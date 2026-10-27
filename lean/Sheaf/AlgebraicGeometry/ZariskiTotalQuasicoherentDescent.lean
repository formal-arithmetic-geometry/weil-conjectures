/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtension
import WeilConjectures.Topology.ModuleObjectOpenDescent
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.CategoryTheory.TotalSitePseudofunctor

/-! # Ordinary unbounded Zariski total descent

Source: Stacks Project, sites-cohomology.tex, Tag 0D7V,
lemma-equivalence-unbounded-one; spaces-simplicial.tex, Tag 0DHF,
lemma-coh-descent-qcoh-unbounded-for-fppf-hypercovering, Zariski specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent).

The Čech levels and maps below are actual coproduct schemes. The presentation
certificate identifies the recorded ringed total construction with precisely
these small Zariski sites and structure maps; its existence is part of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open CategoryTheory.SemisimplicialRingedTotal

namespace AlgebraicGeometry.ZariskiTotal

/-- A tuple intersection, including repeated indices and empty intersections.
Source: Stacks 0DHF, Čech specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
def intersection {T : Scheme.{u}} {I : Type u} (W : I → T.Opens)
    (n : SemiSimplexCategory) (t : Fin (n.len + 1) → I) : T.Opens :=
  ⨅ r, W (t r)

/-- The coproduct of all tuple intersections in degree `n`.
Source: Stacks 0DHF, Čech specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
def level {T : Scheme.{u}} {I : Type u} (W : I → T.Opens)
    (n : SemiSimplexCategory) : Scheme.{u} :=
  ∐ fun t : Fin (n.len + 1) → I ↦ (intersection W n t).toScheme

/-- The augmentation, given on every summand by its open inclusion.
Source: Stacks 0DHF, Čech specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
def augmentation {T : Scheme.{u}} {I : Type u} (W : I → T.Opens)
    (n : SemiSimplexCategory) : level W n ⟶ T :=
  Sigma.desc fun t ↦ (intersection W n t).ι

/-- The face map drops exactly the indices omitted by the injective order map.
Source: Stacks 0DHF, face-only Čech specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
def face {T : Scheme.{u}} {I : Type u} (W : I → T.Opens)
    {m n : SemiSimplexCategory} (a : m ⟶ n) : level W n ⟶ level W m :=
  Sigma.desc fun t ↦
    T.homOfLE (le_iInf fun r ↦ iInf_le (fun s ↦ W (t s))
      (SemiSimplexCategory.homEquiv a r)) ≫
      Sigma.ι (fun s : Fin (m.len + 1) → I ↦ (intersection W m s).toScheme)
        (t ∘ SemiSimplexCategory.homEquiv a)

/-- The small Zariski ringed site of a scheme, with its existing structure sheaf.
Source: Stacks 0DHF, Zariski specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
def site (T : Scheme.{u}) : Site.{u} where
  C := T.Opens
  J := Opens.grothendieckTopology T
  ring := T.sheaf

/-- The concrete Čech specialization of the recorded semisimplicial presentation.
The fibre equalities fix sites, topologies and rings; the base-change and adjoint
ring-map formulas fix the face and augmentation ringed morphisms. No arbitrary
augmentation or arbitrary comparison map is substituted.
Source: Stacks 0DHF and 0D70, small Zariski face-only specialization
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
structure Model {T : Scheme.{u}} {I : Type u} (W : I → T.Opens) where
  F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}
  diagram : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F
  rings : RingDiagram diagram
  sheaf : Presheaf.IsSheaf diagram.totalTopology rings.presheaf
  presentation : Presentation rings sheaf
  fibre : ∀ n : SemiSimplexCategoryᵒᵖ, rings.fibre n = site (level W n.unop)
  baseChange : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n),
    HEq (F.map a.op.toLoc).toFunctor (TopologicalSpace.Opens.map (face W a.unop).base)
  faceDirect : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n),
    HEq (presentation.face a).direct
      (TopCat.Sheaf.pushforward (Type u) (face W a.unop).base)
  faceRing : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n),
    HEq (((presentation.face a).adj.homEquiv _ _ (presentation.face a).ringMap).hom)
      (Functor.whiskerRight (face W a.unop).c (forget CommRingCat))
  augmented : Augmentation rings (site T)
    presentation.face presentation.faceId presentation.faceComp
  augmentationDirect : ∀ n : SemiSimplexCategoryᵒᵖ,
    HEq (augmented.map n).direct
      (TopCat.Sheaf.pushforward (Type u) (augmentation W n.unop).base)
  augmentationRing : ∀ n : SemiSimplexCategoryᵒᵖ,
    HEq (((augmented.map n).adj.homEquiv _ _ (augmented.map n).ringMap).hom)
      (Functor.whiskerRight (augmentation W n.unop).c (forget CommRingCat))
  total : AugmentationPresentation presentation (site T) augmented

/-- Componentwise quasi-coherent cohomology and invertible derived transitions,
inside the actual ordinary total derived category.
Source: Stacks 0DHF and 0D7V
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
def Model.cartesianQCoh {T : Scheme.{u}} {I : Type u} {W : I → T.Opens}
    (M : Model W) : ObjectProperty (M.rings.total M.sheaf).D :=
  fun E ↦ M.presentation.IsCartesian E ∧ ∀ (n : SemiSimplexCategoryᵒᵖ) (q : ℤ),
    SheafOfModules.IsQuasicoherent (R := (site (level W n.unop)).rings)
      (cast (congrArg (fun S : Site.{u} ↦ S.modules) (M.fibre n))
        ((DerivedCategory.homologyFunctor (M.rings.fibre n).modules q).obj
          ((M.presentation.evaluation n).derived.obj E)))

/-- The normalized ambient derived adjunction and its triangulated restriction.
The comparison `beta` is the universal right-derived comparison for the actual
ambient module direct image. The two normalization equations pin the adjunction
to the given ordinary module adjunction, including its unit and counit.
Source: Stacks 0D7V, equivalence-unbounded-one, with its canonical adjunction
(blueprint: lem-sfb-zariski-total-quasicoherent-descent). -/
structure Descent {T : Scheme.{u}} {I : Type u} {W : I → T.Opens}
    (M : Model W) where
  exactFaces : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n),
    PreservesFiniteLimits (M.presentation.pullback a).ordinary ∧
      PreservesFiniteColimits (M.presentation.pullback a).ordinary
  exactAugmentation : PreservesFiniteLimits M.total.pullback.ordinary ∧
    PreservesFiniteColimits M.total.pullback.ordinary
  exactDerived : IsIso M.total.pullback.epsilon
  pushforward : (M.rings.total M.sheaf).D ⥤ (site T).D
  beta : M.total.map.modules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ pushforward
  rightDerived : pushforward.IsRightDerivedFunctor beta
    (HomotopyCategory.quasiIso (M.rings.total M.sheaf).modules (ComplexShape.up ℤ))
  adjunction : M.total.pullback.derived ⊣ pushforward
  unit_model : ∀ K : HomotopyCategory (site T).modules (ComplexShape.up ℤ),
    adjunction.unit.app (DerivedCategory.Qh.obj K) ≫
      pushforward.map (M.total.pullback.epsilon.app K) =
    DerivedCategory.Qh.map
      ((M.total.pullback.adjunction.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K) ≫
        beta.app ((M.total.pullback.ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  counit_model : ∀ K : HomotopyCategory (M.rings.total M.sheaf).modules (ComplexShape.up ℤ),
    M.total.pullback.derived.map (beta.app K) ≫
      adjunction.counit.app (DerivedCategory.Qh.obj K) =
    M.total.pullback.epsilon.app
      ((M.total.map.modules.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((M.total.pullback.adjunction.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K)
  [sourceTriangulated : (@schemeDerivedQCohProperty T (site T).hasDerived).IsTriangulated]
  [targetTriangulated : M.cartesianQCoh.IsTriangulated]
  equivalence : (@schemeDerivedQCohProperty T (site T).hasDerived).FullSubcategory ≌
    M.cartesianQCoh.FullSubcategory
  forward : equivalence.functor ⋙ M.cartesianQCoh.ι ≅
    (@schemeDerivedQCohProperty T (site T).hasDerived).ι ⋙ M.total.pullback.derived
  backward : equivalence.inverse ⋙
    (@schemeDerivedQCohProperty T (site T).hasDerived).ι ≅ M.cartesianQCoh.ι ⋙ pushforward
  [shift : equivalence.functor.CommShift ℤ]
  triangulated : equivalence.functor.IsTriangulated
  unit_iso : ∀ E : (site T).D, (@schemeDerivedQCohProperty T (site T).hasDerived) E →
    IsIso (adjunction.unit.app E)
  counit_iso : ∀ E : (M.rings.total M.sheaf).D, M.cartesianQCoh E →
    IsIso (adjunction.counit.app E)

/-- Unbounded ordinary quasi-coherent descent on the Zariski face total site.
Source: Stacks sites-cohomology.tex, Tag 0D7V, lemma-equivalence-unbounded-one;
spaces-simplicial.tex, Tag 0DHF, verification Ad (1)--(5), specialized to opens
(blueprint: lem-sfb-zariski-total-quasicoherent-descent).

Proof: (1) Construct the Čech diagram of small Zariski sites. Every tuple component
of a face or augmentation is an open inclusion, so module pullback is exact by
lem-weil-pbc-module-open-restriction-injectives. Exact conservative evaluations
from lem-sfb-semisimplicial-ringed-total-category imply exactness upstairs.
(2) Kernels, cokernels and extensions of quasi-coherent modules are quasi-coherent
by lem-weil-pbc-quasi-coherent-module-kernel,
lem-weil-pbc-quasi-coherent-module-cokernel-closure and lem-pc-quasi-coherent-extension.
Exact face pullback preserves cartesianness in these operations; the extension
case follows by the short-exact-sequence chase. Thus the cartesian quasi-coherent
systems and the downstairs quasi-coherent modules are weak Serre subcategories.
(3) For a cartesian system, define the overlap isomorphism as t₁⁻¹ t₀. Triple
compatibility gives the cocycle, and the repeated triple gives the identity on
the diagonal. Apply lem-weil-pbc-module-object-open-descent. Quasi-coherence is
local by pqf-def-coherent, with no finiteness assumption on the cover.
(4) The vertex formula extends the glued isomorphism to every tuple, independently
of the chosen vertex. Compatible degree-zero maps glue uniquely and determine
all higher maps. Compatible sections on every open identify the inverse with the
ambient augmentation direct image, also for arbitrary modules.
(5) lem-sfb-zariski-cech-module-derived-unit supplies the canonical derived unit
isomorphism on every module in degree zero, not merely the heart equivalence.
(6) The total module category is Grothendieck and has enough injectives by
lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives.
The exact free left adjoint from lem-sfb-semisimplicial-evaluation-free-adjoint
makes evaluation preserve injectives. Hence total cohomology at a component open
is component module cohomology, which lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison
identifies with abelian sheaf cohomology, with identity in degree zero.
(7) Affine opens in tuple components form a basis. Componentwise coverings generate
the topology by lem-trf-slice-site-total-pseudofunctor, so affine refinements are
cofinal. pqf-lem-affine-vanishing gives the local bound zero both upstairs and
downstairs; intersections of affine opens are not assumed affine.
(8) Apply lem-sfb-ringed-unbounded-descent-criterion. Exact evaluation identifies
cohomology componentwise, and the exact-face criterion of
lem-sfb-semisimplicial-ringed-total-category identifies derived cartesianness with
cartesian cohomology systems. Thus the two full derived subcategories are precisely
the ones in the statement. The canonical derived adjunction restricts with its
unit and counit invertible. Everything concerns actual total derived objects and
all their morphisms; no strictification of homotopy-category diagrams is asserted. -/
theorem zariski_total_quasicoherent_descent
    (T : Scheme.{u}) (I : Type u) (W : I → T.Opens) (hcover : ⨆ i, W i = ⊤) :
    ∃ M : Model W, Nonempty (Descent M) := by
  sorry

end AlgebraicGeometry.ZariskiTotal
