/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtension
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint

/-! # Ordinary Brown representability for levelwise quasi-coherent systems

Source: Stacks Project, properties.tex, Tag 077P (1), spaces-simplicial.tex,
Tag 0D72; Hall--Neeman--Rydh, Appendix A, Theorem A.3; Hall--Rydh,
Theorem 4.14 (1) (blueprint: lem-sfb-levelwise-quasicoherent-brown).

All systems below are the dependency's ordinary semilinear systems. Their
transitions need not be invertible. The structures merely collect the input
identifications with the small Zariski sites and the several output clauses.
-/

@[expose] public section
set_option autoImplicit false

universe u w a d v

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open AlgebraicGeometry

namespace CategoryTheory

/-- The small Zariski ringed site of the specified scheme. Source: Stacks 077P,
0D72 (blueprint: lem-sfb-levelwise-quasicoherent-brown). -/
def schemeZariskiRingedSite (X : Scheme.{u}) : SemisimplicialRingedTotal.Site.{u} where
  C := X.Opens
  J := Opens.grothendieckTopology X
  ring := X.sheaf

/-- The output clauses for the ordinary full derived subcategory `Q`. Its shift
and triangles are inherited from the ambient derived category, and the inclusion
preserves coproducts. The explicit degreewise coproduct cocone of complexes
with cohomology in `Q` remains in `Q` and is a derived coproduct.
Source: Hall--Neeman--Rydh, Appendix A, Theorem A.3, and Hall--Rydh, Theorem 4.14 (1)
(blueprint: lem-sfb-levelwise-quasicoherent-brown). -/
structure OrdinaryQuasiCoherentBrown
    (A : Type a) [Category.{u} A] [Abelian A] [HasCoproducts.{u} A]
    [HasDerivedCategory.{w} A]
    (Q : ObjectProperty (DerivedCategory A))
    (D : Type d) [Category.{v} D] [LocallySmall.{u} D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{u} D] : Prop where
  [triangulated : Q.IsTriangulated]
  [coproducts : HasCoproducts.{u} Q.FullSubcategory]
  inclusion_coproducts : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) Q.ι
  termwise_coproducts : ∀ (I : Type u) (K : I → CochainComplex A ℤ),
    (∀ i : I, Q (DerivedCategory.Q.obj (K i))) →
    Q (DerivedCategory.Q.obj
      (HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)).pt) ∧
    Nonempty (IsColimit ((DerivedCategory.Q (C := A)).mapCocone
      (HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K))))
  right_adjoint : ∀ (G : Q.FullSubcategory ⥤ D) [G.CommShift ℤ] [G.IsTriangulated],
    (∀ I : Type u, PreservesColimitsOfShape (Discrete I) G) → G.IsLeftAdjoint

namespace SemisimplicialRingedTotal

variable {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
  {S : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F} {R : RingDiagram S}
  {h : Presheaf.IsSheaf S.totalTopology R.presheaf}

/-- Identifications of the given total diagram with the small Zariski ringed
sites of a semisimplicial scheme. The component functors identify each module
and map with itself after site transport, and the face pullbacks are the actual
scheme module pullbacks up to natural isomorphism. This is presentation data,
not an extra geometric or quasi-coherence assumption.
Source: Stacks 0D72 and 077P
(blueprint: lem-sfb-levelwise-quasicoherent-brown). -/
structure SchemePresentation (P : Presentation R h)
    (T : SemiSimplexCategoryᵒᵖ ⥤ Scheme.{u}) where
  site_eq : ∀ i : SemiSimplexCategoryᵒᵖ, R.fibre i = schemeZariskiRingedSite (T.obj i)
  modules : ∀ i : SemiSimplexCategoryᵒᵖ, (R.fibre i).modules ≌ (T.obj i).Modules
  obj_eq : ∀ (i : SemiSimplexCategoryᵒᵖ) (M : (R.fibre i).modules),
    HEq ((modules i).functor.obj M) M
  map_eq : ∀ (i : SemiSimplexCategoryᵒᵖ) {M N : (R.fibre i).modules} (f : M ⟶ N),
    HEq ((modules i).functor.map f) f
  pullback : ∀ {i j : SemiSimplexCategoryᵒᵖ} (f : i ⟶ j),
    (P.pullback f).ordinary ⋙ (modules i).functor ≅
      (modules j).functor ⋙ Scheme.Modules.pullback (T.map f)

/-- The specified small Zariski realization exists for every semisimplicial
scheme; consumers need no additional existence assumption on its total site.
Source: Stacks 09WC, 09WF and 0D72
(blueprint: lem-sfb-levelwise-quasicoherent-brown).

Proof: Assign the small category of opens to each component of T and inverse image
of opens to each face. The scheme functor laws give the coherent pseudofunctor
laws, and inverse image of opens carries covering families to covering families.
Use the structure sheaf on each component; the maps on sections of T give the
semilinear total ring presheaf with its identity and composition laws. Apply
lem-sfb-semisimplicial-ringed-total-category. Its fibre sites are these Zariski
sites, so equality transport gives the module equivalences acting as the identity
on objects and maps. The face module pullback has the same tensor-extension
formula and right-adjoint pushforward as the ordinary scheme module pullback;
the normalized adjunction comparison gives the required natural isomorphism. -/
theorem exists_schemePresentation (T : SemiSimplexCategoryᵒᵖ ⥤ Scheme.{u}) :
    ∃ (F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u})
      (S : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F) (R : RingDiagram S)
      (h : Presheaf.IsSheaf S.totalTopology R.presheaf) (P : Presentation R h),
      Nonempty (SchemePresentation P T) := by
  sorry

/-- The actual full underived quasi-coherent category: all components are
quasi-coherent, with arbitrary semilinear transitions from the total module.
Source: Stacks 077P and 0D72
(blueprint: lem-sfb-levelwise-quasicoherent-brown). -/
def levelwiseQuasiCoherentProperty (P : Presentation R h)
    {T : SemiSimplexCategoryᵒᵖ ⥤ Scheme.{u}} (Z : SchemePresentation P T) :
    ObjectProperty (R.total h).modules :=
  fun M ↦ ∀ i : SemiSimplexCategoryᵒᵖ,
    SheafOfModules.IsQuasicoherent (R := (T.obj i).ringCatSheaf)
      ((Z.modules i).functor.obj ((P.evaluation i).ordinary.obj M))

/-- The full derived subcategory specified by quasi-coherence of every
cohomology of every exact derived evaluation. No cartesian condition is imposed.
Source: Hall--Neeman--Rydh, Appendix A, Theorem A.3, and Stacks 0D72
(blueprint: lem-sfb-levelwise-quasicoherent-brown). -/
def levelwiseDerivedQuasiCoherentProperty (P : Presentation R h)
    {T : SemiSimplexCategoryᵒᵖ ⥤ Scheme.{u}} (Z : SchemePresentation P T) :
    ObjectProperty (R.total h).D :=
  fun E ↦ ∀ (i : SemiSimplexCategoryᵒᵖ) (q : ℤ),
    SheafOfModules.IsQuasicoherent (R := (T.obj i).ringCatSheaf) ((Z.modules i).functor.obj
      ((DerivedCategory.homologyFunctor (R.fibre i).modules q).obj
        ((P.evaluation i).derived.obj E)))

end SemisimplicialRingedTotal

/-- Ordinary Brown representability on an arbitrary scheme. Source: Stacks 077P (1),
Hall--Neeman--Rydh, Appendix A, Theorem A.3, and Hall--Rydh, Theorem 4.14 (1)
(blueprint: lem-sfb-levelwise-quasicoherent-brown).

Proof: Modules on X and quasi-coherent modules are Grothendieck by
lem-pc-scheme-modules-grothendieck-abelian and lem-sfb-qcoh-grothendieck-generators.
The kernel, cokernel, extension and coproduct closure lemmas make quasi-coherent
modules a coproduct-closed weak Serre class. Apply
lem-sfb-grothendieck-weak-serre-derived-representability to get the full ordinary
triangulated subcategory and ambient termwise coproducts. For each target object d,
Hom(G(-),d) is cohomological and sends coproducts to products. Its representing
object is the right adjoint at d; Yoneda transports postcomposition to its maps.
The representing bijections are natural in both variables and give the adjunction. -/
theorem scheme_quasicoherent_brown
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (D : Type d) [Category.{v} D] [LocallySmall.{u} D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{u} D] :
    OrdinaryQuasiCoherentBrown
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (schemeDerivedQCohProperty X) D := by
  sorry

/-- Ordinary Brown for noncartesian levelwise quasi-coherent semisimplicial
module systems with exact face pullbacks.

Source: Stacks 077P (1) and 0D72; Hall--Neeman--Rydh, Appendix A, Theorem A.3,
and Hall--Rydh, Theorem 4.14 (1)
(blueprint: lem-sfb-levelwise-quasicoherent-brown).

Proof plan:
1. Modules and quasi-coherent modules on each scheme are Grothendieck, by
lem-pc-scheme-modules-grothendieck-abelian and lem-sfb-qcoh-grothendieck-generators.
The kernel, cokernel, extension and coproduct closure results in
lem-weil-pbc-quasi-coherent-module-kernel,
lem-weil-pbc-quasi-coherent-module-cokernel-image, lem-pc-quasi-coherent-extension
and lem-weil-pbc-quasi-coherent-module-coproduct-closure give the weak-Serre class.
2. Pullback preserves quasi-coherence by lem-weil-pbc-module-pullback-quasi-coherent
and preserves colimits by def-pc-module-pullback. Use the exact free evaluations
of lem-sfb-semisimplicial-evaluation-free-adjoint, whose components are sums of
face pullbacks. They restrict to levelwise quasi-coherent systems.
3. Compute kernels, cokernels and colimits componentwise. Exact pullbacks induce
kernel transitions; preservation of colimits induces cokernel and colimit
transitions. The universal properties hold componentwise. Exact filtered colimits
are detected by evaluation. The coproduct of the free extensions of component
generators is a generator: a nonzero component map is detected by a component
generator, and the free-evaluation adjunction extends its detecting morphism.
Thus both total modules and levelwise quasi-coherent modules are Grothendieck.
4. Exact evaluations give all four stated closure properties and identify
cohomology of evaluation with evaluation of cohomology. Apply
lem-sfb-grothendieck-weak-serre-derived-representability to the single-scheme pair
and to the total-module pair. It supplies the full triangulated subcategory,
termwise coproducts and cohomological representability, without identifying this
full subcategory with the derived category of the quasi-coherent category.
5. For d in the target, Hom(G(-),d) is cohomological and takes coproducts to
products. Represent it. Postcomposition by a target morphism determines a unique
map between representing objects by Yoneda. Uniqueness gives identities and
composition, and the natural Hom bijections assemble the ordinary right adjoint.
-/
theorem levelwise_quasicoherent_brown
    {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
    {S : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F}
    {R : SemisimplicialRingedTotal.RingDiagram S}
    {h : Presheaf.IsSheaf S.totalTopology R.presheaf}
    (P : SemisimplicialRingedTotal.Presentation R h)
    (T : SemiSimplexCategoryᵒᵖ ⥤ Scheme.{u})
    (Z : SemisimplicialRingedTotal.SchemePresentation P T)
    (exact : ∀ {i j : SemiSimplexCategoryᵒᵖ} (f : i ⟶ j),
      PreservesFiniteLimits (P.pullback f).ordinary ∧
        PreservesFiniteColimits (P.pullback f).ordinary)
    (D : Type d) [Category.{v} D] [LocallySmall.{u} D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{u} D] :
    IsGrothendieckAbelian.{u} (R.total h).modules ∧
    (∃ hAb : Abelian (SemisimplicialRingedTotal.levelwiseQuasiCoherentProperty P Z).FullSubcategory,
      @IsGrothendieckAbelian.{u} _ _ hAb) ∧
    (SemisimplicialRingedTotal.levelwiseQuasiCoherentProperty P Z).IsClosedUnderKernels ∧
    (SemisimplicialRingedTotal.levelwiseQuasiCoherentProperty P Z).IsClosedUnderCokernels ∧
    (SemisimplicialRingedTotal.levelwiseQuasiCoherentProperty P Z).IsClosedUnderExtensions ∧
    (∀ I : Type u, ObjectProperty.IsClosedUnderColimitsOfShape
      (SemisimplicialRingedTotal.levelwiseQuasiCoherentProperty P Z) (Discrete I)) ∧
    OrdinaryQuasiCoherentBrown (R.total h).modules
      (SemisimplicialRingedTotal.levelwiseDerivedQuasiCoherentProperty P Z) D := by
  sorry

end CategoryTheory
