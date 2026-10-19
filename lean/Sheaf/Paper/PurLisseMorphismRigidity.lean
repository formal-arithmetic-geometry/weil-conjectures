/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Topology.Connected.Basic

import Sheaf.Paper.ProEtaleLisseOrigin
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.SiteConstantModuleHom
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-!
# Rigidity of morphisms between finite lisse sheaves

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-inv/lem-pur-lisse-morphism-rigidity.md,
node `lem-pur-lisse-morphism-rigidity` (blueprint: lem-pur-lisse-morphism-rigidity).

The finite coefficient ring is the canonical constant coefficient ring attached to a
`PurityFiniteSetting`.  Module sheaves are represented in the ringed pro-etale category;
local constancy uses the recorded ringed-site predicate, and geometric stalks use
the recorded colimit construction with its action by the coefficient stalk ring.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The canonical map on ringed module stalks, obtained by restricting the morphism to
pointed neighbourhoods and applying the existing module-colimit functor.
Source: Stacks Project, Tag 0F6B, and `def-weil-proetale-geometric-stalk`
(blueprint: lem-pur-lisse-morphism-rigidity). -/
noncomputable def purityProEtaleStalkMap (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {F G : proEtaleRingModules T (proEtaleConstantRing T P.Ring)}
    (y : Spec (.of Ω) ⟶ T) (f : F ⟶ G) :
    proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) F ⟶
      proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) G :=
  (PresheafOfModules.colimitFunctor
    (colimit.isColimit (proEtaleGeometricStalkRingDiagram y
      (proEtaleConstantRing T P.Ring)))).map
    ((PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      ((proEtaleConstantRing T P.Ring).obj ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f.val)

/-- Finite lisse means local constancy as a module over the constant ring sheaf, together
with finite underlying sets at every geometric stalk. Both notions use their dependency
declarations directly; no condition of freeness is imposed.
Source: Stacks Project, Tag 099Y, and the finite-stalk convention of the blueprint node
(blueprint: lem-pur-lisse-morphism-rigidity). -/
noncomputable def PurityFiniteLisse (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (F : proEtaleRingModules T (proEtaleConstantRing T P.Ring)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf T P.Ring F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T),
      Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) F)

/-- Vanishing of a map at one geometric point in the connected component of `x`.
The explicit field structures package the geometric-point quantifiers without changing their
meaning. Source: blueprint node, clause (2), and Stacks Project, Tag 0F6B
(blueprint: lem-pur-lisse-morphism-rigidity). -/
def PurityVanishingAtComponent (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (f : L ⟶ M) (x : T) : Prop :=
  ∃ (Ω : Type u) (hΩ : Field Ω) (hΩalg : @IsAlgClosed Ω hΩ),
    letI := hΩ
    letI := hΩalg
    ∃ (y : Spec (.of Ω) ⟶ T),
      Set.range (((Scheme.Hom.toLRSHom' y).base : TopCat.Hom _ _).hom) ⊆
          connectedComponent x ∧
        purityProEtaleStalkMap P T y f = 0

/-- The internal Hom of finite lisse sheaves is finite lisse, and its maps are determined by
one geometric stalk on every connected component.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-inv/lem-pur-lisse-morphism-rigidity.md, Tags 093T, 093S, 03PR, 03PT, 03Q1 and 03WT
(blueprint: lem-pur-lisse-morphism-rigidity).

Proof plan, following the seven steps of the DAG node:
1. By `lem-sf-proetale-locally-constant-origin`, descend both finite lisse sheaves to the
etale site. The coefficient ring is finite by `def-weil-l-adic-coefficient-extension`.
Use `lem-weil-pbc-finite-locally-constant-module-values` and a fibre-product refinement
of the two trivializing covers to obtain common finite constant module values P_i, Q_i.
2. The comparison inclusion preserves covers. Its pullback commutes with restriction
(`lem-weil-pbc-comparison-pullback`) and preserves constant module sheaves: the comparison
adjunction and constant-sheaf universal property identify maps out of both constructions
with linear maps into global sections. Hence the same cover trivializes L and M on the
pro-etale site. Use `lem-weil-proetale-weakly-etale-localization` to identify slice sites.
3. Internal Hom commutes with localization (`def-pur-sheaf-hom`). A finite module over a
finite ring is finitely presented: take the free module on its finite underlying set;
its kernel is finite and generated by all its elements. Thus `lem-pur-site-constant-module-hom`
identifies the localized Hom with the constant module Hom(P_i,Q_i), a finite set. Lift each
geometric point to the etale cover, restrict the pointed-neighbourhood colimit cofinally,
and apply `lem-weil-proetale-constant-sheaf-stalk` to obtain finite stalks. This proves (1).
4. For (2), descend the morphism by the fully faithful comparison, using the unit
isomorphisms of `prop-weil-pbc-site-comparison-finite-level`. Naturality of the counit and
the triangle identities show that its inverse image is the original morphism.
`lem-cbc-proetale-comparison-stalk` carries the prescribed stalk vanishing to this map.
5. By `lemma-constructible-hom-constant-locally`, refine the common etale cover further
so that this descended map is induced by an actual linear map f_j of constant values.
6. Lift any fixed geometric point through each chart containing its image. The natural
pullback-stalk isomorphism (`lemma-openclosed-stalk-upperstar`) and constant-stalk
comparison identify the stalk map with f_j. Thus the zero locus is the union of chart
images with f_j = 0; its complement is the union with f_j nonzero. They are disjoint
open sets since etale morphisms are open (`lem-weil-pbc-etale-morphism-open-map`).
7. The zero locus meets each connected component, so connectedness makes it all of T.
Every nonempty chart then has f_j = 0; the empty-cover sheaf axiom handles empty charts.
For any etale object and section, the pulled-back covering and sheaf separatedness give
global vanishing of the descended map, hence of the original map. The same empty-cover
argument handles empty T. Apply this to the difference of two maps for the last assertion.
-/
theorem purLisseMorphismRigidity (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (CommRingCat.of P.field.k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (hL : PurityFiniteLisse P T L) (hM : PurityFiniteLisse P T M) :
    PurityFiniteLisse P T (SheafOfModules.homObj (R := proEtaleConstantRing T P.Ring) L M) ∧
      ((∀ (f : L ⟶ M),
          (∀ (x : T), PurityVanishingAtComponent P T L M f x) → f = 0) ∧
        (ConnectedSpace T →
          ∀ (f g : L ⟶ M) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (y : Spec (.of Ω) ⟶ T),
            purityProEtaleStalkMap P T y f = purityProEtaleStalkMap P T y g →
              f = g)) := by
  sorry

end WeilConjectures
