/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.BaseChange.Square
import Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules

/-! # Coherence of normalized etale sum right adjoints

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1; Stacks Tags 03S6, 0F7J, 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

The comparisons below use the actual proper/open compositor and exchange. The map to sum
extension is the constructed graph comparison, rather than a choice of a bare isomorphism.
Right adjoints and their adjunctions are quantified, so no choice of Brown adjoint is imposed.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange exactEtaleSumExchange

/-- The specified compact-support-to-sum identification for the chosen compactification.
Source: Stacks Tags 0F4L, 0F7J, and the blueprint Step 1
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    canonicalEtaleCompactSupportComparison A e (HasCompactification.compactification e)

/-- The normalization rho is the adjunction conjugate of the inverse specified comparison.
Source: blueprint Step 1; Stacks Tags 0037 and 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (etaleSumSupportIso A e).symm

/-- The canonical pullback identification of the coefficient unit, in the exact derived model.
Source: blueprint Step 1, pullback-unit identification
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumPullbackUnitIso
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (e : U ⟶ X) :
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj (constantComplex A X) ≅
      constantComplex A U :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm.app
      (constantComplex A X) ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

/-- The normalization eta of the dualizing coefficient object.
Source: blueprint Step 1, definition of eta from rho at the coefficient unit
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointUnitIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G) :
    G.obj (constantComplex A X) ≅ constantComplex A U :=
  (etaleSumRightAdjointIso A e G adj).app (constantComplex A X) ≪≫
    etaleSumPullbackUnitIso A e

/-- The right-adjoint compositor is the conjugate of the specified compact-support compositor.
Source: Stacks Tags 0F7J, 0F7K; blueprint Step 1
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointCompIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T)
    [HasCompactification e] [HasCompactification v] [HasCompactification (e ≫ v)]
    [QuasiCompact e] [QuasiCompact (e ≫ v)]
    (G_e : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G_v : DerivedCategoryModule A T ⥤ DerivedCategoryModule A X)
    (G_ve : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U)
    (adj_e : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G_e)
    (adj_v : rightDerivedLowerShriek (ModuleCat.{u + 1} A) v ⊣ G_v)
    (adj_ve : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) ⊣ G_ve) :
    G_ve ≅ G_v ⋙ G_e :=
  conjugateIsoEquiv adj_ve (adj_e.comp adj_v) (unboundedEtaleLowerShriekCompIso A e v)

/-- The exceptional exchange at the coefficient unit is the adjunct of the inverse
specified compact-support exchange followed by the pulled-back counit and unit identification.
Source: blueprint Step 1, definition of b; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [IsSeparated e] [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ G') :
    (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.obj
        (G.obj (constantComplex A X)) ⟶ G'.obj (constantComplex A X') :=
  haveI := (unboundedEtaleCompactSupport_baseChange A sq).1
  (adj'.homEquiv _ _)
    (inv ((unboundedEtaleCompactSupportBaseChange A sq).app
        (G.obj (constantComplex A X))) ≫
      (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map
        (adj.counit.app (constantComplex A X)) ≫ (etaleSumPullbackUnitIso A w).hom)

/-- Composition coherence for the normalized right adjoints, at every unbounded input.
Source: blueprint Step 1; Stacks Tags 0F7J, 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: The sum adjunction counit folds each summand; after two extensions it sends a nested
summand to its original section. Sheafification proves equality of the two sheaf counits.
Apply this degreewise and descend through localization, using
lem-amb-etale-adjoint-locality and lem-weil-pbc-localization-universal-property.
The proper-support/sum comparison of lem-sfb-quasifinite-compact-support-exact intertwines
this sum compositor with the actual compact-support compositor. Conjugate that equality
using def-weil-pbc-adjunction-conjugate and lem-weil-pbc-mate-pasting. The conjugate of the
sum compositor is the pullback compositor by the counit calculation. This gives the equation.
No boundedness or constructibility assumption occurs in the degreewise argument. -/
theorem etaleSumRightAdjoint_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    [HasCompactification e] [HasCompactification v] [HasCompactification (e ≫ v)]
    (G_e : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G_v : DerivedCategoryModule A T ⥤ DerivedCategoryModule A X)
    (G_ve : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U)
    (adj_e : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G_e)
    (adj_v : rightDerivedLowerShriek (ModuleCat.{u + 1} A) v ⊣ G_v)
    (adj_ve : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) ⊣ G_ve)
    (K : DerivedCategoryModule A T) :
    (etaleSumRightAdjointIso A (e ≫ v) G_ve adj_ve).hom.app K ≫
        (unboundedEtaleUpperStarCompIso A e v).hom.app K =
      (etaleSumRightAdjointCompIso A e v G_e G_v G_ve adj_e adj_v adj_ve).hom.app K ≫
        (etaleSumRightAdjointIso A e G_e adj_e).hom.app (G_v.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
          ((etaleSumRightAdjointIso A v G_v adj_v).hom.app K) := by
  sorry

/-- The identity normalization uses the canonical identity comparison.
Source: blueprint Step 1; Stacks Tag 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: The proper-support comparison of the identity compactification is the canonical
identity sum comparison (lem-sfb-quasifinite-compact-support-exact). Its conjugate is the
identity pullback comparison by def-weil-pbc-composite-adjunction and
 def-weil-pbc-adjunction-conjugate. Canonical refinement comparisons give the same equation
for the chosen compactification. -/
theorem etaleSumRightAdjoint_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] [HasCompactification (𝟙 X)]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) ⊣ G) :
    etaleSumRightAdjointIso A (𝟙 X) G adj ≪≫ unboundedEtaleUpperStarIdIso A X =
      conjugateIsoEquiv adj (Adjunction.id (C := DerivedCategoryModule A X))
        (unboundedEtaleLowerShriekId A X).symm := by
  sorry

/-- Base change preserves the normalized dualizing coefficient object.
Source: blueprint Step 1; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: Expand the adjunction conjugate to express the compact-support counit as the sum
counit after d and rho. The specified sheaf sum base-change map is the mate of the pullback
square: expand its definition as the conjugate of underived exchange, paste the inverse-image
and sum adjunctions, and cancel their triangles (lem-weil-pbc-mate-pasting). Its counit square
therefore commutes. Apply this degreewise to unbounded representatives and use localization.
The actual proper/open exchange intertwines d with the inverse sum exchange by
lem-pur-etale-support-map-compatibility (1), for arbitrary w, including non-finite proper
compactification factors. Transpose the defining counit composite of b across the sum
adjunction, substitute these two identities, and cancel the injective hom bijection. At A_X
the pullback-unit identifications give exactly the displayed equality. -/
theorem etaleSumRightAdjoint_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ G') :
    etaleSumRightAdjointBaseChange A sq G G' adj adj' ≫
        (etaleSumRightAdjointUnitIso A e' G' adj').hom =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map
        (etaleSumRightAdjointUnitIso A e G adj).hom ≫
          (etaleSumPullbackUnitIso A w').hom := by
  sorry

/-- The derived evaluation counit is preserved by the inverse specified degreewise sum exchange.
Source: blueprint Step 1; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: Write the sum base-change map beta as the mate of the pullback-composition square,
using its definition as the conjugate of underived exchange and the twofold mate-pasting
identity (lem-weil-pbc-mate-pasting). Naturality of the sum counit and the triangle identity
then give H(ev) beta = ev' S'(chi). Apply this sheaf equation degreewise, and descend along
localization (lem-weil-pbc-localization-universal-property). At the constant complex chi
is precisely the canonical constant-pullback identification. This is the formula below;
its final two S' maps spell out the identifications suppressed in the node. -/
theorem etaleSumRightAdjoint_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian X']
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e] (w : X' ⟶ X) :
    (exactEtaleSumExchange A e w).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj
            (constantComplex A X)) ≫
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app (constantComplex A X)) ≫
        (etaleSumPullbackUnitIso A w).hom =
      (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst w e)
          inferInstance).mapDerivedCategory.map
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory.map
            (etaleSumPullbackUnitIso A e).hom ≫
          (etaleSumPullbackUnitIso A (pullback.snd w e)).hom ≫
          (etaleSumPullbackUnitIso A (pullback.fst w e)).inv) ≫
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst w e) inferInstance).counit.app (constantComplex A X') := by
  sorry

/-- Every proper refinement induces the same counit-normalized right-adjoint identification.
Source: blueprint Step 1; Stacks Tags 0F7J, 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: The proper-support graph comparisons agree under the canonical common-refinement
comparison (lem-sfb-quasifinite-compact-support-exact). Conjugate this equality, using the
contravariant composition law of def-weil-pbc-adjunction-conjugate. This gives the displayed
identity for arbitrary compactifications c and d, in particular every proper refinement.
Since compositor and exchange already commute with these comparisons by
lem-amb-unbounded-compact-support-comparisons, their normalized right-adjoint equations
are unchanged as well. -/
theorem etaleSumRightAdjoint_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e)
    (G H : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    conjugateIsoEquiv adj
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
        (canonicalEtaleCompactSupportComparison A e c).symm =
      conjugateIsoEquiv adj adj'
          (rightDerivedLowerShriekOfCompactificationIso A c d).symm ≪≫
        conjugateIsoEquiv adj'
          (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
          (canonicalEtaleCompactSupportComparison A e d).symm := by
  sorry

/-- Compatibility with a further Cartesian open restriction, using the actual exchanges.
Source: blueprint Step 1, last assertion; Stacks Tags 03S6 and 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: The inverse-image comparison of the pasted square is the composite of the two
inverse-image comparisons, by associativity. The specified compact-support exchanges paste
by lem-amb-unbounded-compact-support-comparisons, and their inverse counit transposes paste
by lem-weil-pbc-mate-pasting. Alternatively apply the base-change normalization just proved
to all three squares. Compose each side with the invertible eta of e'', use naturality of
the exact pullback-composition map, and use transitivity of the constant-pullback unit
identifications; the two resulting arrows are identical. Cancel eta. Thus the same b,
not a newly chosen normalization, commutes with every further Cartesian open restriction.
The preceding composition and counit equations hold for these restricted schemes as well. -/
theorem etaleSumRightAdjoint_openRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' U'' X X' X'' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian U'']
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {w : X' ⟶ X} {k : X'' ⟶ X'} {w' : U' ⟶ U} {k' : U'' ⟶ U'}
    [Etale e] [Etale e'] [Etale e'']
    [IsSeparated e] [IsSeparated e'] [IsSeparated e''] [IsOpenImmersion k]
    [QuasiCompact e] [QuasiCompact e'] [QuasiCompact e'']
    [HasCompactification e] [HasCompactification e'] [HasCompactification e'']
    (sq₁ : IsPullback w' e' e w) (sq₂ : IsPullback k' e'' e' k)
    (sq₃ : IsPullback (k' ≫ w') e'' e (k ≫ w))
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (G'' : DerivedCategoryModule A X'' ⥤ DerivedCategoryModule A U'')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ G')
    (adj'' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e'' ⊣ G'') :
    (upperStar (ModuleCat.{u + 1} A) k').mapDerivedCategory.map
        (etaleSumRightAdjointBaseChange A sq₁ G G' adj adj') ≫
      etaleSumRightAdjointBaseChange A sq₂ G' G'' adj' adj'' =
    (unboundedEtaleUpperStarCompIso A k' w').inv.app (G.obj (constantComplex A X)) ≫
      etaleSumRightAdjointBaseChange A sq₃ G G'' adj adj'' := by
  sorry

end AlgebraicGeometry.Etale
