/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
import Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion

/-!
# Finite duality: comparison for a closed immersion

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph;
Stacks Project, Tags 04CA, 04JC and 014A.
(blueprint: lem-weil-finite-duality-closed-comparison)

The comparison below is formulated with the actual derived direct-image adjunctions.
The isomorphism `δ` is the canonical direct-image comparison of
`lem-weil-pbc-comparison-direct-image-canonical-mate`, transported from its bounded-below
mate along an explicit bounded-below lift by the named Plus/full compatibility isomorphisms.
The transpose formula is the definition of the comparison map `α`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The transpose `α` used in the closed comparison: the `Rₚ ⊣ Iₚ` transpose of
`δ⁻¹` followed by the etale counit.  This is a genuine construction from the two
adjunctions and the named direct-image comparison; no choice or postponed theorem is
used in the definition.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph
(blueprint: lem-weil-finite-duality-closed-comparison). -/
noncomputable def finiteDualityClosedComparisonAlpha
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T U : Scheme.{u}}
    (_i : Z ⟶ T) (_j : U ⟶ T)
    (Rₑ : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Iₑ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Rₚ : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A)))
    (Iₚ : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)))
    (F_T : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A)))
    (F_Z : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)))
    (adjₑ : Rₑ ⊣ Iₑ) (adjₚ : Rₚ ⊣ Iₚ)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (δ : F_T.obj (Rₑ.obj (Iₑ.obj M)) ≅ Rₚ.obj (F_Z.obj (Iₑ.obj M))) :
    F_Z.obj (Iₑ.obj M) ⟶ Iₚ.obj (F_T.obj M) :=
  (adjₚ.homEquiv (F_Z.obj (Iₑ.obj M)) (F_T.obj M))
    (δ.inv ≫ F_T.map (adjₑ.counit.app M))

/-- The canonical component `δ` of the direct-image comparison, transported from the
bounded-below mate `fixedComparisonDirectImageMatePlus`.  The input `e` is the chosen
bounded-below lift of the etale object.  All comparison isomorphisms are the named Plus/full
compatibility isomorphisms, so this is independent of an arbitrary choice of a natural
isomorphism.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph
(blueprint: lem-weil-finite-duality-closed-comparison). -/
noncomputable def finiteDualityClosedComparisonDelta
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory).obj
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj X) ⟶
    ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj X) :=
  let rE := (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility
  let rP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility
  let fT :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusCompatibility
  let fZ :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlusCompatibility
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map e.hom ≫ rE.inv.app L) ≫
    fT.inv.app ((Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus.obj L) ≫
    DerivedCategory.Plus.ι.map
      ((ProEtale.fixedComparisonDirectImageMatePlus A i).app L) ≫
    rP.hom.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
      (fZ.hom.app L ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map e.inv)

/-- The transported canonical closed-comparison component is invertible.

Source: the canonical direct-image mate argument in
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first
paragraph (blueprint: lem-weil-finite-duality-closed-comparison).

Proof plan: unfold the transported component and use the qcqs invertibility
of `ProEtale.fixedComparisonDirectImageMatePlus`; the named Plus/full
compatibility isomorphisms and the isomorphism `e` preserve `IsIso` under
composition and functorial mapping.
-/
theorem isIso_finiteDualityClosedComparisonDelta_proof
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L) :
    IsIso (finiteDualityClosedComparisonDelta i X L e) := by
  sorry

/- The postponed theorem is registered as an instance directly, so that `asIso` applies
to the canonical component; no further declaration or proof is added. -/
attribute [instance] isIso_finiteDualityClosedComparisonDelta_proof

/-!
The closed finite-duality comparison.  The hypotheses on the structure morphisms record
the finite-type, separated finite-field setting of the source; the bounded-below lift is
the first clause of the conclusion, and `δ` is the named canonical direct-image comparison.
-/
/-- For a separated finite-type scheme over an algebraically closed finite-field fibre,
the ambient etale and pro-etale closed right adjoints agree on bounded constructible
complexes through the canonical comparison mate.  The mate is invertible, satisfies the
exceptional-counit normalization, and is natural in the complex.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph;
Stacks Project, Tags 04CA, 04JC and 014A.
(blueprint: lem-weil-finite-duality-closed-comparison)

Proof plan recorded for the postponed theorem: (1) finiteness of `A` and Noetherian finite-type
hypotheses give the required qcqs maps; (2) the etale support triangle and exact inverse image
show `Iₑ.obj M` is bounded below; (3) the closed pro-etale direct image is exact and fully
faithful after passage to derived categories; (4) the canonical Plus mate is transported to the
full derived category by the named Plus/full compatibility isomorphisms; (5) the etale and
pro-etale support triangles and the open comparison give the counit normalization and
invertibility; (6) naturality follows from naturality of the mate and adjunction transpose
injectivity. These are exactly the six steps of the source proof.
-/
theorem finiteDualityClosedComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hne : l ≠ D.p) [Fact l.Prime]
    (T Z U : Scheme.{u})
    (aT : T ⟶ Spec (.of D.k))
    (aZ : Z ⟶ Spec (.of D.k))
    (aU : U ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (i : Z ⟶ T) [IsClosedImmersion i] [QuasiCompact i] [QuasiSeparated i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (_hi : i ≫ aT = aZ) (_hj : j ≫ aT = aU)
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (n : ℕ) (hn : 1 ≤ n)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    :
    let A := Padic.coefficientExtensionRing l E n
    letI : Finite A := Padic.finite_coefficientExtensionRing l E n hn
    let Rₑ := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
    letI : Rₑ.IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
    let Iₑ := Rₑ.rightAdjoint
    let Rₚ := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
    let Iₚ := (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
    let F_T := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
    let F_Z := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
    let adjₑ : Rₑ ⊣ Iₑ := Adjunction.ofIsLeftAdjoint Rₑ
    let adjₚ : Rₚ ⊣ Iₚ :=
      ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij
    ∀ (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_hM : Etale.DerivedCategory.isBoundedConstructible A T M),
      (∃ L : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Nonempty (Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L)) ∧
      (∀ (L : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (e : Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L),
        let δ := finiteDualityClosedComparisonDelta i (Iₑ.obj M) L e
        let δIso : F_T.obj (Rₑ.obj (Iₑ.obj M)) ≅
            Rₚ.obj (F_Z.obj (Iₑ.obj M)) := asIso δ
        let α := finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
          adjₑ adjₚ M δIso
        IsIso α ∧
        (δ ≫ Rₚ.map α ≫ adjₚ.counit.app (F_T.obj M) =
          F_T.map (adjₑ.counit.app M)) ∧
        (∀ (N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (h : M ⟶ N) (_hN : Etale.DerivedCategory.isBoundedConstructible A T N)
          (L' : DerivedCategory.Plus
            (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (e' : Iₑ.obj N ≅ DerivedCategory.Plus.ι.obj L'),
          let δ' := finiteDualityClosedComparisonDelta i (Iₑ.obj N) L' e'
          let δIso' : F_T.obj (Rₑ.obj (Iₑ.obj N)) ≅
              Rₚ.obj (F_Z.obj (Iₑ.obj N)) := asIso δ'
          F_Z.map (Iₑ.map h) ≫
              finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
                adjₑ adjₚ N δIso' =
            finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
              adjₑ adjₚ M δIso ≫ Iₚ.map (F_T.map h))) := by
  sorry

end AlgebraicGeometry
