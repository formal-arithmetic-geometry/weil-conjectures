/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ContinuousModuleEncodingUniverses
public import Sheaf.Paper.BoundedConstructibleTower
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Exact scalar extension under the universe-polymorphic section encodings

Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks Project, Tags 03EK and 03DA.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual integral inclusion, transported through the canonical continuous charts.
Source: Bhatt--Scholze, Lemma 6.8.2(2).
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes). -/
def continuousInternalScalarMapUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) T ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj E) T := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (ContinuousRingUniverse.comparison T E) :=
    ContinuousRingUniverse.comparison_isIso T E
  exact ContinuousRingUniverse.comparison T (Padic.coefficientExtensionIntegers l E) ≫
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((Scheme.adicLisseForget T).map
          (latticeCoefficientSheafMap T
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) ≫
    inv (ContinuousRingUniverse.comparison T E)

/-- The chart-transported integral inclusion is a ring-object homomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks 00YV.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes).
Proof: the two chart maps and the underlying map of the continuous ring-sheaf inclusion
preserve multiplication and the unit; their composite does as well. -/
instance continuousInternalScalarMapUniverses_isMonHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    IsMonHom (continuousInternalScalarMapUniverses l E T) := by
  unfold continuousInternalScalarMapUniverses
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (ContinuousRingUniverse.comparison T E) :=
    ContinuousRingUniverse.comparison_isIso T E
  let : IsMonHom ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((Scheme.adicLisseForget T).map
          (latticeCoefficientSheafMap T
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))) :=
    Sheaf.isMonHom_sheafCompose_map (Scheme.ProEt.topology T)
      ((Scheme.adicLisseForget T).map
        (latticeCoefficientSheafMap T
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))
  infer_instance

/-- Exact continuous localization commutes with the specified ordinary encodings.
There is no completeness, boundedness, or constructibility hypothesis on the module.
Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks 03EK, 03DA.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes).

Proof: the continuous field sheaf is the sheaf localization of the continuous integral
ring at the constant uniformizer. Every continuous field-valued function has locally
bounded denominator, so its numerator is integral on a covering by open subobjects.
The sheaf localization is therefore the field sheaf, and localization is flat. Extension
along c is an equivalence, so completed-to-field extension is exact as well. For the
comparison, scalar restriction under the section-action equivalences is the identity
on the underlying abelian sheaf: the scalar acts by its image under the actual inclusion.
The definition of continuousInternalScalarMapUniverses is precisely the conjugation
of this inclusion by the two continuous charts. Thus the ordinary restrictions commute.
Their left adjoints are scalar extensions; uniqueness of left adjoints gives the natural
isomorphism stated below. It applies to arbitrary module sheaves and all universes.
Zero modules and the empty base are included by the same localization and adjunctions. -/
theorem continuousScalarEncodingUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (c : Scheme.pbcAdicCompletion T (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E)) :
    let a := c.hom ≫ latticeCoefficientSheafMap T
      (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val
    PreservesFiniteLimits
        (Mod.extendScalars (continuousInternalScalarMapUniverses l E T)) ∧
      Nonempty (Scheme.pbcExtend a ⋙
          (continuousFieldModuleEquivalenceUniverse l E T).inverse ≅
        (completedContinuousModuleEquivalence l E T c).inverse ⋙
          Mod.extendScalars (continuousInternalScalarMapUniverses l E T)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
