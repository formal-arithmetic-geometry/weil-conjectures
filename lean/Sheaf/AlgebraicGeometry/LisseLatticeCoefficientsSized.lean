/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.LisseLatticeCoefficients

/-!
# Continuous coefficients in the universe of module values

Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3
(blueprint: def-weil-pbc-lisse-lattice-coefficients).
The coefficient universe is allowed to be the larger site universe. The old
small-coefficient constructions and slice-site inclusion remain available.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- Continuous functions with pointwise ring operations, allowing larger coefficients.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseContinuousCommRingPresheafSized (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom.comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous-function presheaf is a sheaf, with no small-coefficient restriction.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 4.2.12
(blueprint: def-weil-pbc-lisse-lattice-coefficients).
Proof: the underlying set presheaf is the restriction of `continuousMapPresheaf T`,
followed by `ULift`. The fpqc sheaf theorem for that presheaf applies in arbitrary
coefficient universes. Restriction to the pro-etale site and lifting preserve the
sheaf condition. The forgetful functor from commutative rings reflects it. -/
theorem isSheaf_lisseContinuousCommRingPresheafSized (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (lisseContinuousCommRingPresheafSized X T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (lisseContinuousCommRingPresheafSized X T) (forget CommRingCat.{u + 1})]
  let e : lisseContinuousCommRingPresheafSized X T ⋙ forget CommRingCat.{u + 1} ≅
      (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙
        continuousMapPresheaf T ⋙ uliftFunctor.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  rw [Presheaf.isSheaf_of_iso_iff e]
  refine Functor.op_comp_isSheaf_of_isSheaf
    (F := Scheme.ProEt.forget X ⋙ Over.forget X)
    (J := Scheme.ProEt.topology X) (K := Scheme.proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le
    Scheme.proetaleTopology_le_fpqcTopology

/-- The continuous coefficient sheaf in the module-value universe.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseContinuousCommRingSheafSized (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨lisseContinuousCommRingPresheafSized X T,
    isSheaf_lisseContinuousCommRingPresheafSized X T⟩

/-- The rational coefficients with the spectral norm topology.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseFieldSheafSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheafSized X E

/-- The integral coefficients with the subspace topology.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseIntegerSheafSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheafSized X (Padic.coefficientExtensionIntegers l E)

/-- Postcomposition with the valuation-ring inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseIntegerToFieldSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    lisseIntegerSheafSized l E X ⟶ lisseFieldSheafSized l E X :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((Padic.coefficientExtensionIntegers l E).subtype.compLeftContinuous _
           continuous_subtype_val).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The constant integral section, in the same topology as the coefficient sheaf.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseIntegerConstantSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (lisseIntegerSheafSized l E X).obj.obj U :=
  letI := spectralNorm.normedField ℚ_[l] E
  ULift.up (ContinuousMap.const U.unop.left a)

/-- The constant rational section.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseFieldConstantSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (a : E) : (lisseFieldSheafSized l E X).obj.obj U :=
  letI := spectralNorm.normedField ℚ_[l] E
  ULift.up (ContinuousMap.const U.unop.left a)

/-- The coefficient comparison for restriction along an etale arrow.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: def-weil-pbc-lisse-lattice-coefficients). -/
def lisseEtaleCoefficientIdentificationSized (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E Y)).obj ⟶
    (lisseEtaleSiteInclusion f).op ⋙
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X)).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }

/-- The existing pointwise continuous-function presheaf, retaining commutativity.
Source: Bhatt--Scholze, Definition 6.8.1.
(blueprint: def-weil-pbc-lisse-lattice-coefficients) -/
def lisseContinuousCommRingPresheafUniverses (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max (u + 1) v} where
  obj U := CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := CommRingCat.ofHom ((continuousMapRingPresheaf X T).map f).hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Continuous coefficients are a sheaf with independent site and coefficient universes.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 4.2.12.
(blueprint: def-weil-pbc-lisse-lattice-coefficients)
Proof: forgetting commutativity gives exactly continuousMapRingPresheaf X T.
Its existing sheaf theorem follows from continuous-function fpqc descent and restriction
to the small pro-etale site, with the specified ULift. The forgetful functor from
commutative rings to rings reflects the sheaf condition. -/
theorem isSheaf_lisseContinuousCommRingPresheafUniverses (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (lisseContinuousCommRingPresheafUniverses X T) := by
  sorry

/-- The continuous commutative-ring sheaf in the maximum of the required universes.
Source: Bhatt--Scholze, Definition 6.8.1.
(blueprint: def-weil-pbc-lisse-lattice-coefficients) -/
def lisseContinuousCommRingSheafUniverses (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{max (u + 1) v} :=
  ⟨lisseContinuousCommRingPresheafUniverses X T,
    isSheaf_lisseContinuousCommRingPresheafUniverses X T⟩

end AlgebraicGeometry.ProEtale
