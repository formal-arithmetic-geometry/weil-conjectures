/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Yoneda

/-!
# Comparison of pulled-back condensed coefficients with completed coefficients

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-sfb-qlbar-colimit-x/_section.md and its two proof files
(blueprint: sk-prop-sfb-qlbar-colimit-x).

The integral comparison is stated as a limit universal property, with its reductions
normalized on constant sections. Rationalization is stated as the sequential module
colimit together with the ring-localization universal property. These formulations
specify the canonical comparisons without choosing new models for the coefficients.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Constant rings, as ring objects in abelian sheaves, with the standard integer tensor.
Source: the constant finite quotients in the first display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbConstantRing (X : Scheme.{u}) :
    RingCat.{u + 1} ⥤ Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  RingCat.toMonAb ⋙ (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMon

/-- The same constant-ring construction on the pro-étale point.
Source: the finite quotients in the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbPointConstantRing :
    RingCat.{u + 1} ⥤ Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  RingCat.toMonAb ⋙ (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon

/-- The quotient tower, including the harmless terminal zero quotient at exponent zero.
Its maps are the quotient reductions, not arbitrary ring homomorphisms.
Source: first display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbCoefficientQuotientTower (R : Type) [CommRing R] (I : Ideal R) :
    ℕᵒᵖ ⥤ RingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ RingCat.of (ULift.{u + 1} (R ⧸ I ^ n)))
    (fun n : ℕ ↦ RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
        ULift.ringEquiv.toRingHom)))

/-- Constant sections of a topological ring, mapped into its condensed abelian sheaf.
This is the adjoint of the map sending a scalar to its constant continuous function.
Source: normalization of the reduction maps in the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbConstantToContinuous (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} R)) ⟶ Profinite.continuousMapRingObj R :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    { app S := AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (ContinuousMap.const S.unop x.down)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

/-- The pulled-back inclusion of integers into their coefficient field. The underlying
map is precisely `p_X^*` applied to postcomposition with the given continuous inclusion.
Source: second display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbCoefficientInclusion (R K : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (φ : R →+* K) (hφ : Continuous φ) (X : Scheme.{u}) :
    coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) :=
  (upperStarFromPoint X).mapMon.map (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ)))

/-- The coefficient field as a module over the pulled-back integers, using their actual
inclusion. Source: the sequential module colimit in the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbRationalCoefficientModule (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K]
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X) :=
  (Mod.comap (i X).hom).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj K) X))

/-- The sequential diagram of integer modules with transition multiplication by `ℓ`.
Multiplication by `ℓ` is used only as a module map.
Source: second display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbRationalizationSequence (ℓ : ℕ) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (X : Scheme.{u}) :
    ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X) :=
  Functor.ofSequence (fun _ : ℕ ↦ ℓ •
    𝟙 (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj R) X)))

/-- Expanded first and second comparisons, including their canonical maps and pullback
compatibility. The reductions are normalized by the actual quotient maps on constants.
`IsLimit` and `IsColimit` give the displayed comparison isomorphisms by uniqueness of
limits and colimits. The last clause is the universal property of localization as rings;
thus the ring structure on the sequential module colimit is the localization structure.

Source: first two displays and inverse-image paragraph of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
def SfbCompletedCoefficientComparison (ℓ : ℕ) (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (I : Ideal R)
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) : Prop :=
  ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
      sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
    (∀ n : ℕ, sfbConstantToContinuous R ≫ (ρ.app (op n)).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)) ∧
    (∀ X : Scheme.{u},
      Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
        (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))) ∧
      Nonempty ((sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ⋙
        (upperStarFromPoint X).mapMon) ≅
          (sfbCoefficientQuotientTower R I ⋙ sfbConstantRing X))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      Nonempty (IsLimit ((upperStar Ab.{u + 1} f).mapMon.mapCone
        ((upperStarFromPoint Y).mapMon.mapCone
          (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))))) ∧
    ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
        (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X),
      (∀ X : Scheme.{u},
        ((ι X).app 0).hom = (i X).hom ∧
        Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X))) ∧
        IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
        (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
            condensedPullbackHom (Profinite.continuousMapRingObj K) f =
          condensedPullbackHom (Profinite.continuousMapRingObj R) f ≫
            ((ι X).app m).hom) ∧
      (∀ (X : Scheme.{u}) (B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})),
        IsIso (ℓ • 𝟙 B.X) →
        ∀ a : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶ B,
          ∃! b : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) ⟶ B,
            i X ≫ b = a)

/-- The finite-subextension diagram, in ring objects rather than only abelian sheaves.
Source: third display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbFiniteSubfieldRingDiagram (ℓ : ℕ) [Fact ℓ.Prime] :
    PadicAlgCl.FiniteIntermediateField ℓ ⥤
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  obj E := Mon.mk (Profinite.continuousMapRingObj E)
  map f := Mon.ofHom (Profinite.padicSubfieldRingObjMap ℓ (leOfHom f))
  map_id E := by
    apply Mon.Hom.ext
    exact Profinite.padicSubfieldRingObjMap_id ℓ E
  map_comp f g := by
    apply Mon.Hom.ext
    exact Profinite.padicSubfieldRingObjMap_comp ℓ (leOfHom f) (leOfHom g)

/-- The canonical finite-field cocone as a cocone of rings; its legs are the inclusions
into the finite-subextension-valued algebraic-closure coefficients.
Source: third display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbFiniteSubfieldRingCocone (ℓ : ℕ) [Fact ℓ.Prime] :
    Cocone (sfbFiniteSubfieldRingDiagram.{u} ℓ) where
  pt := Mon.mk (Profinite.padicAlgClRingObj ℓ)
  ι :=
    { app E := Mon.ofHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      naturality := fun E F f ↦ by
        apply Mon.Hom.ext
        exact (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- The standard finite constant coefficient rings `ZMod (ℓ^n)`, with reduction maps.
Source: final paragraph of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbZModCoefficientTower (ℓ : ℕ) : ℕᵒᵖ ⥤ RingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ RingCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (fun n : ℕ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).comp
        ULift.ringEquiv.toRingHom)))

/-- The three completed-coefficient comparisons, their inverse-image compatibility, and
specialization to `ℤ_ℓ` and `ℚ_ℓ`.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-sfb-qlbar-colimit-x/_section.md, all displayed formulas
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: (1) det-prop-sfb-qlbar-colimit-x-integral-limit identifies both the pulled-back
integers and the inverse limit of constant reductions with the sheaf represented by
`X[𝒪_E]`; their ring operations agree by representability. This supplies the normalized
limit cone. (2) det-prop-sfb-qlbar-colimit-x-invert-ell identifies the sequential module
colimit with `E_X` by the maps `ℓ^(-m) φ`. The ring structure is the localization one;
its universal property gives the final clause of SfbCompletedCoefficientComparison.
(3) On the point, each section of the algebraic-closure coefficients lies in a finite
subextension. Compatible maps therefore glue uniquely, using a common finite compositum
to check addition and multiplication. (4) The left adjoint `p_X^*` preserves this colimit
of abelian sheaves. The unit and multiplication are preserved, since tensor preserves
colimits separately and every pair of finite subextensions lies in a common finite
subextension. Thus this is also a colimit of ring objects. (5) Adjunction and Yoneda
identify the inverse image of a representable with its base change. In particular,
`Y[𝒪_E] ×_Y X = X[𝒪_E]`, including all reduction projections. Hence the pulled-back
integral cone is still limiting; this does not assert preservation of arbitrary limits.
(6) For the two colimits, inverse image preserves colimits and the monoidal comparison
`upperStarFromPointComp` respects every inclusion and every multiplication by `ℓ`.
Uniqueness of the induced colimit maps gives precisely the displayed naturality of
all the rationalization legs and the finite-field legs. (7) At `E = ℚ_ℓ`, the integers
are `ℤ_ℓ`, with uniformizer `ℓ` and quotients `ZMod (ℓ^n)` by def-weil-l-adic-numbers;
these identifications commute with reductions, giving the last two formulas.
-/
theorem sfb_completed_coefficients (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (π : PadicAlgCl.integers ℓ E),
      IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span ({π} : Set _) →
      SfbCompletedCoefficientComparison.{u} ℓ (PadicAlgCl.integers ℓ E) E
        (Ideal.span ({π} : Set _))
        (fun X ↦ Mon.ofHom (padicIntegersToPadicSubfield X ℓ E))) ∧
    SfbCompletedCoefficientComparison.{u} ℓ ℤ_[ℓ] ℚ_[ℓ]
      (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]))
      (sfbCoefficientInclusion ℤ_[ℓ] ℚ_[ℓ] PadicInt.Coe.ringHom
        continuous_subtype_val) ∧
    (∃ e : sfbCoefficientQuotientTower ℤ_[ℓ]
        (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ≅ sfbZModCoefficientTower.{u} ℓ,
      ∀ (n : ℕ) (x : ℤ_[ℓ]),
        (e.hom.app (op n)).hom (ULift.up (Ideal.Quotient.mk
          (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ n) x)) =
            ULift.up (PadicInt.toZModPow n x)) ∧
    (∀ X : Scheme.{u}, Nonempty (IsColimit
      ((upperStarFromPoint X).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ)))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), Nonempty (IsColimit
      ((upperStar Ab.{u + 1} f).mapMon.mapCocone
        ((upperStarFromPoint Y).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ))))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (E : PadicAlgCl.FiniteIntermediateField ℓ),
      (upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl Y ℓ E) ≫
          condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f =
        condensedPullbackHom (Profinite.continuousMapRingObj E) f ≫
          padicSubfieldRingObjToPadicAlgCl X ℓ E) := by
  sorry

end AlgebraicGeometry.ProEtale
