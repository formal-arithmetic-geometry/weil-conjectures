/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PurInverseImageTensorHom

import all Sheaf.Paper.ScalarExtensionDualLocalIso
import all Sheaf.Paper.PurTwistSheafLocallyFree
import all Sheaf.Paper.PurInverseImageScalarComparison
import all Sheaf.Paper.PurTwistRootLocalModels
import all Sheaf.Paper.PurTwistIntegralLocalModels
import all Sheaf.Paper.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.LineUnboundedDerivedTensor
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import all Sheaf.Paper.IntegralLineReductionRestriction
import Sheaf.Paper.CompletedLineTensorCoherence
import Sheaf.Paper.IntegralObjectPullbackLine
import Sheaf.Paper.CommonStageTensorLineCoherence
import Sheaf.Paper.DerivedPullbackTensorIso
import all Sheaf.Paper.FiniteLineTensorConditions
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.CompletedTensorScalarLinearity
import all Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-! # Tate twists are well defined and locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3)
(blueprint: det-def-sp-tate-twist-locally-free).

The helpers specialize the recorded constant sheaf, root module, scalar extension,
signed line and tensor functors. All positive root levels are indexed by `n + 1`.
The theorem includes one common cover, normalized generators, canonical Kummer
independence, signed invertible lines and equivalences with the negative twists.

## Main definitions

* `TateSignedLine` states rank one, same-cover triviality and the tensor inverse.
* `TateRationalSignedLine` and `TateQbarSignedLine` express the same clauses in the
  recorded integral-representative categories, with the canonical restriction functors.
* `TateInverseTwists` fixes the actual functor and negative inverse of an equivalence.

## Main statements

* `tateTwist_locallyFree` states all three source clauses for all four coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The constant commutative coefficient sheaf in clause (2).
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
abbrev tateFiniteCoefficient (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- Apply the canonical quotient coefficient homomorphism to constant sheaves.
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteScalar (X : Scheme.{u}) (ℓ : ℕ) (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    purTwistFiniteRing X ℓ n ⟶ tateFiniteCoefficient X A :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (a.comp ULift.ringEquiv.toRingHom))

/-- The finite A-line is exactly the recorded roots module tensored with A_X.
Source: blueprint clauses (2)--(3) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteLine (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n)

/-- The normalized pure tensor used to specify the Kummer-induced morphism.
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteTensor (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
    (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)) :
    (tateFiniteLine X ℓ A n a).val.obj (op V) :=
  purScalarSection (purTwistFiniteRing X ℓ n) (tateFiniteCoefficient X A)
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n) V b x

/-- Signed line clauses on a specified cover: rank one, the same-cover trivializations,
and the positive/negative tensor pairing. All powers and duals are the recorded ones.
Source: blueprint clause (3) (blueprint: det-def-sp-tate-twist-locally-free). -/
def TateSignedLine (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ m : ℤ, (coefficientTwistLine X (R := R) L m).IsFiniteLocallyFreeOfRank 1 ∧
    ∀ i : I, Nonempty ((coefficientTwistLine X (R := R) L m).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X R)).over (U i))) ∧
  ∀ n : ℕ, Nonempty
    ((SheafOfModules.siteSheafTensorRight (A := R)
      (coefficientTwistLine X L (-(n : ℤ)))).obj (coefficientTwistLine X L n) ≅
        SheafOfModules.unit (purTwistRing X R))

/-- The recorded exact tensor model of K(m), now also for an arbitrary finite A-line.
Source: blueprint clause (3), final paragraph
(blueprint: det-def-sp-tate-twist-locally-free). -/
def tateComplexTwist (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    (hL : L.IsFiniteLocallyFreeOfRank 1) (m : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} (purTwistRing X R)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  letI := hL
  letI := (coefficientTwistLine_exact X L m).1
  letI := (coefficientTwistLine_exact X L m).2.1
  letI := (coefficientTwistLine_exact X L m).2.2
  (SheafOfModules.siteSheafTensorRight (A := R) (coefficientTwistLine X L m)).mapDerivedCategory

/-- Fixing the right input of a published tensor bifunctor retains its full arrow action.
Source: blueprint K(m) formula (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateTensorRight {C : Type c} [Category.{h} C] (T : C × C ⥤ C) (L : C) : C ⥤ C :=
  (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T

/-- An equivalence whose actual functor and inverse are the two prescribed twists.
Source: blueprint clause (3), final sentence
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateInverseTwists {C : Type c} [Category.{h} C] (F G : C ⥤ C) : Prop :=
  ∃ e : C ≌ C, e.functor = F ∧ e.inverse = G

/-- The canonical bounded integral twist uses the recorded intrinsic coefficient line.
Source: blueprint clause (3), integral case
(blueprint: det-def-sp-tate-twist-locally-free). -/
def tateIntegralTwist (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :=
  tateTensorRight (constructibleIntegralTensor ℓ E X)
    (intrinsicIntegralCoefficientTwist D ℓ hD E X m)

/-- The rational twist tensors with the localization of the same integral representative.
Source: blueprint clause (3), rational case
(blueprint: det-def-sp-tate-twist-locally-free). -/
def tateRationalTwist (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :=
  tateTensorRight (rationalDerivedTensor ℓ E X)
    ((sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m))

/-- Transport invertibility along the actual residue-field homomorphism.
Source: the cover in blueprint clause (3)
(blueprint: det-def-sp-tate-twist-locally-free). -/
@[instance_reducible] def tatePullbackInvertible (ℓ : ℕ) {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∀ y : Y, Invertible (ℓ : Y.residueField y) :=
  fun y ↦ (map_natCast (f.residueFieldMap y).hom ℓ) ▸
    Invertible.map (f.residueFieldMap y).hom (ℓ : X.residueField (f y))

/-- The rational signed lines, interpreted in the recorded rational category:
every signed degree-zero line restricts to the coefficient unit on this cover,
and the positive/negative tensor product is the coefficient unit globally.
The integral representative of the coefficient unit is the published zero twist.
Source: blueprint clause (3), rational interpretation via def-coefficient-twists-detailed
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateRationalSignedLine (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ (m : ℤ) (i : I),
    letI := tatePullbackInvertible ℓ (U i).hom
    Nonempty ((rationalDerivedPullback ℓ E (U i).hom).obj
      ((sfRationalConstructibleLocalization ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X m)) ≅
      (sfRationalConstructibleLocalization ℓ E (U i).left).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E (U i).left 0))) ∧
  ∀ n : ℕ, Nonempty ((rationalDerivedTensor ℓ E X).obj
    ((sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X n),
      (sfRationalConstructibleLocalization ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X (-(n : ℤ)))) ≅
    (sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X 0))

/-- The same signed local-line and tensor-inverse clauses in the recorded literal
common-stage category. Both restriction and tensor are the canonical published functors;
the coefficient unit is the least-stage zero twist, not an arbitrarily chosen object.
Source: blueprint clause (3), Qbar interpretation via def-coefficient-twists-detailed
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateQbarSignedLine (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ (m : ℤ) (i : I),
    letI := tatePullbackInvertible ℓ (U i).hom
    Nonempty ((commonStageDerivedPullback ℓ Ω (U i).hom).obj
      (intrinsicQbarCoefficientTwist D ℓ hD X Ω m) ≅
      intrinsicQbarCoefficientTwist D ℓ hD (U i).left Ω 0)) ∧
  ∀ n : ℕ, Nonempty ((commonStageDerivedTensor ℓ Ω X).obj
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω n,
      intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ))) ≅
    intrinsicQbarCoefficientTwist D ℓ hD X Ω 0)

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

private theorem tateAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
attribute [local instance 20000] tateAbSheafify
private theorem tateAbBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X
attribute [local instance 20000] tateAbBijective

private theorem tateWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (tateAbSheafify X).isRightAdjoint
attribute [local instance 20000] tateWeakSheafify

private theorem tateSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] tateSiteSmall

@[instance_reducible] private def tateDerived (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  HasDerivedCategory.standard _
attribute [local instance 20000] tateDerived


private theorem tateLineDerivedInverse (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    (hL : L.IsFiniteLocallyFreeOfRank 1) (m : ℤ) :
    TateInverseTwists.{u + 2, u + 2} (tateComplexTwist.{u} X R L hL m)
      (tateComplexTwist.{u} X R L hL (-m)) := by
  let := hL
  let F : SheafOfModules.{u + 1} (purTwistRing X R) ⥤
      SheafOfModules.{u + 1} (purTwistRing X R) :=
    SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := R) (coefficientTwistLine.{u} X L m)
  let G : SheafOfModules.{u + 1} (purTwistRing X R) ⥤
      SheafOfModules.{u + 1} (purTwistRing X R) :=
    SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := R) (coefficientTwistLine.{u} X L (-m))
  let := (coefficientTwistLine_exact X L m).1
  let := (coefficientTwistLine_exact X L m).2.1
  let := (coefficientTwistLine_exact X L m).2.2
  let := (coefficientTwistLine_exact X L (-m)).1
  let := (coefficientTwistLine_exact X L (-m)).2.1
  let := (coefficientTwistLine_exact X L (-m)).2.2
  have a : F ⋙ G ≅ 𝟭 _ := (signedLineTensor_equivalence.{u} X R L m).2.some
  have b : G ⋙ F ≅ 𝟭 _ := by
    simpa only [neg_neg] using (signedLineTensor_equivalence.{u} X R L (-m)).2.some
  have da : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso _
  have db : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso G F).symm ≪≫
      Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryIdIso _
  exact ⟨CategoryTheory.Equivalence.mk F.mapDerivedCategory G.mapDerivedCategory
    da.symm db, rfl, rfl⟩

private theorem tateSignedLine_of_trivial (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    [L.IsFiniteLocallyFreeOfRank 1] {I : Type (u + 1)} (U : I → X.ProEt)
    (h : ∀ i, Nonempty (L.over (U i) ≅ (SheafOfModules.unit.{u, u + 1, u + 1} _).over (U i))) :
    TateSignedLine X R L U := by
  constructor
  · intro m
    refine ⟨(signedLineTensor_equivalence.{u} X R L m).1, fun i ↦ ?_⟩
    exact ⟨lineSignedOverUnit X R L (U i) (h i).some m⟩
  · intro n
    let C := SheafOfModules.{u + 1} (purTwistRing X R)
    let P := coefficientTwistLine.{u} X (R := R) L (n : ℤ)
    let Q := coefficientTwistLine.{u} X (R := R) L (-(n : ℤ))
    have a := (signedLineTensor_equivalence.{u} X R L (n : ℤ)).2.some
    have e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) P).obj
        (SheafOfModules.unit.{u, u + 1, u + 1} _) ≅ P := by
      let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
      let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
      let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
      exact (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R P).app _ ≪≫
        MonoidalCategory.leftUnitor P
    exact ⟨(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := R) Q).mapIso e.symm ≪≫
      a.app (SheafOfModules.unit.{u, u + 1, u + 1} _)⟩

private noncomputable def tateResidueLinearLift (X : Scheme.{u}) (ℓ n : ℕ)
    (M P : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj P) : M ⟶ P := by
  let a := Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallySurjective (ProEt.topology X) a := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  let g : (PresheafOfModules.restrictScalars a).obj M.val ⟶
      (PresheafOfModules.restrictScalars a).obj P.val :=
    PresheafOfModules.homMk f.hom (by
      intro V b x
      obtain ⟨b⟩ := b
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
      change f.hom.app V
          (@SMul.smul _ _ (M.val.obj V).isModule.toSMul
            (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) x) =
        @SMul.smul _ _ (P.val.obj V).isModule.toSMul
          (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) (f.hom.app V x)
      rw [map_intCast]
      calc
        _ = f.hom.app V (z • (x : M.val.obj V)) := congrArg (f.hom.app V)
          (@Int.cast_smul_eq_zsmul ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
            (M.val.obj V) _ _ (M.val.obj V).isModule z x)
        _ = z • f.hom.app V x := (f.hom.app V).hom.map_zsmul z x
        _ = _ := (@Int.cast_smul_eq_zsmul
          ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
          (P.val.obj V) _ _ (P.val.obj V).isModule z (f.hom.app V x)).symm)
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a P.isSheaf).symm g⟩

private theorem tateRootTransition_comp (X : Scheme.{u}) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ∣ b) (hbc : b ∣ c) :
    proEtaleRootsOfUnityTransition X b c hb hc hbc ≫
        proEtaleRootsOfUnityTransition X a b ha hb hab =
      proEtaleRootsOfUnityTransition X a c ha hc (hab.trans hbc) := by
  have : Mono (proEtaleRootsOfUnityInclusion X a) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  apply (cancel_mono (proEtaleRootsOfUnityInclusion X a)).mp
  simp only [proEtaleRootsOfUnityInclusion, proEtaleRootsOfUnityTransition,
    Category.assoc, kernel.lift_ι, Preadditive.comp_nsmul,
    Category.comp_id, smul_smul]
  change (b / a * (c / b)) • kernel.ι (proEtaleUnitsPower X c) =
    (c / a) • kernel.ι (proEtaleUnitsPower X c)
  exact congrArg (fun q : ℕ ↦ q • kernel.ι (proEtaleUnitsPower X c))
    ((Nat.mul_comm _ _).trans (Nat.div_mul_div hbc hab))

private theorem tateRootTransition_self (X : Scheme.{u}) (a : ℕ) (ha : 0 < a) :
    proEtaleRootsOfUnityTransition X a a ha ha (dvd_refl a) = 𝟙 _ := by
  have : Mono (proEtaleRootsOfUnityInclusion X a) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  apply (cancel_mono (proEtaleRootsOfUnityInclusion X a)).mp
  simp only [proEtaleRootsOfUnityInclusion, proEtaleRootsOfUnityTransition,
    kernel.lift_ι, Nat.div_self ha, one_smul, Category.comp_id, Category.id_comp]

private theorem tateRootTransition_generator (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (V : X.ProEt)
    (ζ : ∀ n : ℕ, (purTwistRootsModule X ℓ n).val.obj (op V))
    (hζ : ∀ n : ℕ,
      (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op V) (ζ (n + 1)) = ζ n)
    (r n : ℕ) (hrn : r ≤ n) :
    (proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) (ζ n) = ζ r := by
  induction n, hrn using Nat.le_induction with
  | base =>
    rw [tateRootTransition_self]
    rfl
  | succ n hn ih =>
    have h := tateRootTransition_comp X (ℓ ^ (r + 1))
      (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hn))
      (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
    let t := proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hn))
    have hh := congrArg (fun f ↦ f.hom.app (op V) (ζ (n + 1))) h
    change t.hom.app (op V)
      ((proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op V) (ζ (n + 1))) =
        (proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op V) (ζ (n + 1)) at hh
    exact hh.symm.trans ((congrArg (t.hom.app (op V)) (hζ n)).trans ih)

private noncomputable def tateKummerMap (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    tateFiniteLine X ℓ A n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
        (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a := by
  let an := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
    (ZMod (ℓ ^ (r + 1))))
  let α := tateFiniteScalar X ℓ A n an
  let β := tateFiniteScalar X ℓ A r a
  let H : SheafOfModules.{u + 1} (purTwistRing X (tateFiniteCoefficient X A)) :=
    tateFiniteLine X ℓ A r a
  let P : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)) :=
    (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj H
  let φ := proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
    (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
  let η := (PurScalar.tensorAdjunction.{u + 1, u + 1, u}
    (K := ProEt.topology X) β).unit.app (purTwistRootsModule X ℓ r)
  let q : (SheafOfModules.toSheaf _).obj (purTwistRootsModule X ℓ n) ⟶
      (SheafOfModules.toSheaf _).obj P :=
    φ ≫ (SheafOfModules.toSheaf _).map η
  exact SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α (purTwistRootsModule X ℓ n) H
    (tateResidueLinearLift X ℓ n _ P q)

private theorem tateKummerMap_tmul (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) (V : X.ProEt)
    (b : (tateFiniteCoefficient X A).obj.obj (op V))
    (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)) :
    (tateKummerMap X ℓ A r n hrn a).val.app (op V)
      (tateFiniteTensor X ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
          (ZMod (ℓ ^ (r + 1))))) V b x) =
      tateFiniteTensor X ℓ A r a V b
        ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x) := by
  unfold tateKummerMap
  erw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}]
  change b • (show (tateFiniteLine X ℓ A r a).val.obj (op V) from
    (((PurScalar.tensorAdjunction.{u + 1, u + 1, u}
    (K := ProEt.topology X) (tateFiniteScalar X ℓ A r a)).unit.app
      (purTwistRootsModule X ℓ r)).val.app (op V)
        ((proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op V) x))) = _
  rw [PurScalar.tensorUnit_section]
  change b • SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
    (tateFiniteScalar X ℓ A r a) (purTwistRootsModule X ℓ r) (op V) 1 _ =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (tateFiniteScalar X ℓ A r a) (purTwistRootsModule X ℓ r) (op V) b _
  rw [SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}, mul_one]

private theorem tateKummerMap_localIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (V : X.ProEt)
    (ζ : ∀ n : ℕ, (purTwistRootsModule X ℓ n).val.obj (op V))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over V ≅
        (purTwistRootsModule X ℓ n).over V)
    (he : ∀ (n : ℕ) (W : (Over V)ᵒᵖ)
      (b : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over V).obj.obj W),
      (e n).hom.val.app W b =
        b • (purTwistRootsModule X ℓ n).val.map W.unop.hom.op (ζ n))
    (r n : ℕ) (hrn : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* A)
    (hζ : (proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) (ζ n) = ζ r) :
    IsIso ((tateKummerMap X ℓ A r n hrn a).over V) := by
  let an := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
    (ZMod (ℓ ^ (r + 1))))
  let en := SheafOfModules.extendedBasisIso.{u + 1, u, u + 1}
    (tateFiniteScalar X ℓ A n an) (purTwistRootsModule X ℓ n) (e n).symm
  let er := SheafOfModules.extendedBasisIso.{u + 1, u, u + 1}
    (tateFiniteScalar X ℓ A r a) (purTwistRootsModule X ℓ r) (e r).symm
  have h : en.inv ≫ (tateKummerMap X ℓ A r n hrn a).over V = er.inv := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (tateKummerMap X ℓ A r n hrn a).val.app (op W.unop.left)
        (tateFiniteTensor X ℓ A n an W.unop.left b
          ((e n).hom.val.app W
            (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over V).obj.obj W))) =
      tateFiniteTensor X ℓ A r a W.unop.left b ((e r).hom.val.app W
        (1 : ((purTwistRing X (purTwistFiniteRing X ℓ r)).over V).obj.obj W))
    rw [he n W 1, he r W 1, one_smul, one_smul, tateKummerMap_tmul]
    have hn := NatTrans.naturality_apply
      (proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom W.unop.hom.op (ζ n)
    rw [hζ] at hn
    exact congrArg (tateFiniteTensor X ℓ A r a W.unop.left b) hn
  have hk : (tateKummerMap X ℓ A r n hrn a).over V = en.hom ≫ er.inv := by
    rw [← cancel_epi en.inv, h, ← Category.assoc, en.inv_hom_id, Category.id_comp]
  rw [hk]
  infer_instance

private theorem tateFiniteTrivial (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (he : ∀ i, Nonempty ((purTwistRootsModule X ℓ r).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ r))).over (U i))) :
    ∀ i, Nonempty ((tateFiniteLine X ℓ A r a).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X (tateFiniteCoefficient X A))).over (U i)) := by
  intro i
  exact ⟨SheafOfModules.extendedBasisIso.{u + 1, u, u + 1} (tateFiniteScalar X ℓ A r a)
    (purTwistRootsModule X ℓ r) (he i).some⟩

private theorem tateFiniteSigned (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (he : ∀ i, Nonempty ((purTwistRootsModule X ℓ r).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ r))).over (U i))) :
    ∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
      TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
      ∀ n : ℕ, TateInverseTwists
        (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
        (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
          (-(n : ℤ))) := by
  have ht := tateFiniteTrivial X ℓ A r a U he
  let hL := rank_one_of_cover (tateFiniteLine X ℓ A r a) ⟨I, U, f, hc, ht⟩
  let := hL
  exact ⟨hL, tateSignedLine_of_trivial X _ _ U ht,
    fun n ↦ tateLineDerivedInverse X _ _ hL n⟩

private theorem tateFiniteClause (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
    (e : ∀ (n : ℕ) (i : I),
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
        (purTwistRootsModule X ℓ n).over (U i))
    (hζ : ∀ (n : ℕ) (i : I),
      (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i)) (ζ (n + 1) i) = ζ n i)
    (he : ∀ (n : ℕ) (i : I) (W : (Over (U i))ᵒᵖ)
      (b : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj W),
      (e n i).hom.val.app W b =
        b • (purTwistRootsModule X ℓ n).val.map W.unop.hom.op (ζ n i)) :
    ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ)))) := by
  intro A _ _ r hA
  have hz : (ℓ ^ (r + 1) : A) = 0 := by
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hA 1
  let a : ZMod (ℓ ^ (r + 1)) →+* A :=
    ZMod.castHom (ringChar.dvd (show ((ℓ ^ (r + 1) : ℕ) : A) = 0 by
      simpa only [Nat.cast_pow] using hz)) A
  refine ⟨a, ?_, tateFiniteSigned X ℓ A r a U f hc (fun i ↦ ⟨(e r i).symm⟩)⟩
  intro n hrn
  refine ⟨tateKummerMap X ℓ A r n hrn a, ?_, tateKummerMap_tmul X ℓ A r n hrn a⟩
  have hU : (ProEt.topology X).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  let k := tateKummerMap X ℓ A r n hrn a
  have hk (i : I) : IsIso (k.over (U i)) :=
    tateKummerMap_localIso X ℓ A (U i) (fun m ↦ ζ m i) (fun m ↦ e m i)
      (fun m ↦ he m i) r n hrn a
      (tateRootTransition_generator X ℓ (U i) (fun m ↦ ζ m i) (fun m ↦ hζ m i) r n hrn)
  have hg : IsIso ((SheafOfModules.toSheaf _).map k) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    have := hk i
    exact inferInstanceAs (IsIso ((SheafOfModules.toSheaf _).map (k.over (U i))))
  exact isIso_of_reflects_iso k (SheafOfModules.toSheaf _)

private theorem tateRootCover (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ i, Nonempty ((purTwistZlModule X ℓ).over (U i) ≅
        (SheafOfModules.unit (purTwistRing X (purTwistZlCompletion X ℓ))).over (U i))) := by
  classical
  obtain ⟨I, U, f, hc, hq⟩ := localTowerCover X ℓ
  let e (n : ℕ) (i : I) := (finiteIsoOfAbIso X ℓ n (U i)
    ((hq i).some.app (op n))).symm
  let ζ (n : ℕ) (i : I) :=
    (e n i).hom.val.app (op (Over.mk (𝟙 (U i))))
      (1 : (purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj (op (U i)))
  refine ⟨I, U, f, ζ, e, hc, ?_, ?_, fun i ↦ ⟨completedBasis X ℓ (U i) (hq i).some⟩⟩
  · intro n i
    have h := (hq i).some.inv.naturality (homOfLE (Nat.le_succ n)).op
    have hh := congrArg (fun t ↦ t.hom.app (op (Over.mk (𝟙 (U i))))
      (1 : (purTwistRing X (purTwistFiniteRing X ℓ (n + 1))).obj.obj (op (U i)))) h
    change (proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op (U i))
      (((hq i).some.inv.app (op (n + 1))).hom.app
        (op (Over.mk (𝟙 (U i))))
        (1 : (purTwistRing X (purTwistFiniteRing X ℓ (n + 1))).obj.obj (op (U i)))) =
      ((hq i).some.inv.app (op n)).hom.app (op (Over.mk (𝟙 (U i))))
        (1 : (purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj (op (U i)))
    simp only [proEtaleRootsOfUnityTower, purTwistZlTower,
      Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ] at hh
    change ((hq i).some.inv.app (op n)).hom.app
      (op (Over.mk (𝟙 (U i))))
      ((purTwistFiniteTransition X ℓ n).hom.app (op (U i)) 1) = _ at hh
    rw [map_one] at hh
    exact hh.symm
  · intro n i V a
    have h := PresheafOfModules.naturality_apply (e n i).hom.val
      (Over.homMk V.unop.hom (Category.comp_id _) :
        V.unop ⟶ Over.mk (𝟙 (U i))).op
      (1 : (purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj (op (U i)))
    have h1 : (e n i).hom.val.app V
        (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V) =
        (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i) := by
      change (e n i).hom.val.app V
        ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.map V.unop.hom.op 1) = _ at h
      rw [map_one] at h
      exact h
    calc
      _ = (e n i).hom.val.app V
          (a • (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V)) :=
        by simp
      _ = a • (e n i).hom.val.app V
        (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V) := map_smul _ _ _
      _ = _ := congrArg (a • ·) h1

private theorem tateIntegralTrivial (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (V : X.ProEt) (h : (purTwistZlModule X ℓ).over V ≅
      (SheafOfModules.unit (purTwistRing X (purTwistZlCompletion X ℓ))).over V) :
    Nonempty ((purTwistIntegralModule X ℓ E).over V ≅
      (SheafOfModules.unit (purTwistRing X
        (completedIntegralCommRingSheafUnrestricted ℓ E X))).over V) := by
  have := integralExtensionReverse_isIso X ℓ E
  exact ⟨(SheafOfModules.overFunctor _ V).mapIso
      (asIso (integralExtensionReverse X ℓ E)).symm ≪≫
    SheafOfModules.extendedBasisIso (purTwistCompletedScalarMap X ℓ E)
      (purTwistZlModule X ℓ) h⟩

private theorem tateIntegralTensorComparison (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :
    Nonempty (
      integralCompletedTensor ℓ E X ≅ IntegralOnSlice.completedTensor ℓ E X none
    ) :=
  ⟨((integralCompletedTensorDescent ℓ E X).universal _
    (IntegralOnSlice.completedTensor_global_comparison ℓ E X).some).exists.choose⟩

private theorem tateIntegralCompletedComparison
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      tateIntegralTwist D ℓ hD E X m ⋙ (sfIntegralConstructible ℓ E X).ι ≅
        (sfIntegralConstructible ℓ E X).ι ⋙
          IntegralLineReduction.completed ℓ E X (purTwistIntegralModule X ℓ E) m
    ) := by
  refine ⟨?_⟩
  let F := tateIntegralTwist D ℓ hD E X m
  let T := tateTensorRight (integralCompletedTensor ℓ E X)
    (integralCoefficientTwist D ℓ hD E X m)
  have a : F ⋙ (sfIntegralConstructible ℓ E X).ι ≅
      (sfIntegralConstructible ℓ E X).ι ⋙ T := Iso.refl _
  have b : T ≅ IntegralLineReduction.completed ℓ E X
      (purTwistIntegralModule X ℓ E) m := by
    rw [IntegralLineReduction.completed, integralLineCompleted,
      IntegralLineReduction.power_eq_coefficient]
    let P := (𝟭 (DerivedCategory (integralTowerModules ℓ E X))).prod'
      ((Functor.const _).obj (integralCoefficientTwist D ℓ hD E X m))
    let Q := Prod.sectL (IntegralOnSlice.D ℓ E X none)
      (coefficientTwistLine X (R := completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) m) ⋙
        (𝟭 _).prod (integralLineSingle ℓ E X ⋙ DerivedCategory.Q)
    have q : P ≅ Q := NatIso.ofComponents (fun K ↦ Iso.refl _) (by
      intro K K' f
      change Prod.mkHom f (𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫
        Prod.mkHom f ((integralLineSingle ℓ E X ⋙ DerivedCategory.Q).map (𝟙 _))
      exact (Category.comp_id _).trans
        ((congrArg (Prod.mkHom f) ((integralLineSingle ℓ E X ⋙
          DerivedCategory.Q).map_id _).symm).trans (Category.id_comp _).symm))
    exact Functor.isoWhiskerLeft P (tateIntegralTensorComparison X ℓ E).some ≪≫
      Functor.isoWhiskerRight q (IntegralOnSlice.completedTensor ℓ E X none)
  exact a ≪≫ Functor.isoWhiskerLeft (sfIntegralConstructible ℓ E X).ι b

private theorem tateIntegralFiniteReductions (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E]
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    IntegralLineReduction.FiniteReductions ℓ E X (purTwistIntegralModule X ℓ E) := by
  intro n
  let A := Padic.coefficientExtensionRing ℓ E (n + 1)
  let := Padic.finite_coefficientExtensionRing ℓ E (n + 1) (Nat.succ_pos n)
  let L := (IntegralLineReduction.line ℓ E X (purTwistIntegralModule X ℓ E) n)
  let e : L ≅ purTwistFiniteOne X ℓ E n :=
    eqToIso ((scalarReductionExistence.{u, u} ℓ E X n).choose_spec.choose
      (purTwistIntegralModule X ℓ E)) ≪≫
    SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1}
      (completedIntegralCommRingProjectionUnrestricted ℓ E X n)
        (purTwistIntegralModule X ℓ E) ≪≫
    (((pur_twist_sheaf_locally_free.{u, 0} X ℓ E).2.2.1.2.2.2 n).1).some
  have : L.IsFiniteLocallyFreeOfRank 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
  obtain ⟨I, U, f, hc, he⟩ := line_constant_models X A L
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  refine ⟨ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A), inferInstance, ?_⟩
  exact he i

private theorem tateIntegralInverse (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (ℓ : X.residueField x)]
    (hf : IntegralLineReduction.FiniteReductions ℓ E X (purTwistIntegralModule X ℓ E))
    (m : ℤ) : TateInverseTwists (tateIntegralTwist D ℓ hD E X m)
      (tateIntegralTwist D ℓ hD E X (-m)) := by
  obtain ⟨b, d, e, hb, hd, he, hc, hs, hr⟩ :=
    IntegralLineReduction.integral_line_reduction_restriction ℓ E X hX
      (purTwistIntegralModule X ℓ E) hf
  obtain ⟨h, c, hc, hr⟩ := hr
  obtain ⟨v, w, hv, hw, ho, F, a, b, hF⟩ := hr m
  let inc := (sfIntegralConstructible ℓ E X).ι
  have a' : F.functor ≅ tateIntegralTwist D ℓ hD E X m :=
    Functor.fullyFaithfulCancelRight inc
      (a ≪≫ (tateIntegralCompletedComparison D ℓ hD E X m).some.symm)
  have b' : F.inverse ≅ tateIntegralTwist D ℓ hD E X (-m) :=
    Functor.fullyFaithfulCancelRight inc
      (b ≪≫ (tateIntegralCompletedComparison D ℓ hD E X (-m)).some.symm)
  exact ⟨(F.changeFunctor a').changeInverse b', rfl, rfl⟩

private theorem tateIntegralAdditive (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    (tateIntegralTwist D ℓ hD E X m).Additive := by
  obtain ⟨e, he, hi⟩ := tateIntegralInverse D ℓ hD E X
    (tateIntegralFiniteReductions X ℓ E) m
  have : (tateIntegralTwist D ℓ hD E X m).IsEquivalence := he ▸ inferInstance
  exact Functor.additive_of_preserves_binary_products _

private theorem tateIntegralLinear (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    (tateIntegralTwist D ℓ hD E X m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) where
  map_smul := by
    intro K K' f c
    exact completedTensor_map_smul_left ℓ E X K K'
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m)
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m) f (𝟙 _) c

private noncomputable def tateLocalizedTensorIso
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) (F : C ⥤ C) [F.Additive] [F.Linear R]
    (T : ScalarLocalization R C p ⥤ ScalarLocalization R C p)
    (ho : ∀ K, T.obj K = (ScalarLocalization.map R C p F).obj K)
    (hm : ∀ K K', ∃ q : (K ⟶ K') →ₗ[Localization.Away p]
      (T.obj K ⟶ T.obj K'), ∀ f, T.map f = q f)
    (ht : ∀ (K K' : ScalarLocalization R C p) (c : Localization.Away p)
      (f : K.obj ⟶ K'.obj), HEq (T.map (c ⊗ₜ[R] f)) (c ⊗ₜ[R] F.map f)) :
    T ≅ ScalarLocalization.map R C p F := by
  let G := ScalarLocalization.map R C p F
  let : G.Additive := ScalarLocalization.mapAdditive R C p F
  refine NatIso.ofComponents (fun K ↦ eqToIso (ho K)) ?_
  intro K K' f
  obtain ⟨q, hq⟩ := hm K K'
  change T.map f ≫ eqToHom (ho K') = eqToHom (ho K) ≫ G.map f
  rw [comp_eqToHom_iff, Category.assoc]
  apply (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mpr
  induction f using TensorProduct.induction_on with
  | zero =>
    rw [hq, map_zero, Functor.map_zero]
    exact (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mp (by simp)
  | tmul c f =>
    exact (ht K K' c f).trans
      (heq_of_eq (LinearMap.baseChange_tmul (F.mapLinearMap R) c f).symm)
  | add f g hf hg =>
    rw [hq, map_add, ← hq, ← hq, Functor.map_add]
    exact (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mp (by
      rw [(conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mpr hf,
        (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mpr hg]
      simp only [Preadditive.comp_add, Preadditive.add_comp])

private theorem tateRationalComparison
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      letI := tateIntegralAdditive D ℓ hD E X m
      letI := tateIntegralLinear D ℓ hD E X m
      tateRationalTwist D ℓ hD E X m ≅
        ScalarLocalization.map (Padic.coefficientExtensionIntegers ℓ E)
          (sfIntegralConstructibleCategory ℓ E X)
          (Padic.coefficientExtensionUniformizer ℓ E) (tateIntegralTwist D ℓ hD E X m)
    ) := by
  refine ⟨?_⟩
  letI := tateIntegralAdditive D ℓ hD E X m
  letI := tateIntegralLinear D ℓ hD E X m
  let L := (sfRationalConstructibleLocalization ℓ E X).obj
    (intrinsicIntegralCoefficientTwist D ℓ hD E X m)
  apply tateLocalizedTensorIso (Padic.coefficientExtensionUniformizer ℓ E)
    (tateIntegralTwist D ℓ hD E X m) (tateRationalTwist D ℓ hD E X m)
    (fun K ↦ (rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.1 (K, L))
  · intro K K'
    obtain ⟨b, hb, ht⟩ :=
      (rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.2 K K' L L
    exact ⟨b.flip (𝟙 L), fun g ↦ hb g (𝟙 L)⟩
  · intro K K' c f
    obtain ⟨b, hb, ht⟩ :=
      (rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.2 K K' L L
    have h := ht f (𝟙 L.obj) c 1
    have hh := heq_of_eq (hb (c ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E] f) (𝟙 L))
    exact hh.trans h |>.trans (heq_of_eq (congrArg
      (fun a ↦ a ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E]
        (constructibleIntegralTensor ℓ E X).map (Prod.mkHom f (𝟙 L.obj))) (mul_one c)))

private noncomputable def tateLocalizedPair
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) (U V : C ⥤ C) [U.Additive] [V.Additive] [U.Linear R] [V.Linear R]
    (c : U ⋙ V ≅ 𝟭 C) :
    ScalarLocalization.map R C p U ⋙ ScalarLocalization.map R C p V ≅ 𝟭 _ := by
  let hp : IsUnit (algebraMap R (Localization.Away p) ((RingHom.id R) p)) :=
    IsLocalization.Away.algebraMap_isUnit p
  let q := ScalarLocalization.extensionNatIso p p (RingHom.id R) hp
    (ScalarLocalization.isSemilinear_of_linear (U ⋙ V))
    (ScalarLocalization.isSemilinear_of_linear (𝟭 C)) c
  have hh (W : C ⥤ C) [W.Additive] [W.Linear R] :=
    (ScalarLocalization.extension_id_and_linear (C := C) p).2 W
  rw [hh (U ⋙ V), hh (𝟭 C)] at q
  exact eqToIso (ScalarLocalization.map_comp R C p U V) ≪≫ q ≪≫
    eqToIso (ScalarLocalization.map_identity R C p)

private theorem tateRationalInverse (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    TateInverseTwists (tateRationalTwist D ℓ hD E X m)
      (tateRationalTwist D ℓ hD E X (-m)) := by
  let R := Padic.coefficientExtensionIntegers ℓ E
  let C := sfIntegralConstructibleCategory ℓ E X
  let p : R := Padic.coefficientExtensionUniformizer ℓ E
  let F := tateIntegralTwist D ℓ hD E X m
  let G := tateIntegralTwist D ℓ hD E X (-m)
  let : F.Additive := tateIntegralAdditive D ℓ hD E X m
  let : G.Additive := tateIntegralAdditive D ℓ hD E X (-m)
  let : F.Linear R := tateIntegralLinear D ℓ hD E X m
  let : G.Linear R := tateIntegralLinear D ℓ hD E X (-m)
  obtain ⟨e, he, hi⟩ := tateIntegralInverse D ℓ hD E X
    (tateIntegralFiniteReductions X ℓ E) m
  have a : F ⋙ G ≅ 𝟭 C := by simpa only [he, hi] using e.unitIso.symm
  have b : G ⋙ F ≅ 𝟭 C := by simpa only [he, hi] using e.counitIso
  let q := CategoryTheory.Equivalence.mk
    (ScalarLocalization.map R C p F) (ScalarLocalization.map R C p G)
    (tateLocalizedPair p F G a).symm (tateLocalizedPair p G F b)
  exact ⟨(q.changeFunctor (tateRationalComparison D ℓ hD E X m).some.symm).changeInverse
    (tateRationalComparison D ℓ hD E X (-m)).some.symm, rfl, rfl⟩

private theorem tateLineGood (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (L : integralTowerModules ℓ E X) [L.IsFiniteLocallyFreeOfRank 1] :
    IntegralOnSlice.Good ℓ E X none ((integralLineSingle ℓ E X).obj L) := by
  obtain ⟨_, _, hL, _, hf, _, _⟩ :=
    SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u} X
      (completedIntegralCommRingSheafUnrestricted ℓ E X) L
  exact ⟨hL, hf⟩

private theorem tateIntegralLineProduct
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      (constructibleIntegralTensor ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X m,
          intrinsicIntegralCoefficientTwist D ℓ hD E X (-m)) ≅
        intrinsicIntegralCoefficientTwist D ℓ hD E X 0
    ) := by
  refine ⟨?_⟩
  let L := purTwistIntegralModule X ℓ E
  let P := coefficientTwistLine X
    (R := completedIntegralCommRingSheafUnrestricted ℓ E X) L m
  let T := coefficientTwistLine X
    (R := completedIntegralCommRingSheafUnrestricted ℓ E X) L (-m)
  let K := intrinsicIntegralCoefficientTwist D ℓ hD E X m
  have : P.IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted ℓ E X) L m).1
  have : T.IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted ℓ E X) L (-m)).1
  let PG : (IntegralOnSlice.Good ℓ E X none).FullSubcategory :=
    ⟨(integralLineSingle ℓ E X).obj P, tateLineGood X ℓ E P⟩
  let hT := (tateLineGood X ℓ E T).1
  have ep : DerivedCategory.Q.obj PG.obj ≅ K.obj :=
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app P).symm
  have hc : IntegralOnSlice.IsComplete ℓ E X none K.obj :=
    CompletedLineTensor.intrinsic_complete ℓ E X K
  have hi := IntegralLineReduction.comparison_isIso ℓ E X hX L (-m) K.obj hc
  have a := (tateIntegralCompletedComparison D ℓ hD E X (-m)).some.app K
  have b := (asIso ((IntegralLineReduction.comparison ℓ E X L (-m)).app K.obj)).symm
  have c : (IntegralLineReduction.ordinary ℓ E X L (-m)).obj K.obj ≅
      DerivedCategory.Q.obj (integralLineComplex ℓ E X PG.obj T) := by
    change (integralLineOrdinary ℓ E X).obj
      (K.obj, IntegralLineReduction.power ℓ E X L (-m)) ≅ _
    rw [IntegralLineReduction.power_eq_coefficient]
    exact (integralLineRepresentativeIso ℓ E X PG T hT K.obj ep).symm
  let R := completedIntegralCommRingSheafUnrestricted ℓ E X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have collapse := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (MonoidalCategory.curriedTensor (integralTowerModules ℓ E X)) T
  have single := HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.siteSheafTensorRight
      (A := completedIntegralCommRingSheafUnrestricted ℓ E X) T) (.up ℤ) 0
  have evaluation : (SheafOfModules.siteSheafTensorRight
      (A := completedIntegralCommRingSheafUnrestricted ℓ E X) T).obj P ≅
      SheafOfModules.unit (purTwistRing X
        (completedIntegralCommRingSheafUnrestricted ℓ E X)) := by
    let U := SheafOfModules.unit (purTwistRing X
      (completedIntegralCommRingSheafUnrestricted ℓ E X))
    have ep : (SheafOfModules.siteSheafTensorRight (A := R) P).obj U ≅ P :=
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R P).app U ≪≫
        MonoidalCategory.leftUnitor P
    exact ((SheafOfModules.siteSheafTensorRight (A := R) T).mapIso ep.symm) ≪≫
      (signedLineTensor_equivalence X R L m).2.some.app U
  have e : ((constructibleIntegralTensor ℓ E X).obj (K,
      intrinsicIntegralCoefficientTwist D ℓ hD E X (-m))).obj ≅
      (intrinsicIntegralCoefficientTwist D ℓ hD E X 0).obj :=
    a ≪≫ b ≪≫ c ≪≫ DerivedCategory.Q.mapIso
      (collapse.app PG.obj ≪≫
        ((NatIso.mapHomologicalComplex
          (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R T).symm
          (.up ℤ)).app PG.obj) ≪≫ single.app P ≪≫
        (integralLineSingle ℓ E X).mapIso evaluation) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (integralTowerModules ℓ E X) 0).app
        (SheafOfModules.unit (purTwistRing X R))).symm
  exact (sfIntegralConstructible ℓ E X).ι.preimageIso e

private theorem tateRationalLineProduct
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      (rationalDerivedTensor ℓ E X).obj
        ((sfRationalConstructibleLocalization ℓ E X).obj
          (intrinsicIntegralCoefficientTwist D ℓ hD E X m),
          (sfRationalConstructibleLocalization ℓ E X).obj
            (intrinsicIntegralCoefficientTwist D ℓ hD E X (-m))) ≅
        (sfRationalConstructibleLocalization ℓ E X).obj
          (intrinsicIntegralCoefficientTwist D ℓ hD E X 0)
    ) :=
  ⟨eqToIso ((rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.1 _) ≪≫
    (sfRationalConstructibleLocalization ℓ E X).mapIso
      (tateIntegralLineProduct D ℓ hD E X m).some⟩

private theorem tateCommonTensorOnStage
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (B : AlgebraicallyClosedCoefficients.Index ℓ Ω)
    (M N : sfRationalConstructibleCategory ℓ
      (AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B) X) :
    Nonempty (
      (commonStageDerivedTensor ℓ Ω X).obj
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B |>.obj M,
          (GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B |>.obj N) ≅
        (GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B |>.obj
          ((rationalDerivedTensor ℓ
            (AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B) X).obj (M, N))
    ) := by
  refine ⟨?_⟩
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B
  let P := (S.ι B).obj M
  let Q := (S.ι B).obj N
  have objIso : (commonStageDerivedTensor ℓ Ω X).obj (P, Q) ≅
      commonStageTensorObject ℓ Ω X P Q :=
    eqToIso ((commonStageDerivedTensor_existsUnique ℓ Ω X).exists.choose_spec.1 P Q)
  have hc : Padic.finiteCoefficientCompositum ℓ Ω B B = B := by
    apply Subtype.ext
    simp only [Padic.finiteCoefficientCompositum, sup_idem]
  have unit : S.T (le_refl B) ≅ 𝟭 _ :=
    eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      ℓ Ω X).exists.choose_spec.1 B B (le_refl B)) ≪≫
      GeneralAlgebraicallyClosedCoefficients.unitor ℓ Ω X B
  let h : (commonStageTensorObject ℓ Ω X P Q).stage ≤ B := hc.le
  exact objIso ≪≫ S.isoToStage (commonStageTensorObject ℓ Ω X P Q) h ≪≫
    (S.ι B).mapIso (commonStageTensorComparison ℓ Ω X P Q B h ≪≫
      (rationalDerivedTensor ℓ E X).mapIso (Iso.prod (unit.app M) (unit.app N)))

private theorem tateQbarSigned_of_rational
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    {I : Type (u + 1)} (U : I → X.ProEt)
    (h : TateRationalSignedLine D ℓ hD
      (AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω
        (Padic.finiteCoefficientBase ℓ Ω)) X U) :
    TateQbarSignedLine D ℓ hD X Ω U := by
  let B := Padic.finiteCoefficientBase ℓ Ω
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B
  constructor
  · intro m i
    let := tatePullbackInvertible ℓ (U i).hom
    have a := (h.1 m i).some
    refine ⟨eqToIso ((commonStageDerivedPullback_existsUnique ℓ Ω
      (U i).hom).exists.choose_spec.1 _) ≪≫ ?_⟩
    exact (GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω (U i).left).ι B |>.mapIso a
  · intro n
    exact ⟨(tateCommonTensorOnStage ℓ X Ω B _ _).some ≪≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B).mapIso
        (h.2 n).some⟩

private theorem tateIntegralLocal
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    (W : X.ProEt) [∀ y : W.left, Invertible (ℓ : W.left.residueField y)]
    (e : (purTwistIntegralModule X ℓ E).over W ≅
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted ℓ E X)).over W)
    (m : ℤ) : Nonempty ((constructibleIntegralPullback ℓ E W.hom).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m) ≅
      intrinsicIntegralCoefficientTwist D ℓ hD E W.left 0) := by
  let R := completedIntegralCommRingSheafUnrestricted ℓ E X
  let L := purTwistIntegralModule X ℓ E
  let P := coefficientTwistLine X (R := R) L m
  have hP : P.IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence X R L m).1
  have eP := lineSignedOverUnit X R L W e m
  exact ⟨(sfIntegralConstructible ℓ E W.left).ι.preimageIso
    (integralObjectPullbackLine ℓ E X W P hP eP).some⟩

private theorem tateRationalSigned
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    {I : Type (u + 1)} (U : I → X.ProEt)
    (he : ∀ i, Nonempty ((purTwistIntegralModule X ℓ E).over (U i) ≅
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted ℓ E X)).over
        (U i))) : TateRationalSignedLine D ℓ hD E X U := by
  constructor
  · intro m i
    let := tatePullbackInvertible ℓ (U i).hom
    refine ⟨eqToIso ((rationalDerivedPullback_existsUnique ℓ E
      (U i).hom).exists.choose_spec.2.1 _) ≪≫ ?_⟩
    exact (sfRationalConstructibleLocalization ℓ E (U i).left).mapIso
      (tateIntegralLocal D ℓ hD E X (U i) (he i).some m).some
  · intro n
    exact tateRationalLineProduct D ℓ hD E X n

private noncomputable def tateTensorRightIso
    {C : Type c} [Category.{h} C] (T : C × C ⥤ C) {L M : C} (e : L ≅ M) :
    tateTensorRight T L ≅ tateTensorRight T M := by
  refine NatIso.ofComponents (fun K ↦ T.mapIso (Iso.prod (Iso.refl K) e)) ?_
  intro K K' f
  change T.map (Prod.mkHom f (𝟙 L)) ≫ T.map (Prod.mkHom (𝟙 K') e.hom) =
    T.map (Prod.mkHom (𝟙 K) e.hom) ≫ T.map (Prod.mkHom f (𝟙 M))
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  ext <;> simp

private theorem tateTensorInverse
    {C : Type c} [Category.{h} C] (T : C × C ⥤ C) (U L M : C)
    (a : tateTensorRight T L ⋙ tateTensorRight T M ≅
      tateTensorRight T (T.obj (L, M)))
    (b : tateTensorRight T M ⋙ tateTensorRight T L ≅
      tateTensorRight T (T.obj (M, L)))
    (u : tateTensorRight T U ≅ 𝟭 C)
    (e : T.obj (L, M) ≅ U) (e' : T.obj (M, L) ≅ U) :
    TateInverseTwists (tateTensorRight T L) (tateTensorRight T M) := by
  have aa := a ≪≫ tateTensorRightIso T e ≪≫ u
  have bb := b ≪≫ tateTensorRightIso T e' ≪≫ u
  exact ⟨CategoryTheory.Equivalence.mk (tateTensorRight T L) (tateTensorRight T M)
    aa.symm bb, rfl, rfl⟩


private theorem tateQbarInverse
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (n : ℕ)
    (e : (commonStageDerivedTensor ℓ Ω X).obj
      (intrinsicQbarCoefficientTwist D ℓ hD X Ω n,
        intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ))) ≅
      intrinsicQbarCoefficientTwist D ℓ hD X Ω 0) :
    TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
      (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ))) := by
  obtain ⟨ha, hu⟩ := commonStageTensorLineCoherence ℓ X Ω
  exact tateTensorInverse (commonStageDerivedTensor ℓ Ω X)
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω 0)
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω n)
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ)))
    (ha _ _).some (ha _ _).some hu.some e
    (pullbackTensorCommonBraiding ℓ Ω X _ _ ≪≫ e)

/-- One common covering trivializes the compatible root generators and all coefficient
lines; Kummer transitions induce the canonical A-linear isomorphisms; every signed twist
is a line, with positive and negative twist functors inverse on the specified categories.

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, all three clauses
(blueprint: det-def-sp-tate-twist-locally-free).

Proof:
1. The compatible root-tower local model supplies one pro-etale cover, compatible
   sections at every positive root level, and unit-to-root basis isomorphisms.
   Their naturality gives the displayed transition and slice formulas.
2. Annihilation supplies the quotient map from Z/ell^(r+1) to A. Form the
   scalar-extension adjunct of the specified root transition. Its value on a
   pure tensor is the prescribed Kummer formula. On the root cover it carries
   the chosen generator to the chosen generator, so it is locally and globally
   an isomorphism. Signed-line tensor equivalences give all finite signed powers
   and their two inverse functors on unbounded complexes.
3. Extend the same integral root basis to every finite coefficient field E.
   The completed integral local model identifies this extension with the actual
   integral Tate line. Signed powers and internal duals remain trivial on the
   same cover. The finite scalar reductions are the finite Tate lines already
   constructed, so coherent reduction and reconstruction give the two inverse
   intrinsic integral twist functors.
4. Identify the actual integral right-tensor functor with its completed line
   model. Prove its additivity and scalar linearity. Localize the two inverse
   natural isomorphisms; induction on pure Hom scalar tensors identifies these
   localized functors with the intrinsic rational twist functors.
5. For each signed integral line, the completed pullback calculation for a
   supplied slice basis identifies its actual derived inverse image with the
   regular line. Rational pullback then gives the required rational local
   trivializations. Transport these from the least finite coefficient stage
   to obtain the algebraically closed local trivializations.
6. Compute opposite integral Tate object products using a flat single-complex
   representative, completeness, the ordinary-to-completed comparison and the
   signed evaluation isomorphism. Localize this product to rational
   coefficients and identify the common-stage product on objects from one stage.
7. Natural fixed-right tensor associativity and the specified regular unit in
   the common-stage category combine with the opposite object products (and
   braiding for the reversed product) to give both inverse composites of the
   actual algebraically closed twist functors. Assemble all clauses using the
   original common root cover.
-/
theorem tateTwist_locallyFree
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (ι : E →ₐ[Padic ℓ] Ω) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) ∧
      TateSignedLine X (completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) U ∧
      ∀ (D : FiniteFieldDatum.{d}) (hD : ℓ ≠ D.p),
        TateRationalSignedLine D ℓ hD E X U ∧
        TateQbarSignedLine D ℓ hD X Ω U ∧
        ∀ n : ℕ, TateInverseTwists (tateIntegralTwist D ℓ hD E X n)
          (tateIntegralTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (tateRationalTwist D ℓ hD E X n)
          (tateRationalTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
          (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ))) := by
  classical
  have _ := ι
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hr⟩ := tateRootCover X ℓ
  let hi (F : Type u) [Field F] [Algebra (Padic ℓ) F]
      [FiniteDimensional (Padic ℓ) F] (i : I) :
      Nonempty ((purTwistIntegralModule X ℓ F).over (U i) ≅
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted ℓ F X)).over (U i)) :=
    tateIntegralTrivial X ℓ F (U i) (hr i).some
  refine ⟨I, U, f, ζ, e, hc, hζ, he,
    tateFiniteClause X ℓ U f hc ζ e hζ he,
    tateSignedLine_of_trivial X (completedIntegralCommRingSheafUnrestricted ℓ E X)
      (purTwistIntegralModule X ℓ E) U (hi E), ?_⟩
  intro D hD
  have hE := tateRationalSigned D ℓ hD E X U (hi E)
  let E₀ := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω
    (Padic.finiteCoefficientBase ℓ Ω)
  have hΩ := tateQbarSigned_of_rational D ℓ hD X Ω U
    (tateRationalSigned D ℓ hD E₀ X U (hi E₀))
  refine ⟨hE, hΩ, fun n ↦ ⟨?_, ?_, ?_⟩⟩
  · exact tateIntegralInverse D ℓ hD E X (tateIntegralFiniteReductions X ℓ E) n
  · exact tateRationalInverse D ℓ hD E X n
  · exact tateQbarInverse D ℓ hD X Ω n (hΩ.2 n).some

end AlgebraicGeometry.Scheme
