/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.ConstructibleSheaf.Pullback
/-!
# A common local basis for all signed finite Tate powers

The primitive-root etale cover gives a basis without any finiteness condition on A.
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct

private theorem finiteTwistIntPreimageApply
    {M N : ModuleCat.{u + 1} ℤ}
    (f : (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat).obj N) (z : M) :
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat).preimage f).hom z = f.hom z := by
  exact ConcreteCategory.congr_hom
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat).map_preimage f) z

private noncomputable def finiteTwistSectionIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (T : Scheme.{u}) (W : T.Etaleᵒᵖ) :
    (ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA)).obj
        (finiteEtaleMuModuleObj T m W) ≅
      (ModuleCat.extendScalarsAddCommGrp A).obj ((T.rootsOfUnitySheaf m).obj.obj W) := by
  let M := finiteEtaleMuModuleObj T m W
  let e : (ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA)).obj M ≅
      ModuleCat.of A (A ⊗[ℤ] M) := by
    letI := Module.compHom A (finiteEtaleTwistScalar m A hA)
    letI : TensorProduct.CompatibleSMul ℤ (ZMod m) A M := ⟨by
      intro c a z
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
      simp only [Int.cast_smul_eq_zsmul]
      exact TensorProduct.smul_tmul k a z⟩
    exact (TensorProduct.equivOfCompatibleSMul ℤ (ZMod m) A A M).toModuleIso
  let G := (T.rootsOfUnitySheaf m).obj.obj W
  let f : ModuleCat.of ℤ M ≅
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv.obj G :=
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).preimageIso
      ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.counitIso.app G).symm
  let AA := (ModuleCat.restrictScalars (Int.castRingHom A)).obj (ModuleCat.of A A)
  letI : Module ℤ AA := AA.isModule
  let ea : A ≃ₗ[ℤ] AA := (AddEquiv.refl A).toIntLinearEquiv
  let N := (ModuleCat.extendScalars (Int.castRingHom A)).obj (ModuleCat.of ℤ M)
  let ee := TensorProduct.congr ea (LinearEquiv.refl ℤ M)
  letI : Module ℤ (A ⊗[ℤ] M) := TensorProduct.instModule
  letI : Module ℤ (AA ⊗[ℤ] M) := TensorProduct.instModule
  let ad := ee.toAddEquiv
  let e' : ModuleCat.of A (A ⊗[ℤ] M) ≅ N :=
    (ad.toLinearEquiv (R := A) (by
      intro a x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b z =>
        simp only [ad, ee, TensorProduct.smul_tmul']
        rfl
      | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ HAdd.hAdd hx hy
      )).toModuleIso
  exact e ≪≫ e' ≪≫ (ModuleCat.extendScalars (Int.castRingHom A)).mapIso f

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteTwistLineIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (T : Scheme.{u}) :
    finiteEtaleTateLine T m A hA ≅ (Etale.extendScalars A T).obj (T.rootsOfUnitySheaf m) := by
  let e : finiteEtaleMuModulePresheaf T m ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA) ≅
      (T.rootsOfUnitySheaf m).obj ⋙ ModuleCat.extendScalarsAddCommGrp A :=
    NatIso.ofComponents (finiteTwistSectionIso A m hA T) (by
      intro W W' f
      ext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa only [map_add] using congrArg₂ HAdd.hAdd hx hy
      | tmul a z =>
        let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
        have hn := ConcreteCategory.congr_hom
          (V.asEquivalence.counitIso.inv.naturality ((T.rootsOfUnitySheaf m).obj.map f)) z
        have hh := congrArg
          (fun z' : V.inv.obj ((T.rootsOfUnitySheaf m).obj.obj W') ↦
            (a ⊗ₜ[ℤ, Int.castRingHom A] z' :
              (ModuleCat.extendScalarsAddCommGrp A).obj ((T.rootsOfUnitySheaf m).obj.obj W')))
          hn
        convert hh using 1 <;>
          dsimp [finiteTwistSectionIso, ModuleCat.extendScalarsAddCommGrp,
            ModuleCat.extendScalars, ModuleCat.ExtendScalars.map', LinearMap.baseChange,
            TensorProduct.AlgebraTensorModule.map, TensorProduct.AlgebraTensorModule.lift,
            TensorProduct.equivOfCompatibleSMul, TensorProduct.mapOfCompatibleSMul]
        · rfl
        · change a ⊗ₜ[ℤ, Int.castRingHom A]
              ((V.preimage (X := ModuleCat.of ℤ (finiteEtaleMuModuleObj T m W'))
                (Y := V.inv.obj ((T.rootsOfUnitySheaf m).obj.obj W'))
                (V.asEquivalence.counitIso.inv.app ((T.rootsOfUnitySheaf m).obj.obj W'))).hom
                  (((T.rootsOfUnitySheaf m).obj.map f).hom z)) = _
          rw [finiteTwistIntPreimageApply]
          rfl
        · change a ⊗ₜ[ℤ, Int.castRingHom A]
              ((V.inv.map ((T.rootsOfUnitySheaf m).obj.map f)).hom
                ((V.preimage (X := ModuleCat.of ℤ (finiteEtaleMuModuleObj T m W))
                  (Y := V.inv.obj ((T.rootsOfUnitySheaf m).obj.obj W))
                  (V.asEquivalence.counitIso.inv.app
                    ((T.rootsOfUnitySheaf m).obj.obj W))).hom z)) = _
          rw [finiteTwistIntPreimageApply]
          rfl)
  exact (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso e

private noncomputable def finiteTwistPositiveTrivialization
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (T : Scheme.{u}) (hA : (m : A) = 0)
    (U : T.Etale)
    (e : (Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj
        (finiteEtaleTateLine T m A hA) ≅ 𝟙_ _) :
    ∀ n : ℕ, (Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj
        (finiteEtaleTateTwist T m A hA n) ≅ 𝟙_ _
  | 0 => (Functor.Monoidal.εIso _).symm
  | 1 => e
  | n + 2 =>
    asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) U.hom)
      (finiteEtaleTateTwist T m A hA (n + 1)) (finiteEtaleTateLine T m A hA)) ≪≫
    tensorIso (finiteTwistPositiveTrivialization A m T hA U e (n + 1)) e ≪≫ λ_ _

private noncomputable def finiteTwistSignedTrivialization
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (T : Scheme.{u}) (hA : (m : A) = 0)
    (U : T.Etale)
    (e : (Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj
        (finiteEtaleTateLine T m A hA) ≅ 𝟙_ _) :
    ∀ a : ℤ, (Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj
        (finiteEtaleTateSheaf A m T hA a) ≅ 𝟙_ _
  | .ofNat n => finiteTwistPositiveTrivialization A m T hA U e n
  | .negSucc n => by
    let G := Etale.upperStar (ModuleCat.{u + 1} A) U.hom
    let P := finiteEtaleTateTwist T m A hA (n + 1)
    haveI := Etale.isIso_ihomComparison_upperStar (ModuleCat.{u + 1} A) U.hom P
    exact asIso ((Functor.LaxMonoidal.ihomComparison G P).natTrans.app (𝟙_ _)) ≪≫
      (ihom (G.obj P)).mapIso (Functor.Monoidal.εIso G).symm ≪≫
      MonoidalClosed.ihomIsoOfIsoLeft
        (finiteTwistPositiveTrivialization A m T hA U e (n + 1)) _ ≪≫
      MonoidalClosed.unitIsoSelf _

private theorem finiteTwistOverTrivialization
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (T : Scheme.{u}) (hA : (m : A) = 0)
    (U : T.Etale)
    (eU : (Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj
      (finiteEtaleTateLine T m A hA) ≅ 𝟙_ _) (a : ℤ) :
    Nonempty ((finiteEtaleTateSheaf A m T hA a).over U ≅
      (constantSheaf (T.smallEtaleTopology.over U) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A)) := by
  let E := Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let eC := ((Etale.overEquiv U).constantSheafSheafCongrIso
    (T.smallEtaleTopology.over U) U.left.smallEtaleTopology
    (ModuleCat.{u + 1} A) CategoryTheory.Over.mkIdTerminal).app (ModuleCat.of A A)
  exact ⟨E.fullyFaithfulFunctor.preimageIso
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U
        (finiteEtaleTateSheaf A m T hA a) ≪≫
      finiteTwistSignedTrivialization A m T hA U eU a ≪≫ eC.symm)⟩

set_option maxHeartbeats 1000000 in
-- Elaborating the primitive-root cover and its iterated pullback needs extra heartbeats.
/-- A cyclic roots basis trivializes every signed Tate power on the same cover.
Source: Stacks Project, Etale Cohomology, Tag 03PK, section-kummer; Modules on Sites,
Tags 03EK and 04TT (blueprint: lem-asd-finite-twist-common-local-bases).
Proof: Pull back the primitive-root cover of Spec Gamma(T). It is etale and
surjective, and its tautological root has invertible differences of distinct powers.
The proved source roots comparison and constant-cyclic comparison identify the
pulled-back roots sheaf with constant ZMod m. Extending coefficients identifies it
with constant A. The sectionwise change from ZMod m to integer tensor products is
an isomorphism since both scalar actions agree; naturality follows from the counit
of the equivalence between integer modules and abelian groups. Sheafification gives
the required comparison with the published coefficient line. Tensor its basis
recursively for positive powers. For negative powers use the inverse-image internal
Hom comparison and evaluation of a functional at the basis. Transfer these
trivializations to the slice site by the over-site equivalence. The single cover
is independent of the signed exponent. -/
theorem finiteEtaleTwistCommonLocalBases (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) :
    (∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
        Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) := by
  let : NeZero m := ⟨hm.ne'⟩
  intro T hT
  have : Etale (primitiveRootsCover Γ(T, ⊤) m) :=
    etale_primitiveRootsCover _ _ hm.ne' hT
  let q := pullback.fst T.toSpecΓ (primitiveRootsCover Γ(T, ⊤) m)
  let P := pullback T.toSpecΓ (primitiveRootsCover Γ(T, ⊤) m)
  let ζ : Γ(P, ⊤)ˣ :=
    ((PrimitiveRootsAlgebra.isUnit_zeta Γ(T, ⊤) m hm).map
      ((Scheme.ΓSpecIso (.of (PrimitiveRootsAlgebra Γ(T, ⊤) m))).inv ≫
        (pullback.snd T.toSpecΓ (primitiveRootsCover Γ(T, ⊤) m)).appTop).hom).unit
  let φ : PrimitiveRootsAlgebra Γ(T, ⊤) m →+* Γ(P, ⊤) :=
    ((Scheme.ΓSpecIso (.of (PrimitiveRootsAlgebra Γ(T, ⊤) m))).inv ≫
      (pullback.snd T.toSpecΓ (primitiveRootsCover Γ(T, ⊤) m)).appTop).hom
  have hz : (ζ : Γ(P, ⊤)) = φ (PrimitiveRootsAlgebra.zeta Γ(T, ⊤) m) :=
    IsUnit.unit_spec _
  have hζ : ζ ^ m = 1 := by
    apply Units.ext
    change (ζ : Γ(P, ⊤)) ^ m = 1
    rw [hz, ← map_pow, PrimitiveRootsAlgebra.zeta_pow, map_one]
  have hζ' : ∀ i < m, ∀ j < m, i ≠ j → IsUnit ((ζ : Γ(P, ⊤)) ^ i - (ζ : Γ(P, ⊤)) ^ j) := by
    intro i hi j hj hij
    rw [hz, ← map_pow, ← map_pow, ← map_sub]
    exact (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow Γ(T, ⊤) m hi hj hij).map φ
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v, hv⟩ := surjective_primitiveRootsCover Γ(T, ⊤) m hT (T.toSpecΓ x)
    obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hv.symm
    exact ⟨y, hy⟩
  let U : Cover.{u} etalePrecoverage T :=
    Cover.mkOfCovers PUnit.{u + 1} (fun _ ↦ P) (fun _ ↦ q)
      (fun x ↦ by obtain ⟨y, hy⟩ := hq x; exact ⟨PUnit.unit, y, hy⟩)
  have := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit m q hT
  have := P.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub m ζ hζ hζ'
  let e : (Etale.upperStar (ModuleCat.{u + 1} A) q).obj
      (finiteEtaleTateLine T m A hA) ≅ 𝟙_ _ :=
    (Etale.upperStar (ModuleCat.{u + 1} A) q).mapIso (finiteTwistLineIso A m hA T) ≪≫
    (Etale.upperStarExtendScalarsIso A q).app (T.rootsOfUnitySheaf m) ≪≫
    (Etale.extendScalars A P).mapIso
      (asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m q)) ≪≫
    (Etale.extendScalars A P).mapIso
      (asIso (P.constantZModToRootsOfUnitySheaf m ζ hζ)).symm ≪≫
    Etale.extendScalarsConstantZModIso P hA
  exact ⟨U, fun i a ↦ finiteTwistOverTrivialization A m T hA
    (U.etalePrecoverageToEtale i) e a⟩

end AlgebraicGeometry.Scheme
