/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefficientRealization.CoefficientRealizationData
public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateScalarPresentation
import WeilConjectures.SmoothPurity.NativePairCohomology.NativePairHomologyComparison
import WeilConjectures.WeilSheaf.HomologyShift
import WeilConjectures.WeilSheaf.TateTwistCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # The Tate cohomology of a unit-normalized equivariant realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits
namespace WeilConjectures.NativeCoefficientCohomology

open CategoryTheory.Endofunctor
open WeilConjectures.ConstantPurityFrobenius

section ScalarTransport
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} [L.Additive]

private theorem map_scaled_square (θ : L ⋙ G ≅ F ⋙ L)
    (K U : IsoAlgebra F) (a : K.carrier ≅ U.carrier) (n : ℕ)
    (h : n • (K.str.hom ≫ a.hom) = F.map a.hom ≫ U.str.hom) :
    n • (((IsoAlgebra.mapOfNatIso θ).obj K).str.hom ≫ L.map a.hom) =
      G.map (L.map a.hom) ≫ ((IsoAlgebra.mapOfNatIso θ).obj U).str.hom := by
  change n • ((θ.hom.app K.carrier ≫ L.map K.str.hom) ≫ L.map a.hom) =
    G.map (L.map a.hom) ≫ θ.hom.app U.carrier ≫ L.map U.str.hom
  rw [Category.assoc, ← L.map_comp, ← Preadditive.comp_nsmul, ← L.map_nsmul,
    h, L.map_comp, ← Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ L.map U.str.hom) (θ.hom.naturality a.hom).symm

private theorem scaled_square_comp (K U V : IsoAlgebra F)
    (a : K.carrier ≅ U.carrier) (b : U ≅ V) (n : ℕ)
    (h : n • (K.str.hom ≫ a.hom) = F.map a.hom ≫ U.str.hom) :
    n • (K.str.hom ≫ (a ≪≫ (IsoAlgebra.forget F).mapIso b).hom) =
      F.map (a ≪≫ (IsoAlgebra.forget F).mapIso b).hom ≫ V.str.hom := by
  change n • (K.str.hom ≫ (a.hom ≫ b.hom.hom.f)) =
    F.map (a.hom ≫ b.hom.hom.f) ≫ V.str.hom
  rw [← Category.assoc, ← Preadditive.nsmul_comp, h, Category.assoc,
    IsoAlgebra.str_hom, ← b.hom.hom.h, ← Category.assoc, ← F.map_comp]
  rfl

private def shift_transport_iso [HasShift C ℤ] [F.CommShift ℤ]
    (K : IsoAlgebra F) (s : ℤ) :
    K⟦s⟧ ≅ (IsoAlgebra.mapOfNatIso (F.commShiftIso s)).obj K := by
  exact (Algebra.IsIsoStr F).fullyFaithfulι.preimageIso
    (((IsoAlgebra.ι F).commShiftIso s).app K)
end ScalarTransport

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

private def native_shift (K : WeilComplex P.field.k₀ P.coefficients.l X₀.left) (s : ℤ) :
    (NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left).obj (K⟦s⟧) ≅
      ((NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left).obj K)⟦s⟧ := by
  letI : (WeilComplex.objectProperty P.field.k₀ P.coefficients.l
      X₀.left).IsStableUnderShift ℤ := inferInstance
  letI : (WeilComplex.objectProperty P.field.k₀ P.coefficients.l
      X₀.left).ι.CommShift ℤ := inferInstance
  letI : (IsoAlgebra.forget (WeilSheaf.frobeniusPullback P.field.k₀ P.coefficients.l
      X₀.left)).mapDerivedCategory.CommShift ℤ := inferInstance
  letI : (WeilComplex.forget (k₀ := P.field.k₀) (l := P.coefficients.l)
      (X := X₀.left)).CommShift ℤ := by
    dsimp only [WeilComplex.forget]
    infer_instance
  haveI : NatTrans.CommShift
      (NativePairCohomology.theta P.field.k₀ P.coefficients.l X₀.left).hom ℤ := by
    dsimp only [NativePairCohomology.theta, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  let N := NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left
  let F := (WeilSheaf.frobeniusPullback
    P.field.k₀ P.coefficients.l X₀.left).mapDerivedCategory
  let j : N.obj (K⟦s⟧) ≅ (IsoAlgebra.mapOfNatIso (F.commShiftIso s)).obj (N.obj K) :=
    IsoAlgebra.isoMk ((WeilComplex.forget.commShiftIso s).app K) (by
      change F.map ((WeilComplex.forget.commShiftIso s).hom.app K) ≫
          (F.commShiftIso s).hom.app (WeilComplex.forget.obj K) ≫
          (NativePairCohomology.theta P.field.k₀ P.coefficients.l X₀.left).hom.app K⟦s⟧' =
        (NativePairCohomology.theta P.field.k₀ P.coefficients.l X₀.left).hom.app (K⟦s⟧) ≫
          (WeilComplex.forget.commShiftIso s).hom.app K
      simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
        NatTrans.shift_app_comm
          (NativePairCohomology.theta P.field.k₀ P.coefficients.l X₀.left).hom s K)
  exact j ≪≫ (shift_transport_iso (N.obj K) s).symm

private def realized_shifted_unit (R : CoefficientRealization.Data P X₀) (d : ℕ) :
    (CoefficientRealization.pairCohomology P X₀ R (-2 * (d : ℤ))).obj
        ((constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
          P.coefficients.different X₀ P.coefficients.Qbar)⟦2 * (d : ℤ)⟧) ≅
      (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left).obj := by
  letI : (CoefficientRealization.pairs P X₀ R).CommShift ℤ := by
    dsimp only [CoefficientRealization.pairs]
    infer_instance
  let U := constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
    P.coefficients.different X₀ P.coefficients.Qbar
  let C₀ := WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left
  let K := (WeilSheaf.toComplex.obj C₀)⟦2 * (d : ℤ)⟧
  let e := ((CoefficientRealization.pairs P X₀ R).commShiftIso (2 * (d : ℤ))).app U ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso R.unit.some.symm ≪≫
      (native_shift P X₀ (WeilSheaf.toComplex.obj C₀) (2 * (d : ℤ))).symm
  let h := (NativePairCohomology.native_homology P.field.k₀ P.coefficients.l
    X₀.left K (-2 * (d : ℤ))).some
  exact (NativePairCohomology.homology P.field.k₀ P.coefficients.l X₀.left
    (-2 * (d : ℤ))).mapIso e ≪≫ h.symm ≪≫
      (WeilSheaf.objectProperty P.field.k₀ P.coefficients.l X₀.left).ι.mapIso
        (WeilComplex.homologySheafShiftToComplexIso C₀ (2 * (d : ℤ))
          (-2 * (d : ℤ)) (by omega))

omit [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)] in
private theorem native_nsmul_injective
    (M N : CoefficientRealization.Native P X₀) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun f : M ⟶ N ↦ n • f) := by
  have : CharZero (ULift.{u + 1} (PadicAlgCl P.coefficients.l)) :=
    (ULift.ringEquiv.toRingHom).charZero
  intro f g h
  apply Mod.hom_ext
  have he : n • f.hom = n • g.hom := congrArg (fun k : M ⟶ N ↦ k.hom) h
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (PadicAlgCl P.coefficients.l)),
    ← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (PadicAlgCl P.coefficients.l))] at he
  exact (smul_right_inj (Nat.cast_ne_zero.mpr hn)).mp he

omit [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom] in
private theorem native_twist_scalar
    (U : ProEtaleWeilSheaf P.field.k₀ P.coefficients.l X₀.left) (d : ℕ) :
    let c := WeilSheaf.cyclotomicUnit P.field.k₀ P.coefficients.l ^ (d : ℤ)
    (Nat.card P.field.k₀ ^ d) •
      ((ProEtaleWeilSheaf.constantTwist P.field.k₀ P.coefficients.l X₀.left c).obj U).str.hom =
        U.str.hom := by
  have : CharZero (ULift.{u + 1} (PadicAlgCl P.coefficients.l)) :=
    (ULift.ringEquiv.toRingHom).charZero
  dsimp only
  rw [IsoAlgebra.str_hom, ProEtaleWeilSheaf.constantTwist_obj_obj_str,
    ← Preadditive.nsmul_comp]
  have hc : (Nat.card P.field.k₀ ^ d : PadicAlgCl P.coefficients.l) *
      ((WeilSheaf.cyclotomicUnit P.field.k₀ P.coefficients.l ^ (d : ℤ) :
        (PadicAlgCl P.coefficients.l)ˣ) : PadicAlgCl P.coefficients.l) = 1 := by
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast,
      WeilSheaf.cyclotomicUnit_eq, inv_pow, mul_inv_cancel₀]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hs (M : CoefficientRealization.Native P X₀) :
      (Nat.card P.field.k₀ ^ d) • ProEtale.AdicSheaf.smul
        (ULift.up ((WeilSheaf.cyclotomicUnit P.field.k₀ P.coefficients.l ^ (d : ℤ) :
          (PadicAlgCl P.coefficients.l)ˣ) : PadicAlgCl P.coefficients.l)) M = 𝟙 M := by
    apply Mod.hom_ext
    change (Nat.card P.field.k₀ ^ d) • (_ • 𝟙 M.X) = 𝟙 M.X
    rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (PadicAlgCl P.coefficients.l)),
      smul_smul]
    have hc' : (Nat.card P.field.k₀ ^ d : ULift.{u + 1} (PadicAlgCl P.coefficients.l)) *
        ULift.up ((WeilSheaf.cyclotomicUnit P.field.k₀ P.coefficients.l ^ (d : ℤ) :
          (PadicAlgCl P.coefficients.l)ˣ) : PadicAlgCl P.coefficients.l) = 1 :=
      congrArg ULift.up hc
    rw [Nat.cast_pow, hc', one_smul]
  rw [hs, Category.id_comp]
  rfl

/-- Any additive, shift-compatible equivariant ordinary realization normalized
on the scalar unit has the specified Tate endpoint.

Source: cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md,
constant-unit identification; the canonical root-line convention of
lem-pur-constant-purity-frobenius-square. No smooth purity is used here.
(blueprint: lem-sf-realized-tate-cohomology)

Proof: trivialize the geometric Tate line by a compatible system of roots of
unity in the algebraically closed geometric field. On its d-th tensor power
the geometric Frobenius map is multiplication by q^(-d), where q is the finite
base field's cardinality. Apply the pullback-unit and tensor-unit comparisons
in canonicalSourceTheta. They identify the unshifted source with the scalar
unit carrying this scalar Frobenius action; this calculation is independent of
the choice of roots since a different basis conjugates a scalar action.

An additive functor preserves multiplication by q^d and the inverse of that
invertible endomorphism. It therefore preserves multiplication by q^(-d);
no extra choice of a scalar-linear structure is required. Naturality of its
Frobenius comparison and Data.unit identify the realized pair with the native
constant pair with the same scalar action, namely the native d-th Tate sheaf
tensor the native constant. Data.shift and Data.frobeniusShift transport the
even shift by 2d, including its action. Degree -2d cohomology of this shifted
degree-zero sheaf is the original sheaf by the single-functor homology
isomorphism. Compose these identifications to obtain the stated pair
isomorphism. For d=0 all comparisons are the specified unit maps; on the empty
scheme the same maps are the unique isomorphisms between zero objects. -/
theorem realized_tate_cohomology (R : CoefficientRealization.Data P X₀) (d : ℕ) :
    Nonempty
      ((CoefficientRealization.pairCohomology P X₀ R (-2 * (d : ℤ))).obj
          (twistedConstant P X₀ d) ≅
        ((WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
          (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
          (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d)).obj) := by
  let U := constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
    P.coefficients.different X₀ P.coefficients.Qbar
  obtain ⟨a, ha, ⟨e⟩⟩ := coefficient_tate_scalar_presentation P X₀ d
  let B := IsoAlgebra.mk U.carrier (U.str ≪≫ a)
  let F := sourceFrobenius P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀
  let S := IsoAlgebra.mapOfNatIso (F.commShiftIso (2 * (d : ℤ)))
  let K := S.obj B
  let Uₛ := S.obj U
  let A := CoefficientRealization.pairs P X₀ R
  let H := NativePairCohomology.homology P.field.k₀ P.coefficients.l X₀.left
    (-2 * (d : ℤ))
  let n := Nat.card P.field.k₀ ^ d
  have hb : n • (B.str.hom ≫ (Iso.refl U.carrier).hom) =
      F.map (Iso.refl U.carrier).hom ≫ U.str.hom := by
    change n • ((U.str.hom ≫ a.hom) ≫ 𝟙 _) = F.map (𝟙 _) ≫ U.str.hom
    rw [Category.comp_id, F.map_id, Category.id_comp, ← Preadditive.comp_nsmul,
      ha, Category.comp_id]
  have h₀ := map_scaled_square (F.commShiftIso (2 * (d : ℤ))) B U
    (Iso.refl U.carrier) n hb
  let aₛ := (shiftFunctor _ (2 * (d : ℤ))).mapIso (Iso.refl U.carrier)
  have h₁ := map_scaled_square R.frobenius K Uₛ aₛ n h₀
  have h₂ := map_scaled_square
    ((WeilSheaf.frobeniusPullback
      P.field.k₀ P.coefficients.l X₀.left).mapDerivedCategoryHomologyFunctorIso (-2 * (d : ℤ)))
    (A.obj K) (A.obj Uₛ) (R.functor.mapIso aₛ) n h₁
  let b := H.mapIso (A.mapIso (shift_transport_iso U (2 * (d : ℤ))).symm) ≪≫
    realized_shifted_unit P X₀ R d
  have h₃ := scaled_square_comp (H.obj (A.obj K)) (H.obj (A.obj Uₛ))
    (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left).obj
    ((DerivedCategory.homologyFunctor (CoefficientRealization.Native P X₀)
      (-2 * (d : ℤ))).mapIso (R.functor.mapIso aₛ)) b n h₂
  let V := (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left).obj
  let c := WeilSheaf.cyclotomicUnit P.field.k₀ P.coefficients.l ^ (d : ℤ)
  let W := (ProEtaleWeilSheaf.constantTwist P.field.k₀ P.coefficients.l X₀.left c).obj V
  let j := (DerivedCategory.homologyFunctor (CoefficientRealization.Native P X₀)
      (-2 * (d : ℤ))).mapIso (R.functor.mapIso aₛ) ≪≫
    (IsoAlgebra.forget _).mapIso b
  have hj : n • ((H.obj (A.obj K)).str.hom ≫ j.hom) =
      (WeilSheaf.frobeniusPullback P.field.k₀ P.coefficients.l X₀.left).map j.hom ≫
        V.str.hom := h₃
  let w : H.obj (A.obj K) ≅ W := IsoAlgebra.isoMk j (by
    apply native_nsmul_injective P X₀ _ _ n (pow_ne_zero _ Nat.card_pos.ne')
    change n • ((WeilSheaf.frobeniusPullback P.field.k₀ P.coefficients.l X₀.left).map
        j.hom ≫ W.str.hom) = n • ((H.obj (A.obj K)).str.hom ≫ j.hom)
    rw [← Preadditive.comp_nsmul]
    change (WeilSheaf.frobeniusPullback P.field.k₀ P.coefficients.l X₀.left).map
        j.hom ≫ ((Nat.card P.field.k₀ ^ d) •
          ((ProEtaleWeilSheaf.constantTwist P.field.k₀ P.coefficients.l X₀.left
            (WeilSheaf.cyclotomicUnit P.field.k₀ P.coefficients.l ^ (d : ℤ))).obj V).str.hom) = _
    rw [native_twist_scalar P X₀ V d]
    exact hj.symm)
  let C₀ := WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left
  let T := WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d
  let t := WeilSheaf.tensorObjObjIsoOfIso T C₀
    (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d)
    (WeilSheaf.tateTwistSheafObjIso P.field.k₀ P.coefficients.l X₀.left d)
    (ProEtaleWeilSheaf.constantTwistOneObjIso C₀.obj).symm ≪≫
      ProEtaleWeilSheaf.constantTwistCongrIso (mul_one c) V
  exact ⟨(CoefficientRealization.pairCohomology P X₀ R (-2 * (d : ℤ))).mapIso
      (e ≪≫ shift_transport_iso B (2 * (d : ℤ))) ≪≫
    w ≪≫ t.symm⟩

end WeilConjectures.NativeCoefficientCohomology
