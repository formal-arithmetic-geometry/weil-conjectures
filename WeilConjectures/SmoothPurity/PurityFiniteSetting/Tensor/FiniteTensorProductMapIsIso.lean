/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorProductFrameExt

import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Normalized ordinary finite signed product maps

Source: finite-reduction proof Step 2; Stacks Project, Modules on Sites,
Sections 03EK and 04TT.
(blueprint: lem-pur-finite-tensor-product-map-isIso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open AlgebraicGeometry.Scheme
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj' ModuleCat.RestrictScalars.map'
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  SheafOfModules.forget AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf
  sfIntrinsicRealizationUnit
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

open Opposite
open scoped TensorProduct

/-- Scalar realization identifies ordinary tensors with the explicit intrinsic tensor,
with the comparison fixed by the sheafification units on pure sections. -/
private theorem realization_tensor_iso (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ∃ q : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        ((sfIntrinsicModuleEquivalence T A).functor.obj N)).obj
          ((sfIntrinsicModuleEquivalence T A).functor.obj M) ≅
        (sfIntrinsicModuleEquivalence T A).functor.obj (M ⊗ N),
      ∀ (U : T.ProEtᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U),
        q.hom.val.app U
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ U
            (sfIntrinsicRealizationUnit T A M U x)
            (sfIntrinsicRealizationUnit T A N U y)) =
          sfIntrinsicRealizationUnit T A (M ⊗ N) U
            ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
              (ModuleCat.{u + 1} (ULift.{u + 1} A))) M N).app U (x ⊗ₜ y)) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let J := ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let E := ProEtale.finiteCoefficientModulePresheaf.{u, u, u + 1} T.ProEt (ULift.{u + 1} A)
  let S := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let U := sheafToPresheaf J B
  let L := presheafToSheaf J B
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let hW : (J.W.inverseImage (PresheafOfModules.toPresheaf.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T A)).obj)).IsMonoidal :=
    SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1}
      (proEtaleConstantRing T A)
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing T A)
  let := finiteScalarPresheafMonoidal T A
  let t : E ⋙ S ⟶ L ⋙ F :=
    Functor.whiskerRight (sheafificationAdjunction J B).unit (E ⋙ S)
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact finiteScalarModuleSheafificationUnit_isIso T A P
  let mu := Functor.LaxMonoidal.μ U M N
  have hmu : IsIso (L.map mu) := by
    have h := (sheafificationAdjunction J B).map_μ_comp_counit_app_tensor M N
    have : IsIso (L.map mu ≫ (sheafificationAdjunction J B).counit.app (M ⊗ N)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right (L.map mu)
      ((sheafificationAdjunction J B).counit.app (M ⊗ N))
  let a := S.map (E.map mu)
  have ha : IsIso a := by
    have hn := t.naturality mu
    have heq : a = t.app (U.obj M ⊗ U.obj N) ≫ F.map (L.map mu) ≫
        inv (t.app (U.obj (M ⊗ N))) := by
      apply (cancel_mono (t.app (U.obj (M ⊗ N)))).mp
      simpa only [Functor.comp_obj, Functor.comp_map, a, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id] using hn
    rw [heq]
    infer_instance
  obtain ⟨e, he⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (R := proEtaleConstantRing T A)
    (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let R := proEtaleConstantRing T A
  let Rm : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let M' := (sfIntrinsicModuleEquivalence T A).functor.obj M
  let N' := (sfIntrinsicModuleEquivalence T A).functor.obj N
  let S0 := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (𝟙 Rm.obj)
  let b := S0.mapIso ((SheafOfModules.siteTensorRightIso.{u + 1, u, u + 1} R N'.val).app M'.val) ≪≫
    (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M' N').symm
  let q := b ≪≫ e.app (E.obj M.obj, E.obj N.obj) ≪≫ asIso a
  refine ⟨q, ?_⟩
  intro V x y
  have hn := congrArg (fun k ↦ k.app V (x ⊗ₜ y))
    (adj.unit.naturality (E.map mu))
  have ht := he (E.obj M.obj) (E.obj N.obj) V x y
  have ht' := congrArg (fun z ↦ (e.hom.app (E.obj M.obj, E.obj N.obj)).val.app V z) ht
  simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.inv_hom_id_app, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at ht'
  have hb (z : M'.val.obj V) (w : N'.val.obj V) :
      b.hom.val.app V (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M' N' V z w) =
        (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M' N').inv.val.app V
          (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
            (𝟙 Rm.obj)).unit.app
            (M'.val ⊗ N'.val)).app V (z ⊗ₜ[R.obj.obj V] w)) := by
    apply congrArg
      ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
        (R := R) M' N').inv.val.app V)
    exact congrArg (fun k ↦ k.app V (z ⊗ₜ[R.obj.obj V] w))
      ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
        (𝟙 Rm.obj)).unit.naturality
        ((SheafOfModules.siteTensorRightIso.{u + 1, u, u + 1} R N'.val).hom.app M'.val)).symm
  change a.val.app V ((e.hom.app (E.obj M.obj, E.obj N.obj)).val.app V
    (b.hom.val.app V (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M' N' V _ _))) = _
  rw [hb]
  erw [← ht']
  exact hn.symm

/-- A normalized ordinary signed product morphism is locally a basis isomorphism.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, invertible twists;
Stacks Project, sites-modules.tex, Section invertible and Lemma constructions-invertible.
(blueprint: lem-pur-finite-tensor-product-map-isIso).
Proof: on a cover trivializing the first line, take its ordered-power and dual
frames. Realization identifies their ordinary representatives with the same
intrinsic sections. The tensor comparison identifies the product of the two
frame vectors with the basis of the tensor line. The hypothesis says that f
sends this basis to the basis of the sum-degree line. In these charts f is the
identity of the coefficient unit, hence invertible. The inverses agree on overlaps
because they are inverses of the same morphism, so they glue to a two-sided inverse.
The equivalence with fixed-scalar sheaves reflects this isomorphism. This works
for arbitrary signs, including zero and opposite signs, because the negative
frames are evaluation-dual bases. No uniqueness of product morphisms or preexisting
signed product is used. Empty charts and the zero ring have the unique inverse. -/
theorem finiteTensorSheafProductMap_isIso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ)
    (f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T (r + t))
    (hf : ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T (r + t) V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
          e.basis (r + t) 0) :
    IsIso f := by
  classical
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let J := ProEt.topology T
  let R := proEtaleConstantRing T P.Ring
  let Rm : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let L := P.finiteTensorFirstLine T
  let e := sfIntrinsicModuleEquivalence T P.Ring
  let M := e.functor.obj (P.finiteTensorFixedSheaf T r)
  let N := e.functor.obj (P.finiteTensorFixedSheaf T t)
  let c (m : ℤ) := e.counitIso.app (P.finiteTensorLine T m)
  obtain ⟨q, hq⟩ := realization_tensor_iso T P.Ring
    (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)
  let g := q.hom ≫ e.functor.map f ≫ (c (r + t)).hom
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (T.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (T.presheaf.stalk x))).invertible
  have transport_rank (n m : ℕ) (h : n = m)
      (K : proEtaleRingModules T (proEtaleConstantRing T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension n)))
      (hK : K.IsFiniteLocallyFreeOfRank 1) :
      (Eq.mp (congrArg (fun k : ℕ ↦ proEtaleRingModules T (proEtaleConstantRing T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension k))) h) K
        ).IsFiniteLocallyFreeOfRank 1 := by
    subst m
    exact hK
  have hfirst : L.IsFiniteLocallyFreeOfRank 1 :=
    transport_rank _ _ (Nat.sub_add_cancel P.level_pos) _
      (coefficientTwistFiniteRank P.coefficients.l P.extension T (P.level - 1))
  obtain ⟨I, X, hX, hcharts⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp hfirst
  choose E hE using fun i ↦ SheafOfModules.signedBasis_on_chart.{u + 1, u, u + 1}
    L (X i) ((hcharts i).some ≪≫ SheafOfModules.freeUniqueIso (ULift (Fin 1)))
  have hb (V : T.ProEt) (i : I) (k : V ⟶ X i) :
      Function.Bijective (g.val.app (op V)) := by
    let F := fun m : ℤ ↦ (SheafOfModules.signedLinePower.{u + 1, u, u + 1} L m).val.map
      k.op (E i m)
    have hF := SheafOfModules.signedBasis_restrict.{u + 1, u, u + 1}
      L (op (X i)) (op V) k.op (E i) (hE i)
    let b (m : ℤ) : Module.Basis (Fin 1) (R.obj.obj (op V))
        ((P.finiteTensorLine T m).val.obj (op V)) :=
      (Module.Basis.singleton (Fin 1) (R.obj.obj (op V))).map
        (LinearEquiv.ofBijective
          { toFun := fun a ↦ a • F m
            map_add' := fun a b ↦ add_smul a b _
            map_smul' := fun a b ↦ mul_smul a b _ }
          (SheafOfModules.signedBasis_bijective.{u + 1, u, u + 1} L (op V) F hF m))
    have hbase (m : ℤ) : b m 0 = F m := by
      simp only [b, Module.Basis.map_apply, Module.Basis.singleton_apply]
      change (1 : R.obj.obj (op V)) • F m = F m
      exact one_smul _ _
    let frame : P.FiniteTensorFrame T V :=
      { basis := b
        zero := (hbase 0).trans hF.2.1
        positive := by
          intro j
          erw [hbase, hbase, hbase]
          exact hF.2.2.1 j
        negative := by
          intro j
          erw [hbase, hbase]
          have h := hF.2.2.2 j (op (Over.mk (𝟙 V)))
          simp only [Over.mk_hom] at h
          erw [SheafOfModules.signed_map_id.{u + 1, u, u + 1}] at h
          exact h }
    let z (m : ℤ) := (c m).inv.val.app (op V) (F m)
    have hz (m : ℤ) (W : (Over V)ᵒᵖ) : Function.Bijective
        (fun a : R.obj.obj (op W.unop.left) ↦
          a • (e.functor.obj (P.finiteTensorFixedSheaf T m)).val.map W.unop.hom.op (z m)) := by
      have hn := PresheafOfModules.naturality_apply (c m).inv.val W.unop.hom.op (F m)
      have heq : (fun a : R.obj.obj (op W.unop.left) ↦
          a • (e.functor.obj (P.finiteTensorFixedSheaf T m)).val.map W.unop.hom.op (z m)) =
          (fun a ↦ (c m).inv.val.app (op W.unop.left)
            (a • (P.finiteTensorLine T m).val.map W.unop.hom.op (F m))) := by
        funext a
        rw [map_smul]
        exact congrArg (fun x ↦ a • x) hn.symm
      rw [heq]
      exact (((SheafOfModules.evaluation Rm (op W.unop.left)).mapIso (c m).symm
        ).toLinearEquiv.bijective).comp (hF.1 m W)
    have htensor := SheafOfModules.tensorBasis_bijective.{u + 1, u, u + 1}
      M N (op V) (z r) (z t) (hz r) (hz t) (op (Over.mk (𝟙 V)))
    simp only [Over.mk_hom] at htensor
    erw [SheafOfModules.signed_map_id.{u + 1, u, u + 1}] at htensor
    obtain ⟨x, hx⟩ := (sfIntrinsicSectionEquiv P.Ring T
      (P.finiteTensorLine T r) (op V)).surjective (F r)
    obtain ⟨y, hy⟩ := (sfIntrinsicSectionEquiv P.Ring T
      (P.finiteTensorLine T t) (op V)).surjective (F t)
    have hx' : sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r)
        (op V) x = z r := by
      apply ((SheafOfModules.evaluation Rm (op V)).mapIso (c r)).toLinearEquiv.injective
      exact hx.trans (congrArg (fun a ↦ a.val.app (op V) (F r)) (c r).inv_hom_id).symm
    have hy' : sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T t)
        (op V) y = z t := by
      apply ((SheafOfModules.evaluation Rm (op V)).mapIso (c t)).toLinearEquiv.injective
      exact hy.trans (congrArg (fun a ↦ a.val.app (op V) (F t)) (c t).inv_hom_id).symm
    have hnorm : g.val.app (op V)
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          M N (op V) (z r) (z t)) = F (r + t) := by
      have h := hf V frame x y (hx.trans (hbase r).symm) (hy.trans (hbase t).symm)
      have hn := sfRealizationSectionEquiv_map P.Ring T f (op V)
        (P.finiteTensorSectionTmul T r t V x y)
      change (c (r + t)).hom.val.app (op V)
        ((e.functor.map f).val.app (op V)
          (q.hom.val.app (op V)
            (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ (op V)
            (z r) (z t)))) = _
      rw [← hx', ← hy', hq]
      erw [← hn]
      exact h.trans (hbase (r + t))
    have hcomp : (fun a : R.obj.obj (op V) ↦
        g.val.app (op V) (a • SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ (op V)
          (z r) (z t))) = (fun a ↦ a • F (r + t)) := by
      funext a
      rw [map_smul]
      exact congrArg (fun x ↦ a • x) hnorm
    apply (Function.Bijective.of_comp_iff _ htensor).mp
    change Function.Bijective (fun a : R.obj.obj (op V) ↦
      g.val.app (op V) (a • SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        _ _ (op V) (z r) (z t)))
    rw [hcomp]
    exact SheafOfModules.signedBasis_bijective.{u + 1, u, u + 1} L (op V) F hF (r + t)
  have hgi : IsIso ((SheafOfModules.toSheaf _).map g) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp
      ⟨Presheaf.isLocallyInjective_of_coversTop hX _ (fun V i k ↦ (hb V i k).1),
        Presheaf.isLocallySurjective_of_coversTop hX _ (fun V i k ↦ (hb V i k).2)⟩
  have : IsIso g := isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have heq : e.functor.map f = q.inv ≫ g ≫ (c (r + t)).inv := by
    simp only [g, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have : IsIso (e.functor.map f) := by
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso f e.functor

end WeilConjectures.PurityFiniteSetting
