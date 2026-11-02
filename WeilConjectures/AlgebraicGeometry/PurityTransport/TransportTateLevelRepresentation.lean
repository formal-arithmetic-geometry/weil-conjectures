/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement

/-! # Representability of one free integral root level

Source: the Roots of unity and Integral twist paragraphs of the current blueprint
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`.
(blueprint: lem-pur-transport-tate-level-representation).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

-- The finite root scheme argument is the one used in the library's
-- NativeIntegralTateFiniteRepresentation, specialized to the root sheaf alone.
private theorem roots_representation (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hunit : IsUnit (N : Γ(Y, ⊤))) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
          (Scheme.proEtaleRootsOfUnitySheaf Y N)) := by
  classical
  let R := Γ(Y, ⊤)
  let P := affineRootsOver R N
  have hmonic : ((Polynomial.X : Polynomial R) ^ N - 1).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hN.ne'
  have : IsFinite P.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hmonic.finite_adjoinRoot
  have : Etale P.hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    apply RingHom.etale_algebraMap.mpr
    simpa only [Polynomial.C_1] using
      AdjoinRoot.etale_X_pow_sub_C hN.ne' hunit (isUnit_one : IsUnit (1 : R))
  let W := (Over.pullback Y.toSpecΓ).obj P
  let : IsFinite W.hom := inferInstanceAs (IsFinite (pullback.snd P.hom Y.toSpecΓ))
  let : Etale W.hom := inferInstanceAs (Etale (pullback.snd P.hom Y.toSpecΓ))
  let V : Y.ProEt := Scheme.ProEt.mk W.hom
  obtain ⟨_, _, _, _, _, _, _, hbase⟩ := affineRoots_representability R N hN
  obtain ⟨e, _, hnat, _⟩ := hbase Y Y.toSpecΓ
  let a (U : Y.ProEtᵒᵖ) :
      (U.unop ⟶ V) ≃ ((Scheme.ProEt.forget Y).obj U.unop ⟶ W) :=
    { toFun := fun f ↦ Over.homMk f.left f.w
      invFun := fun f ↦ MorphismProperty.Over.homMk f.left f.w
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let b (U : Y.ProEtᵒᵖ) :
      {z : Γ(U.unop.left, ⊤)ˣ // z ^ N = 1} ≃
        Additive (rootsOfUnity N Γ(U.unop.left, ⊤)) :=
    { toFun := fun z ↦ Additive.ofMul ⟨z.val, (mem_rootsOfUnity N _).mpr z.property⟩
      invFun := fun z ↦ ⟨z.toMul.val, (mem_rootsOfUnity N _).mp z.toMul.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let k (U : Y.ProEtᵒᵖ) :
      ULift.{u + 1} (U.unop ⟶ V) ≃
        (Scheme.proEtaleRootsOfUnitySheaf Y N).obj.obj U :=
    Equiv.ulift.trans ((a U).trans ((e _).trans
      ((b U).trans (Scheme.proEtaleRootsOfUnitySections Y N U).toEquiv.symm)))
  let j : ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V).obj ≅
      ((sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
        (Scheme.proEtaleRootsOfUnitySheaf Y N)).obj :=
    NatIso.ofComponents (fun U ↦ (k U).toIso) (by
      intro U U' f
      ext x
      apply (Scheme.proEtaleRootsOfUnitySections Y N U').injective
      apply Additive.toMul.injective
      apply Subtype.ext
      have hi := NatTrans.naturality_apply
        (Scheme.proEtaleRootsOfUnityInclusion Y N).hom f (k U x)
      have hu := (Scheme.existsUnique_proEtaleRootsOfUnitySections Y N U).exists.choose_spec
        (k U x)
      have hv := (Scheme.existsUnique_proEtaleRootsOfUnitySections Y N U').exists.choose_spec
        ((Scheme.proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))
      have hk (T : Y.ProEtᵒᵖ) (z : ULift.{u + 1} (T.unop ⟶ V)) :
          (Scheme.proEtaleRootsOfUnitySections Y N T (k T z)).toMul.val =
            (e _ (a T z.down)).val := by
        dsimp [k, b]
        exact congrArg (fun z ↦ z.toMul.val)
          ((Scheme.proEtaleRootsOfUnitySections Y N T).apply_symm_apply _)
      have hr : (Scheme.proEtaleRootsOfUnitySections Y N U'
          ((Scheme.proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))).toMul.val =
          Units.map f.unop.left.appTop.hom.toMonoidHom
            (Scheme.proEtaleRootsOfUnitySections Y N U (k U x)).toMul.val := by
        rw [← hu, ← hv] at hi
        exact congrArg (fun z ↦ z.down.toMul) hi
      change (Scheme.proEtaleRootsOfUnitySections Y N U'
          (k U' ⟨f.unop ≫ x.down⟩)).toMul.val =
        (Scheme.proEtaleRootsOfUnitySections Y N U'
          ((Scheme.proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))).toMul.val
      exact (hk U' _).trans ((hnat _ _ ((Scheme.ProEt.forget Y).map f.unop)
        (a U x.down)).trans ((congrArg
          (Units.map f.unop.left.appTop.hom.toMonoidHom) (hk U x).symm).trans hr.symm)))
  exact ⟨V, ‹IsFinite W.hom›, ‹Etale W.hom›,
    ⟨(sheafToPresheaf _ _).preimageIso j⟩⟩

-- The section equivalence identifies the old presheaf with the kernel sheaf's
-- underlying presheaf; sheafification then gives the comparison.
private noncomputable def rootsComparison (X : Scheme.{u}) (N : ℕ) :
    rootsOfUnitySheaf X N ≅ proEtaleRootsOfUnitySheaf X N := by
  let F := proEtaleRootsOfUnitySheaf X N
  let P := rootsOfUnityPresheaf X N
  let J := ProEt.topology X
  have hs (U : X.ProEtᵒᵖ) (x : F.obj.obj U) :
      ULift.up (Additive.ofMul (proEtaleRootsOfUnitySections X N U x).toMul.val) =
        (proEtaleRootsOfUnityInclusion X N).hom.app U x :=
    (existsUnique_proEtaleRootsOfUnitySections X N U).exists.choose_spec x
  let i : F.obj ≅ P := NatIso.ofComponents
    (fun U ↦ ((proEtaleRootsOfUnitySections X N U).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) (by
      intro U V a
      ext x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      have h := congrArg (fun b ↦ b x)
        ((proEtaleRootsOfUnityInclusion X N).hom.naturality a)
      change (proEtaleRootsOfUnityInclusion X N).hom.app V (F.obj.map a x) =
        (proEtaleUnitsSheaf X).obj.map a
          ((proEtaleRootsOfUnityInclusion X N).hom.app U x) at h
      rw [← hs V _, ← hs U x] at h
      exact congrArg (fun y ↦ y.down.toMul) h)
  let e : rootsOfUnitySheaf X N ≅ F :=
    (presheafToSheaf J Ab.{u + 1}).mapIso i.symm ≪≫ (sheafificationIso F).symm
  exact e

-- Tensor the presentation Z --N--> Z --> Z/N with an N-torsion sheaf.
-- After applying the constant-sheaf unit comparison, its first map is zero.
private noncomputable def residueTensor (Y : Scheme.{u}) (N : ℕ)
    (M : Sheaf (ProEt.topology Y) Ab.{u + 1}) (hM : N • 𝟙 M = 0) :
    (constantSheaf (ProEt.topology Y) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ⊗ M ≅ M := by
  let F := constantSheaf (ProEt.topology Y) Ab.{u + 1} ⋙ tensorRight M
  let e : F.obj (𝟙_ Ab.{u + 1}) ≅ M :=
    (tensorRight M).mapIso
      (Functor.Monoidal.εIso (constantSheaf (ProEt.topology Y) Ab.{u + 1})).symm ≪≫ λ_ M
  let c := CokernelCofork.ofπ (AddCommGrpCat.intResidue.{u} N)
    (AddCommGrpCat.intResidue_condition N)
  exact CokernelCofork.mapIsoOfIsColimit
    (c.mapIsColimit (AddCommGrpCat.intResidueCokernel N) F)
    (CokernelCofork.IsColimit.ofId (0 : M ⟶ M) rfl)
    (Arrow.isoMk e e (by
      change e.hom ≫ 0 = F.map (N • 𝟙 _) ≫ e.hom
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
        Category.id_comp, comp_zero]
      have h := congrArg (fun f : M ⟶ M ↦ e.hom ≫ f) hM
      simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero] using h.symm))

-- Absorb the constant residue sheaf on both sides of the integral tensor.
private noncomputable def integralTensorRoots (Y : Scheme.{u}) (ell n : ℕ)
    [Fact ell.Prime] :
    (tateModuleLevel Y ell n).X ≅ proEtaleRootsOfUnitySheaf Y (ell ^ n) := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) Y
  let C := (constantSheaf (ProEt.topology Y) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ell ^ n))))
  let M := proEtaleRootsOfUnitySheaf Y (ell ^ n)
  have hM : (ell ^ n) • 𝟙 M = 0 := by
    ext U x
    exact proEtaleRootsOfUnity_nsmul Y (ell ^ n) U x
  have : NeZero (ell ^ n) := ⟨pow_ne_zero _ (Fact.out : ell.Prime).ne_zero⟩
  let hR := Profinite.finiteDiscreteCondensedRing_constant.{u} (ZMod (ell ^ n))
  let eR := hR.choose
  let eY := (finiteDiscreteSchemeRing_constant (ZMod (ell ^ n)) Y eR hR.choose_spec).choose
  let ec : R ⊗ C ≅ C :=
    (Mod.forget R).mapIso (freeConstantResidueIso Y ell n) ≪≫
      (asIso (chartComparison Y (ZMod (ell ^ n)))).symm ≪≫ eY.symm
  let em := residueTensor Y (ell ^ n) M hM
  exact (tensorLeft R).mapIso (rootsComparison Y (ell ^ n)) ≪≫
    (tensorLeft R).mapIso em.symm ≪≫ (α_ R C M).symm ≪≫
    (tensorRight M).mapIso ec ≪≫ em

/-- The underlying set sheaf of a single finite integral Tate level is finite etale.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Roots of unity and Integral twist.
(blueprint: lem-pur-transport-tate-level-representation).

Proof: the integral level is R_Y tensor mu_(ell^n), with R_Y the pulled-back
condensed Z_ell ring. Write N = ell^n. The roots sheaf presented by
sheafification is the kernel roots sheaf, sectionwise, and the latter is killed
by N. Tensoring the cokernel Z --N--> Z --> Z/N with an N-torsion sheaf M after
constant sheafification shows (Z/N)_Y tensor M = M. The proved free constant
residue comparison, the coefficient chart comparison and the finite discrete
constant ring comparison identify R_Y tensor (Z/N)_Y with (Z/N)_Y; associativity
then gives R_Y tensor mu_N = (Z/N)_Y tensor mu_N = mu_N. The root functor is
represented by Spec(O_Y[t]/(t^N-1)), the base change to Y of the spectrum over
Gamma(Y,O_Y) (affine roots representability); the representing equivalence
sends a map to the pullback of t. Since ell is invertible in every residue
field it is a unit in Gamma(Y,O_Y). The polynomial is monic, so the morphism is
finite, and it is etale because N and 1 are units. These section equivalences
give the displayed lifted-Yoneda isomorphism. At n=0, N=1 and the scheme is Y
itself; the empty base is included. No choice of a comparison at another level is asserted. -/
theorem tateLevelRepresentation (Y : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (n : ℕ) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (ProEt.topology Y) (forget Ab.{u + 1})).obj
          (tateModuleLevel Y ell n).X) := by
  have hp : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos n
  have hu : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
    rw [Nat.cast_pow]
    exact (globalPrimeUnit Y ell).pow n
  obtain ⟨V, hfin, het, ⟨e⟩⟩ := roots_representation Y (ell ^ n) hp hu
  exact ⟨V, hfin, het, ⟨e ≪≫
    (sheafCompose (ProEt.topology Y) (forget Ab.{u + 1})).mapIso
      (integralTensorRoots Y ell n).symm⟩⟩

end AlgebraicGeometry.ProEtale.PurityTransport
