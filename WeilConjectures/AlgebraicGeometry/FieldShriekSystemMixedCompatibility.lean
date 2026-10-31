/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemMixed
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemTransitionFormula
import WeilConjectures.SecSmoothPurity.ProEtaleDirectImageScalarCocycle
import WeilConjectures.SecSmoothPurity.ProEtaleOpenScalarCocycle
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Mixed quotient and field-extension compatibility of compact support

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
proof step 8 of lem-sp-field-shriek-system-comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

attribute [local irreducible] HasDerivedCategory.standard scalarExtensionFunctor
  scalarExtensionFunctor_composition SemilinearSections.derivedTransition
  FieldShriekSystem.coefficientMap comparison supportEvaluation
  directImageScalarComparison reductionOpenScalarIso reductionDirectImageComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  reductionDerivedChange completedAdicDerivedChange

private theorem transpose_naturality
    {C A B : Type*} [Category C] [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (F : C ⥤ A) (G : C ⥤ B) (t : F ⟶ G ⋙ R) {K M : C} (v : K ⟶ M) :
    L.map (F.map v) ≫ (adj.homEquiv _ _).symm (t.app M) =
      (adj.homEquiv _ _).symm (t.app K) ≫ G.map v :=
  adj.homEquiv_naturality_right_square _ _ _ _ (t.naturality v)

private def quotientRingDiagram (P : PurityFiniteSetting.{u}) (E : Index P) :
    ℕᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj n := CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l E.val n.unop))
  map {n m} v := CommRingCat.ofHom
    (RingHom.ulift (SpTowerCalculus.quotient P.coefficients.l E.val (leOfHom v.unop)))
  map_id n := by
    ext x
    rcases x with ⟨x⟩
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  map_comp f g := by
    ext x
    rcases x with ⟨x⟩
    refine Quotient.inductionOn' x ?_
    intro x
    rfl

set_option maxHeartbeats 2000000 in
-- Compare the concrete quotient diagrams before descending to module restrictions.
private theorem quotient_coefficientMap (P : PurityFiniteSetting.{u}) (E : Index P)
    (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n) :
    SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T) v =
      proEtaleConstantRingMap (T := T) (SpTowerCalculus.quotient P.coefficients.l E.val v) := by
  let B := SemilinearSections.rings (Scheme.ProEt.topology T)
    (SpTowerShriek.B P.coefficients.l E.val T)
    (SpTowerShriek.tau P.coefficients.l E.val T)
  let C := quotientRingDiagram P E ⋙ constantSheaf (Scheme.ProEt.topology T) CommRingCat
  let a : B ⟶ C := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro i
    simp only [B, SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ]
    change (spCoefficientCommRings P.coefficients.l E.val T).map
      (homOfLE (Nat.le_succ i)).op = _
    delta spCoefficientCommRings
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    rfl)
  change B.map (homOfLE v).op = C.map (homOfLE v).op
  have hn : B.map (homOfLE v).op ≫ 𝟙 _ = 𝟙 _ ≫ C.map (homOfLE v).op :=
    a.naturality (homOfLE v).op
  simpa only [Category.comp_id, Category.id_comp] using hn

private def restrictionCongr
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} {a b : R ⟶ S} (h : a = b) :
    SheafOfModules.restrictScalars.{u + 1} a ≅ SheafOfModules.restrictScalars b :=
  NatIso.ofComponents
    (fun N ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsCongr
          (f := (a.hom.app U).hom) (g := (b.hom.app U).hom)
          (congrArg (fun z ↦ (z.hom.app U).hom) h)).app (N.val.obj U))
        (fun _ _ _ ↦ by subst b; rfl)))
    (fun _ ↦ by subst b; ext U x; rfl)

private def quotientCoordinates (P : PurityFiniteSetting.{u}) (E : Index P)
    (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n) : QuotientRestriction P E T v where
  ordinary := restrictionCongr (C := T.ProEt) (J := Scheme.ProEt.topology T)
    (congrArg (fun a ↦ (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)
      (quotient_coefficientMap P E T v))
  sections := by
    intro N U x
    rfl

private theorem reduction_natural (P : PurityFiniteSetting.{u}) (E : Index P)
    (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n) (q : QuotientRestriction P E T v)
    {K L : SpTowerShriek.D P.coefficients.l E.val T} (z : K ⟶ L) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l E.val v) T).map
        ((SpTowerShriek.Ev P.coefficients.l E.val T n).map z) ≫
      systemReduction P E T v q L =
    systemReduction P E T v q K ≫
      (SpTowerShriek.Ev P.coefficients.l E.val T m).map z := by
  have := Limits.preservesFiniteLimits_of_natIso q.ordinary
  have := Limits.preservesFiniteColimits_of_natIso q.ordinary
  unfold systemReduction
  exact transpose_naturality
    (finiteScalarAdjunction (SpTowerCalculus.quotient P.coefficients.l E.val v) T)
    (SpTowerShriek.Ev P.coefficients.l E.val T n)
    (SpTowerShriek.Ev P.coefficients.l E.val T m)
    ((SemilinearSections.derivedTransition (Scheme.ProEt.topology T)
      (SpTowerShriek.B P.coefficients.l E.val T)
      (SpTowerShriek.tau P.coefficients.l E.val T) v) ≫
        Functor.whiskerLeft (SpTowerShriek.Ev P.coefficients.l E.val T m)
          (Functor.mapDerivedCategoryNatIso q.ordinary).hom) z


private theorem ell_torsion (P : PurityFiniteSetting.{u}) (E : Index P) (n : ℕ) :
    ∃ a : ℕ, ∀ x : SpTowerShriek.R P.coefficients.l E.val n,
      (P.coefficients.l ^ a) • x = 0 := by
  refine ⟨n + 1, fun x ↦ ?_⟩
  have h : ((P.coefficients.l ^ (n + 1) : ℕ) :
      SpTowerShriek.R P.coefficients.l E.val n) = 0 := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (I := spEllIdeal P.coefficients.l E.val)
        (Ideal.subset_span (Set.mem_singleton
          (P.coefficients.l : Padic.coefficientExtensionIntegers P.coefficients.l E.val)))
        (n + 1)))
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
  rw [nsmul_eq_mul, h, zero_mul]

private theorem pasteScalarCocycles
    {XA ZA YA XB ZB YB XC ZC YC : Type*}
    [Category XA] [Category ZA] [Category YA]
    [Category XB] [Category ZB] [Category YB]
    [Category XC] [Category ZC] [Category YC]
    (JA : XA ⥤ ZA) (PA : ZA ⥤ YA) (JB : XB ⥤ ZB) (PB : ZB ⥤ YB)
    (JC : XC ⥤ ZC) (PC : ZC ⥤ YC)
    (SX : XA ⥤ XB) (SZ : ZA ⥤ ZB) (SY : YA ⥤ YB)
    (TX : XB ⥤ XC) (TZ : ZB ⥤ ZC) (TY : YB ⥤ YC)
    (UX : XA ⥤ XC) (UZ : ZA ⥤ ZC) (UY : YA ⥤ YC)
    (αX : SX ⋙ TX ⟶ UX) (αZ : SZ ⋙ TZ ⟶ UZ) (αY : SY ⋙ TY ⟶ UY)
    (eAB : JA ⋙ SZ ⟶ SX ⋙ JB) (eBC : JB ⋙ TZ ⟶ TX ⋙ JC)
    (eAC : JA ⋙ UZ ⟶ UX ⋙ JC)
    (gAB : PA ⋙ SY ⟶ SZ ⋙ PB) (gBC : PB ⋙ TY ⟶ TZ ⋙ PC)
    (gAC : PA ⋙ UY ⟶ UZ ⋙ PC)
    (hp : ∀ N, αY.app (PA.obj N) ≫ gAC.app N =
      TY.map (gAB.app N) ≫ gBC.app (SZ.obj N) ≫ PC.map (αZ.app N))
    (he : ∀ M, αZ.app (JA.obj M) ≫ eAC.app M =
      TZ.map (eAB.app M) ≫ eBC.app (SX.obj M) ≫ JC.map (αX.app M))
    (M : XA) :
    αY.app (PA.obj (JA.obj M)) ≫ (gAC.app (JA.obj M) ≫ PC.map (eAC.app M)) =
      TY.map (gAB.app (JA.obj M) ≫ PB.map (eAB.app M)) ≫
        (gBC.app (JB.obj (SX.obj M)) ≫ PC.map (eBC.app (SX.obj M))) ≫
          PC.map (JC.map (αX.app M)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← PC.map_comp, he, PC.map_comp, PC.map_comp]
  have hn := gBC.naturality (eAB.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

set_option maxHeartbeats 2000000 in
-- Pasting the fixed derived comparisons requires their definitional coordinate aliases.
attribute [local semireducible] scalarExtensionFunctor reductionDirectImageComparison in
-- The two public scalar-extension aliases unfold to the same fixed derived extension.
private theorem ambient_cocycle (P : PurityFiniteSetting.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, ∀ x : A, (P.coefficients.l ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (P.coefficients.l ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (P.coefficients.l ^ n) • x = 0)
    (φ : A →+* B) (ψ : B →+* C) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) (M : proEtaleDerivedCategory X A) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((reductionCompactSupport A j p).obj M) ≫
      (reductionDirectImageComparison (ψ.comp φ) j p).app M =
    (scalarExtensionFunctor ψ Y).map ((reductionDirectImageComparison φ j p).app M) ≫
      (reductionDirectImageComparison ψ j p).app ((scalarExtensionFunctor φ X).obj M) ≫
        (reductionCompactSupport C j p).map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M) := by
  have torsion {R : Type u} [CommRing R]
      (h : ∃ n : ℕ, ∀ x : R, (P.coefficients.l ^ n) • x = 0) :
      ∃ n : ℕ, (P.coefficients.l : R) ^ n = 0 := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn 1⟩
  have hproper := proEtaleDirectImageScalarCocycle P.coefficients.l hA hB hC φ ψ p
  have hopen := proEtaleOpenScalarCocycle P.coefficients.l (Fact.out : P.coefficients.l.Prime)
    (torsion hA) (torsion hB) (torsion hC) φ ψ j
  let J₁ := (sfIntrinsicExtensionByZero j A).mapDerivedCategory
  let J₂ := (sfIntrinsicExtensionByZero j B).mapDerivedCategory
  let J₃ := (sfIntrinsicExtensionByZero j C).mapDerivedCategory
  exact pasteScalarCocycles
    J₁ (directImageConstantPush A p) J₂ (directImageConstantPush B p)
    J₃ (directImageConstantPush C p)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ Z) (scalarExtensionFunctor φ Y)
    (scalarExtensionFunctor ψ X) (scalarExtensionFunctor ψ Z) (scalarExtensionFunctor ψ Y)
    (scalarExtensionFunctor (ψ.comp φ) X) (scalarExtensionFunctor (ψ.comp φ) Z)
    (scalarExtensionFunctor (ψ.comp φ) Y)
    (scalarExtensionFunctor_composition φ ψ X).hom
    (scalarExtensionFunctor_composition φ ψ Z).hom
    (scalarExtensionFunctor_composition φ ψ Y).hom
    (reductionOpenScalarIso φ j).hom (reductionOpenScalarIso ψ j).hom
    (reductionOpenScalarIso (ψ.comp φ) j).hom
    (directImageScalarComparison φ p) (directImageScalarComparison ψ p)
    (directImageScalarComparison (ψ.comp φ) p)
    hproper hopen M


private theorem finite_comparison_congr
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ ψ : A →+* B} (h : φ = ψ) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (M : proEtaleDerivedCategory X A) :
    (reductionDirectImageComparison φ j p).app M ≫
        (reductionCompactSupport B j p).map
          (eqToHom (congrArg (fun a ↦ (scalarExtensionFunctor a X).obj M) h)) =
      eqToHom (congrArg (fun a ↦ (scalarExtensionFunctor a Y).obj
        ((reductionCompactSupport A j p).obj M)) h) ≫
      (reductionDirectImageComparison ψ j p).app M := by
  subst ψ
  simp

private theorem cancel_cocycle
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category D₁] [Category D₂] [Category D₃]
    (H₁ : C₁ ⥤ D₁) (H₂ : C₂ ⥤ D₂) (H₃ : C₃ ⥤ D₃)
    (SX : C₁ ⥤ C₂) (SY : D₁ ⥤ D₂) (TX : C₂ ⥤ C₃) (TY : D₂ ⥤ D₃)
    (UX : C₁ ⥤ C₃) (UY : D₁ ⥤ D₃)
    (ax : SX ⋙ TX ≅ UX) (ay : SY ⋙ TY ≅ UY)
    (b₁ : H₁ ⋙ SY ⟶ SX ⋙ H₂) (b₂ : H₂ ⋙ TY ⟶ TX ⋙ H₃)
    (b₃ : H₁ ⋙ UY ⟶ UX ⋙ H₃)
    (M : C₁) (N : C₃) (r : UX.obj M ⟶ N)
    (hc : ay.hom.app (H₁.obj M) ≫ b₃.app M =
      TY.map (b₁.app M) ≫ b₂.app (SX.obj M) ≫ H₃.map (ax.hom.app M)) :
    ay.inv.app (H₁.obj M) ≫ TY.map (b₁.app M) ≫ b₂.app (SX.obj M) ≫
        H₃.map (ax.hom.app M ≫ r) = b₃.app M ≫ H₃.map r := by
  simp only [Functor.map_comp]
  rw [← Category.assoc (b₂.app _), ← Category.assoc (TY.map _), ← hc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem insert_iso
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {A B K L : C} {Z U W : D}
    (a : Z ⟶ V.obj A) (v : A ⟶ B) (w : B ⟶ K) (e : K ≅ L)
    (r : V.obj K ⟶ U) (s : U ⟶ W) :
    a ≫ V.map (v ≫ w) ≫ r ≫ s =
      a ≫ V.map (v ≫ w ≫ e.hom) ≫ (V.map e.inv ≫ r ≫ s) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← V.map_comp_assoc e.hom e.inv, e.hom_inv_id, V.map_id, Category.id_comp]

private theorem map_suffix
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {A B K L : C} {Z U W T : D}
    (a : Z ⟶ V.obj A) (v : A ⟶ B) (w : B ⟶ K)
    (s : V.obj K ⟶ U) (t : U ⟶ W) (u : W ⟶ T)
    (k : K ⟶ L) (z : V.obj L ⟶ T) (h : s ≫ t ≫ u = V.map k ≫ z) :
    a ≫ V.map (v ≫ w) ≫ s ≫ t ≫ u = a ≫ V.map (v ≫ w ≫ k) ≫ z := by
  simp only [Functor.map_comp, Category.assoc]
  rw [h]

private theorem naturality_with_iso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (H : C ⥤ D) (V : D ⥤ F) (S : C ⥤ E) (G : E ⥤ F)
    (b : H ⋙ V ⟶ S ⋙ G) {K L : C} {Z : E} {W W' : F}
    (r : K ⟶ L) (a : S.obj K ≅ Z) (u : W ⟶ W') (v : W' ⟶ V.obj (H.obj K)) :
    u ≫ v ≫ V.map (H.map r) ≫ b.app L =
      u ≫ v ≫ b.app K ≫ G.map (a.hom ≫ a.inv ≫ S.map r) := by
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Functor.comp_map] using
    congrArg (fun z ↦ u ≫ v ≫ z) (b.naturality r)

private theorem map_comp_congr
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {A B : C} {Z W : D} (a : Z ⟶ V.obj A)
    {x y : A ⟶ B} {r s : V.obj B ⟶ W} (hx : x = y) (hr : r = s) :
    a ≫ V.map x ≫ r = a ≫ V.map y ≫ s := by rw [hx, hr]

private theorem map_factor
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {A B K : C} {Z W : D} (a : Z ⟶ V.obj A) (s : V.obj B ⟶ W)
    {x : A ⟶ B} {v : A ⟶ K} {w : K ⟶ B} (h : x = v ≫ w) :
    a ≫ V.map x ≫ s = a ≫ V.map v ≫ V.map w ≫ s := by
  rw [h, V.map_comp, Category.assoc]

private theorem transport_suffix
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {A B N : C} {X Y : D} (r : B ⟶ N)
    {e : A ⟶ B} {b₁ : X ⟶ H.obj A} {b₂ : Y ⟶ H.obj B} {s : X ⟶ Y}
    (h : b₁ ≫ H.map e = s ≫ b₂) :
    b₁ ≫ H.map (e ≫ r) = s ≫ (b₂ ≫ H.map r) := by
  rw [H.map_comp, ← Category.assoc, h, Category.assoc]

private theorem conjugate_reduction
    {Xn Xm Yn Ym : Type*} [Category Xn] [Category Xm] [Category Yn] [Category Ym]
    (Hn : Xn ⥤ Yn) (Hm : Xm ⥤ Ym) (QX : Xn ⥤ Xm) (QY : Yn ⥤ Ym)
    (b : Hn ⋙ QY ⟶ QX ⋙ Hm)
    {A B : Xn} {K L : Xm} {N : Yn} {M : Ym}
    (en : B ≅ A) (em : K ≅ L) (zn : N ≅ Hn.obj B) (zm : M ≅ Hm.obj K)
    (rY : QY.obj N ⟶ M) (rX : QX.obj B ⟶ K) (s : QX.obj A ⟶ L)
    (hs : QY.map zn.inv ≫ rY ≫ zm.hom = b.app B ≫ Hm.map rX)
    (hx : QX.map en.inv ≫ rX ≫ em.hom = s) :
    QY.map (zn ≪≫ Hn.mapIso en).inv ≫ rY ≫ (zm ≪≫ Hm.mapIso em).hom =
      b.app A ≫ Hm.map s := by
  have hn := b.naturality en.inv
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  slice_lhs 2 4 => rw [hs]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hx]

private theorem evaluated_comparison (P : PurityFiniteSetting.{u}) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (e : EvaluationLaw P D c)
    {E F : Index P} (h : E ≤ F) (n : ℕ)
    (M : SpTowerShriek.D P.coefficients.l E.val X) :
    (comparisonSource P D c e h n M).inv ≫
        (SpTowerShriek.Ev P.coefficients.l F.val Y n).map ((comparison P D h c).app M) ≫
        (comparisonTarget P D c e h n M).hom =
      (reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g).app
        ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M) := by
  apply (cancel_epi (comparisonSource P D c e h n M).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  simpa only [comparisonSource, comparisonTarget, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc] using e.evaluation E F h n M

private theorem coefficient_square (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F : Index P) (h : E ≤ F) (m n : ℕ) (v : m ≤ n) :
    (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n) =
      ((D.coefficients E F h).quotient m).comp
        (SpTowerCalculus.quotient P.coefficients.l E.val v) := by
  apply RingHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro x
  change (SpTowerCalculus.quotient P.coefficients.l F.val v)
      (((D.coefficients E F h).quotient n) (Ideal.Quotient.mk _ x)) =
    ((D.coefficients E F h).quotient m)
      ((SpTowerCalculus.quotient P.coefficients.l E.val v) (Ideal.Quotient.mk _ x))
  simp only [Coefficients.quotient_mk, SpTowerCalculus.quotient, Ideal.Quotient.factor_mk]

set_option maxHeartbeats 2000000 in
-- These equations elaborate the fixed unbounded derived functors in several coordinates.
private theorem target_reduction (P : PurityFiniteSetting.{u}) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (e : EvaluationLaw P D c)
    {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (qE : QuotientRestriction P E X v) (qF : QuotientRestriction P F X v)
    (qY : QuotientRestriction P F Y v)
    (hc : (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n) =
      ((D.coefficients E F h).quotient m).comp
        (SpTowerCalculus.quotient P.coefficients.l E.val v))
    (M : SpTowerShriek.D P.coefficients.l E.val X) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) Y).map
        ((comparisonTarget P D c e h n M).inv) ≫
      systemReduction P F Y v qY
        ((SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).obj
          ((D.scalars E F h X).T.obj M)) ≫
      (comparisonTarget P D c e h m M).hom =
    (reductionDirectImageComparison (SpTowerCalculus.quotient P.coefficients.l F.val v)
        c.i c.g).app
        ((scalarExtensionFunctor ((D.coefficients E F h).quotient n) X).obj
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)) ≫
      (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val m) c.i c.g).map
        ((scalarExtensionFunctor_composition ((D.coefficients E F h).quotient n)
            (SpTowerCalculus.quotient P.coefficients.l F.val v) X).hom.app
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M) ≫
        eqToHom (congrArg (fun a ↦ (scalarExtensionFunctor a X).obj
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)) hc) ≫
        (scalarExtensionFunctor_composition (SpTowerCalculus.quotient P.coefficients.l E.val v)
            ((D.coefficients E F h).quotient m) X).inv.app
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M) ≫
        (scalarExtensionFunctor ((D.coefficients E F h).quotient m) X).map
          (systemReduction P E X v qE M)) := by
  have hs := support_reduction_formula P D F c v qF qY
    (e.supportCoordinates F n) (e.supportCoordinates F m) ((D.scalars E F h X).T.obj M)
  have hr := (scalar_reduction_formula P D h X v qE qF
    (e.scalarEvaluation E F h X n) (e.scalarEvaluation E F h X m)).choose_spec M
  unfold comparisonTarget
  exact conjugate_reduction
    (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g)
    (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val m) c.i c.g)
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) X)
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) Y)
    (reductionDirectImageComparison (SpTowerCalculus.quotient P.coefficients.l F.val v)
      c.i c.g)
    ((e.scalarEvaluation E F h X n).iso.app M)
    ((e.scalarEvaluation E F h X m).iso.app M)
    ((supportEvaluation P D F c n (e.supportCoordinates F n)).app _)
    ((supportEvaluation P D F c m (e.supportCoordinates F m)).app _)
    (systemReduction P F Y v qY
      ((SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).obj
        ((D.scalars E F h X).T.obj M)))
    (systemReduction P F X v qF ((D.scalars E F h X).T.obj M)) _ hs hr

set_option maxHeartbeats 2000000 in
-- These equations elaborate the fixed unbounded derived functors in several coordinates.
private theorem mixed_first (P : PurityFiniteSetting.{u}) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (e : EvaluationLaw P D c)
    {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (qE : QuotientRestriction P E X v) (qF : QuotientRestriction P F X v)
    (qY : QuotientRestriction P F Y v)
    (hc : (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n) =
      ((D.coefficients E F h).quotient m).comp
        (SpTowerCalculus.quotient P.coefficients.l E.val v))
    (M : SpTowerShriek.D P.coefficients.l E.val X) :
    quotientAfterComparison P D c e h v qY M =
      commonTransitionComparison P D c h v hc qE M := by
  let Mn := (SpTowerShriek.Ev P.coefficients.l E.val X n).obj M
  let a := (D.coefficients E F h).quotient n
  let b := SpTowerCalculus.quotient P.coefficients.l F.val v
  let d := SpTowerCalculus.quotient P.coefficients.l E.val v
  let t := (D.coefficients E F h).quotient m
  let H := reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val m) c.i c.g
  let Hn := reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g
  let ax := scalarExtensionFunctor_composition a b X
  let ay := scalarExtensionFunctor_composition a b Y
  let r := eqToHom (congrArg (fun z ↦ (scalarExtensionFunctor z X).obj Mn) hc) ≫
    (scalarExtensionFunctor_composition d t X).inv.app Mn ≫
    (scalarExtensionFunctor t X).map (systemReduction P E X v qE M)
  let bn := (comparison P D h c).app M
  let rn := systemReduction P F Y v qY
    ((SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).obj
      ((D.scalars E F h X).T.obj M))
  let V := scalarExtensionFunctor b Y
  have ht := target_reduction P D c e h v qE qF qY hc M
  have he := evaluated_comparison P D c e h n M
  have hcoc := ambient_cocycle P (ell_torsion P E n) (ell_torsion P F n)
    (ell_torsion P F m) a b c.i c.g Mn
  unfold quotientAfterComparison commonTransitionComparison
  calc
    _ = ay.inv.app (Hn.obj Mn) ≫
        V.map ((comparisonSource P D c e h n M).inv ≫
          (SpTowerShriek.Ev P.coefficients.l F.val Y n).map bn ≫
          (comparisonTarget P D c e h n M).hom) ≫
        (V.map (comparisonTarget P D c e h n M).inv ≫ rn ≫
          (comparisonTarget P D c e h m M).hom) := by
      exact insert_iso V (ay.inv.app (Hn.obj Mn))
        (comparisonSource P D c e h n M).inv
        ((SpTowerShriek.Ev P.coefficients.l F.val Y n).map bn)
        (comparisonTarget P D c e h n M) rn (comparisonTarget P D c e h m M).hom
    _ = ay.inv.app (Hn.obj Mn) ≫
        V.map ((reductionDirectImageComparison a c.i c.g).app Mn) ≫
        (reductionDirectImageComparison b c.i c.g).app
          ((scalarExtensionFunctor a X).obj Mn) ≫ H.map (ax.hom.app Mn ≫ r) := by
      exact map_comp_congr V (ay.inv.app (Hn.obj Mn)) he ht
    _ = (reductionDirectImageComparison (b.comp a) c.i c.g).app Mn ≫ H.map r := by
      exact cancel_cocycle Hn
        (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g) H
        (scalarExtensionFunctor a X) (scalarExtensionFunctor a Y)
        (scalarExtensionFunctor b X) V
        (scalarExtensionFunctor (b.comp a) X) (scalarExtensionFunctor (b.comp a) Y)
        ax ay (reductionDirectImageComparison a c.i c.g)
        (reductionDirectImageComparison b c.i c.g)
        (reductionDirectImageComparison (b.comp a) c.i c.g) Mn _ r hcoc

set_option maxHeartbeats 2000000 in
-- These equations elaborate the fixed unbounded derived functors in several coordinates.
private theorem mixed_second (P : PurityFiniteSetting.{u}) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (e : EvaluationLaw P D c)
    {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (qE : QuotientRestriction P E X v) (qY : QuotientRestriction P E Y v)
    (hc : (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n) =
      ((D.coefficients E F h).quotient m).comp
        (SpTowerCalculus.quotient P.coefficients.l E.val v))
    (M : SpTowerShriek.D P.coefficients.l E.val X) :
    HEq (comparisonAfterQuotient P D c e h v qY M)
      (commonTransitionComparison P D c h v hc qE M) := by
  let Mn := (SpTowerShriek.Ev P.coefficients.l E.val X n).obj M
  let Mm := (SpTowerShriek.Ev P.coefficients.l E.val X m).obj M
  let a := (D.coefficients E F h).quotient n
  let b := SpTowerCalculus.quotient P.coefficients.l F.val v
  let d := SpTowerCalculus.quotient P.coefficients.l E.val v
  let t := (D.coefficients E F h).quotient m
  let H := reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val m) c.i c.g
  let Hn := reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g
  let Hm := reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val m) c.i c.g
  let ax := scalarExtensionFunctor_composition d t X
  let ay := scalarExtensionFunctor_composition d t Y
  let rE := systemReduction P E X v qE M
  let r := ax.inv.app Mn ≫ (scalarExtensionFunctor t X).map rE
  let V := scalarExtensionFunctor t Y
  let suppn := (supportEvaluation P D E c n (e.supportCoordinates E n)).app M
  let suppm := (supportEvaluation P D E c m (e.supportCoordinates E m)).app M
  let rn := systemReduction P E Y v qY
    ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M)
  have hs := support_reduction_formula P D E c v qE qY
    (e.supportCoordinates E n) (e.supportCoordinates E m) M
  have hcoc := ambient_cocycle P (ell_torsion P E n) (ell_torsion P E m)
    (ell_torsion P F m) d t c.i c.g Mn
  have he : (e.scalarEvaluation E F h Y m).iso.inv.app
        ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M) ≫
      (SpTowerShriek.Ev P.coefficients.l F.val Y m).map ((comparison P D h c).app M) ≫
      (comparisonTarget P D c e h m M).hom =
    V.map suppm.hom ≫ (reductionDirectImageComparison t c.i c.g).app Mm := by
    apply (cancel_epi ((e.scalarEvaluation E F h Y m).iso.hom.app _)).mp
    simpa only [V, suppm, t, Mm, Iso.hom_inv_id_app_assoc, comparisonTarget,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
      Functor.comp_obj] using e.evaluation E F h m M
  have hpath : comparisonAfterQuotient P D c e h v qY M =
      (reductionDirectImageComparison (t.comp d) c.i c.g).app Mn ≫ H.map r := by
    unfold comparisonAfterQuotient
    calc
      _ = ay.inv.app (Hn.obj Mn) ≫
          V.map ((scalarExtensionFunctor d Y).map suppn.inv ≫ rn ≫ suppm.hom) ≫
          (reductionDirectImageComparison t c.i c.g).app Mm := by
        exact map_suffix V (ay.inv.app (Hn.obj Mn))
          ((scalarExtensionFunctor d Y).map suppn.inv) rn
          ((e.scalarEvaluation E F h Y m).iso.inv.app _)
          ((SpTowerShriek.Ev P.coefficients.l F.val Y m).map ((comparison P D h c).app M))
          (comparisonTarget P D c e h m M).hom suppm.hom
          ((reductionDirectImageComparison t c.i c.g).app Mm) he
      _ = ay.inv.app (Hn.obj Mn) ≫
          V.map ((reductionDirectImageComparison d c.i c.g).app Mn) ≫
          V.map (Hm.map rE) ≫ (reductionDirectImageComparison t c.i c.g).app Mm := by
        exact map_factor V (ay.inv.app (Hn.obj Mn))
          ((reductionDirectImageComparison t c.i c.g).app Mm) hs
      _ = ay.inv.app (Hn.obj Mn) ≫
          V.map ((reductionDirectImageComparison d c.i c.g).app Mn) ≫
          (reductionDirectImageComparison t c.i c.g).app
            ((scalarExtensionFunctor d X).obj Mn) ≫
          H.map (ax.hom.app Mn ≫ r) := by
        exact naturality_with_iso Hm V (scalarExtensionFunctor t X) H
          (reductionDirectImageComparison t c.i c.g) rE (ax.app Mn)
          (ay.inv.app (Hn.obj Mn))
          (V.map ((reductionDirectImageComparison d c.i c.g).app Mn))
      _ = _ := cancel_cocycle Hn Hm H
        (scalarExtensionFunctor d X) (scalarExtensionFunctor d Y)
        (scalarExtensionFunctor t X) V
        (scalarExtensionFunctor (t.comp d) X) (scalarExtensionFunctor (t.comp d) Y)
        ax ay (reductionDirectImageComparison d c.i c.g)
        (reductionDirectImageComparison t c.i c.g)
        (reductionDirectImageComparison (t.comp d) c.i c.g) Mn _ r hcoc
  have hcongr : commonTransitionComparison P D c h v hc qE M =
      eqToHom (congrArg (fun z ↦ (scalarExtensionFunctor z Y).obj (Hn.obj Mn)) hc) ≫
        ((reductionDirectImageComparison (t.comp d) c.i c.g).app Mn ≫ H.map r) := by
    unfold commonTransitionComparison
    change (reductionDirectImageComparison (b.comp a) c.i c.g).app Mn ≫
      H.map (eqToHom (congrArg (fun z ↦ (scalarExtensionFunctor z X).obj Mn) hc) ≫ r) = _
    exact transport_suffix H r (finite_comparison_congr hc c.i c.g Mn)
  exact (heq_of_eq hpath).trans
    ((eqToHom_comp_heq
      ((reductionDirectImageComparison (t.comp d) c.i c.g).app Mn ≫ H.map r)
      (congrArg (fun z ↦ (scalarExtensionFunctor z Y).obj (Hn.obj Mn)) hc)).symm.trans
        (heq_of_eq hcongr.symm))

/-- The given finite evaluation law extends to mixed quotient compatibility for the
actual system comparison. This does not assert invertibility or the whole-system
coefficient-extension cocycle, and retains the given evaluation coordinates exactly.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
lem-sp-field-shriek-system-comparison, step 8
(blueprint: lem-route-field-shriek-system-mixed).

Proof: identify quotient restriction with constant-ring restriction by the identity
on sections. The residue-class formula in Coefficients proves the coefficient square:
both quotient paths send an integer x to its image modulo ell^(m+1). Transpose the
naturality square of derivedTransition under the finite scalar adjunction; this is
ComparisonTransitionSquare for every system morphism, hence for comparison.app M.
The semilinear direct-image transition formula, followed by termwise open evaluation,
identifies the compact-support transition with finite coefficient comparison followed
by compact support of the input reduction. Substitute this formula and the given
EvaluationLaw in quotientAfterComparison and comparisonAfterQuotient. The finite
coefficient cocycle identifies the two coefficient words with the comparison for the
common map R_n to S_m, under the specified scalar associators. Naturality of the
finite comparison moves the input reduction past the second comparison, leaving
exactly commonTransitionComparison. The coefficient square transports the two source
scalar actions; their targets are already identical, so these are the required HEq
statements. Equal indices reduce to the scalar unitors. The quotient maps may be
nonflat throughout: all reductions are the actual derived adjunction transposes. -/
theorem field_shriek_system_mixed (P : PurityFiniteSetting.{u}) (D : Models P)
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (c : Compactification f)
    (e : EvaluationLaw P D c) :
    ∃ l : MixedLaw P D c, l.toEvaluationLaw = e := by
  let q := quotientCoordinates P
  let l : MixedLaw P D c :=
    { toEvaluationLaw := e
      quotientCoordinates := q
      coefficientSquare := coefficient_square P D
      system_square := by
        intro E F h m n v M _
        unfold ComparisonTransitionSquare
        exact reduction_natural P F Y v (q F Y v) ((comparison P D h c).app M)
      mixed := by
        intro E F h m n v M _
        exact ⟨heq_of_eq (mixed_first P D c e h v (q E X v) (q F X v) (q F Y v)
          (coefficient_square P D E F h m n v) M),
          mixed_second P D c e h v (q E X v) (q E Y v)
            (coefficient_square P D E F h m n v) M⟩ }
  exact ⟨l, rfl⟩

end AlgebraicGeometry.ProEtale.FieldShriekSystem
