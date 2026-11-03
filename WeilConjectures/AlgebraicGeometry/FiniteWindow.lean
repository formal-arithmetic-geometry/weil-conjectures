/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ConstructibleIndExtBound
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# The finite cohomological window for constructible sources

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-lem-finite-window/_section.md and its proof
(blueprint: sk-lem-finite-window).

The two coefficient cases use the ordinary unbounded derived category of module sheaves.
The predicate indexing the equivalences is precisely Dic: every cohomology sheaf is an
ambient small filtered colimit of finite constant-model constructible sheaves.
`FiniteWindowAssertions` specifies the truncation zigzag and naturality in K.
No lower or upper cohomological bound on K is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Triangulated CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · change (CondensedRing.upperStar Λ (𝟙 X)).obj M ≅
      ((upperStarFromPoint X).mapMod Λ).obj HasZeroObject.zero.choose
    exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.

private lemma hom_mor₁_bijective
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (t : TStructure D) {Y : D} {T : Triangle D}
    (hT : T ∈ distTriang D)
    (hle : t.IsLE Y 0) (hge : t.IsGE T.obj₃ 1) :
    Function.Bijective (fun f : Y ⟶ T.obj₁ ↦ f ≫ T.mor₁) := by
  constructor
  · intro f g hfg
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang T hT) (f - g) (by
      rw [Triangle.invRotate_mor₂]
      simpa [Preadditive.sub_comp] using sub_eq_zero.mpr hfg)
    have hq0 : q = 0 := by
      apply t.zero_of_isLE_of_isGE q 0 2 (by omega) hle
      rw [Triangle.invRotate_obj₁]
      exact t.isGE_shift T.obj₃ 1 (-1) 2 (by omega)
    rw [hq0, zero_comp] at hq
    exact sub_eq_zero.mp hq
  · intro g
    have hz : g ≫ T.mor₂ = 0 :=
      t.zero_of_isLE_of_isGE _ 0 1 (by omega) hle hge
    obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ T hT g hz
    exact ⟨f, hf.symm⟩

private lemma hom_mor₂_bijective
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {Y : D} {T : Triangle D} (hT : T ∈ distTriang D)
    (h₀ : Subsingleton (Y ⟶ T.obj₁)) (h₁ : Subsingleton (Y ⟶ T.obj₁⟦(1 : ℤ)⟧)) :
    Function.Bijective (fun f : Y ⟶ T.obj₂ ↦ f ≫ T.mor₂) := by
  constructor
  · intro f g hfg
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ T hT (f - g) (by
      simpa [Preadditive.sub_comp] using sub_eq_zero.mpr hfg)
    rw [h₀.elim q 0, zero_comp] at hq
    exact sub_eq_zero.mp hq
  · intro g
    obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ T.rotate
      (rot_of_distTriang T hT) g (h₁.elim _ 0)
    exact ⟨f, hf.symm⟩

private lemma unsigned_postcomp_bijective
    {D : Type u} [Category.{v} D] [Preadditive D]
    {Y Z W : D} (f : Z ⟶ W) (a : ℤˣ)
    (h : Function.Bijective (fun g : Y ⟶ Z ↦ g ≫ (a • f))) :
    Function.Bijective (fun g : Y ⟶ Z ↦ g ≫ f) := by
  have hs : ∀ g : Y ⟶ Z, g ≫ (a • f) = a • (g ≫ f) := by
    intro g
    simp only [Units.smul_def, Preadditive.comp_zsmul]
  constructor
  · intro g k hgk
    apply h.1
    change g ≫ (a • f) = k ≫ (a • f)
    rw [hs, hs]
    exact congrArg (fun x ↦ a • x) hgk
  · intro g
    obtain ⟨k, hk⟩ := h.2 (a • g)
    refine ⟨k, (MulAction.toPerm a).injective ?_⟩
    change a • (k ≫ f) = a • g
    simpa only [hs] using hk

/-- The finite-window conclusion, including its canonical-map characterization and
naturality on a full class P of derived objects. This only packages the two equations
in the statement; it chooses no map or inverse.
Source: blueprint main-20261015, sk-lem-finite-window, displayed natural isomorphism
(blueprint: sk-lem-finite-window). -/
def FiniteWindowAssertions
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{t} A]
    (C : A) (P : ObjectProperty (DerivedCategory A)) (d_C : ℕ) (m : ℤ) : Prop :=
    ∃ e : ∀ K : {K : DerivedCategory A // P K},
      ((DerivedCategory.singleFunctor _ 0).obj C ⟶ K.val⟦m⟧) ≃+
        ((DerivedCategory.singleFunctor _ 0).obj C ⟶
          ((DerivedCategory.TStructure.t.truncGE (m - (d_C : ℤ))).obj
            ((DerivedCategory.TStructure.t.truncLE m).obj K.val))⟦m⟧),
      (∀ K, ∀ f : (DerivedCategory.singleFunctor _ 0).obj C ⟶
          ((DerivedCategory.TStructure.t.truncLE m).obj K.val)⟦m⟧,
        e K (f ≫ ((DerivedCategory.TStructure.t.truncLEι m).app K.val)⟦m⟧') =
          f ≫ ((DerivedCategory.TStructure.t.truncGEπ (m - (d_C : ℤ))).app
            ((DerivedCategory.TStructure.t.truncLE m).obj K.val))⟦m⟧') ∧
      (∀ K L, ∀ (f : K.val ⟶ L.val)
          (g : (DerivedCategory.singleFunctor _ 0).obj C ⟶ K.val⟦m⟧),
        e L (g ≫ f⟦m⟧') = e K g ≫
          ((DerivedCategory.TStructure.t.truncLE m ⋙
            DerivedCategory.TStructure.t.truncGE (m - (d_C : ℤ))).map f)⟦m⟧')

/-- The single-degree identification between Ext and derived morphisms. -/
private theorem finiteWindow_hom_single_of_ext_bound
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (C B : A) (d : ℕ) (q : ℤ) (hq : q ≤ -(d : ℤ) - 1)
    (hExt : Subsingleton
      (@Abelian.Ext _ _ _ (HasExt.standard _) C B (-q).toNat)) :
    Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      (DerivedCategory.singleFunctor A q).obj B) := by
  have : HasExt A := HasExt.standard A
  have hcast : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
  have : Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      ((DerivedCategory.singleFunctor A 0).obj B)⟦((-q).toNat : ℤ)⟧) :=
    Equiv.subsingleton (Abelian.Ext.homEquiv (X := C) (Y := B)).symm
  have hshift : Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      ((DerivedCategory.singleFunctor A 0).obj B)⟦-q⟧) := by
    simpa only [hcast] using this
  let e := ((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app B
  exact ⟨fun f g ↦ by
    have hfg := hshift.elim (f ≫ e.inv) (g ≫ e.inv)
    simpa using congrArg (fun k ↦ k ≫ e.hom) hfg⟩

/-- Apply left-complete devissage below the cutoff, then attach its boundary layer.
The auxiliary property includes zero so truncations preserve it without requiring
any additional closure property of the original class of sheaves. -/
private theorem finiteWindow_hom_lower_tail_of_ext
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [HasLimitsOfShape (Discrete ℕ) A]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (C : A) (d : ℕ)
    (hExt : ∀ B, P B → ∀ r : ℕ, d < r →
      Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r))
    (L : DerivedCategory A) (hL : DerivedCategory.homologyProperty P L)
    (hvanish : ∀ q : ℤ, -(d : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor A q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶ L) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let P₀ : ObjectProperty A := fun B ↦ P B ∨ IsZero B
  have : P₀.ContainsZero := ⟨⟨HasZeroObject.zero.choose, isZero_zero A, Or.inr (isZero_zero A)⟩⟩
  have : P₀.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.elim
    (fun h ↦ Or.inl (P.prop_of_iso e h)) (fun h ↦ Or.inr (h.of_iso e.symm))⟩
  let N : ℤ := -(d : ℤ) - 1
  let S := (DerivedCategory.singleFunctor A 0).obj C
  have hv : ∀ B, P₀ B → ∀ q ≤ N,
      ∀ f : S ⟶ (DerivedCategory.singleFunctor A q).obj B, f = 0 := by
    intro B hB q hq f
    rcases hB with hB | hB
    · exact (finiteWindow_hom_single_of_ext_bound C B d q hq
        (hExt B hB (-q).toNat (by dsimp [N] at hq; omega))).elim f 0
    · exact ((DerivedCategory.singleFunctor A q).map_isZero hB).eq_of_tgt f 0
  have hL₀ : DerivedCategory.homologyProperty P₀ L := fun q ↦ Or.inl (hL q)
  have : L.IsLE N := (DerivedCategory.isLE_iff L N).mpr hvanish
  let T := (t.triangleLTGE N).obj L
  have hT := t.triangleLTGE_distinguished N L
  have h₁ : DerivedCategory.homologyProperty P₀ T.obj₁ :=
    (DerivedCategory.homologyProperty P₀).prop_of_iso
      ((t.truncLEIsoTruncLT (N - 1) N (by omega)).app L)
      (DerivedCategory.homologyProperty_truncLE hL₀ (N - 1))
  have h₃ : DerivedCategory.homologyProperty P₀ T.obj₃ :=
    DerivedCategory.homologyProperty_truncGE hL₀ N
  have : T.obj₁.IsLE (N - 1) := inferInstanceAs (t.IsLE T.obj₁ (N - 1))
  have : T.obj₃.IsGE N := inferInstanceAs (t.IsGE T.obj₃ N)
  have : T.obj₃.IsLE N := inferInstanceAs (t.IsLE ((t.truncGE N).obj L) N)
  refine subsingleton_of_forall_eq 0 fun f ↦ ?_
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f
    (DerivedCategory.eq_zero_of_isGE_of_isLE_self N hv N T.obj₃ h₃ le_rfl _)
  rw [hg, DerivedCategory.eq_zero_of_isLE N hv T.obj₁ h₁ g, zero_comp]


-- Apply the two truncation triangles, then compose their induced Hom equivalences.

private lemma finiteWindow_of_lowerTail
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{t} A]
    (C : A) (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (d : ℕ) (m : ℤ)
    (hvanish : ∀ L : DerivedCategory A,
      DerivedCategory.homologyProperty P L →
      (∀ q : ℤ, -(d : ℤ) - 1 < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) →
      Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L)) :
    FiniteWindowAssertions C (DerivedCategory.homologyProperty P) d m := by
  classical
  let t : TStructure (DerivedCategory A) := DerivedCategory.TStructure.t
  let Y := (DerivedCategory.singleFunctor A 0).obj C
  let Q := DerivedCategory.homologyProperty P
  let a (K : {K : DerivedCategory A // Q K}) :
      (Y ⟶ ((t.truncLE m).obj K.val)⟦m⟧) →+ (Y ⟶ K.val⟦m⟧) :=
    { toFun := fun f ↦ f ≫ ((t.truncLEι m).app K.val)⟦m⟧'
      map_zero' := zero_comp
      map_add' := fun _ _ ↦ Preadditive.add_comp .. }
  let b (K : {K : DerivedCategory A // Q K}) :
      (Y ⟶ ((t.truncLE m).obj K.val)⟦m⟧) →+
        (Y ⟶ ((t.truncGE (m - (d : ℤ))).obj ((t.truncLE m).obj K.val))⟦m⟧) :=
    { toFun := fun f ↦ f ≫ ((t.truncGEπ (m - (d : ℤ))).app
        ((t.truncLE m).obj K.val))⟦m⟧'
      map_zero' := zero_comp
      map_add' := fun _ _ ↦ Preadditive.add_comp .. }
  have ha (K : {K : DerivedCategory A // Q K}) : Function.Bijective (a K) := by
    let T := (t.triangleLEGT m).obj K.val
    let Tm := (Triangle.shiftFunctor _ m).obj T
    have hTm : Tm ∈ distTriang _ :=
      Triangle.shift_distinguished T (t.triangleLEGT_distinguished m K.val) m
    have : t.IsGE T.obj₃ (m + 1) := by
      exact t.isGE_truncGT_obj K.val m (m + 1)
    have hge : t.IsGE Tm.obj₃ 1 :=
      t.isGE_shift T.obj₃ (m + 1) m 1 (by omega)
    exact unsigned_postcomp_bijective _ (Int.negOnePow m)
      (hom_mor₁_bijective t hTm (by infer_instance) hge)
  have hb (K : {K : DerivedCategory A // Q K}) : Function.Bijective (b K) := by
    let V := (t.truncLE (m - (d : ℤ) - 1)).obj ((t.truncLE m).obj K.val)
    let T := (t.triangleLEGE (m - (d : ℤ) - 1) (m - (d : ℤ)) (by omega)).obj
      ((t.truncLE m).obj K.val)
    let Tm := (Triangle.shiftFunctor _ m).obj T
    have hTm : Tm ∈ distTriang _ := Triangle.shift_distinguished T
      (t.triangleLEGE_distinguished _ _ (by omega) _) m
    have hPV : Q V := DerivedCategory.homologyProperty_truncLE
      (DerivedCategory.homologyProperty_truncLE K.property m) _
    have hPVm : Q (V⟦m⟧) := Q.le_shift m V hPV
    have hPVm1 : Q ((V⟦m⟧)⟦(1 : ℤ)⟧) := Q.le_shift 1 _ hPVm
    have hVm : t.IsLE (V⟦m⟧) (-(d : ℤ) - 1) :=
      t.isLE_shift V (m - (d : ℤ) - 1) m (-(d : ℤ) - 1) (by omega)
    have hVm1 : t.IsLE ((V⟦m⟧)⟦(1 : ℤ)⟧) (-(d : ℤ) - 2) :=
      t.isLE_shift (V⟦m⟧) (-(d : ℤ) - 1) 1 (-(d : ℤ) - 2) (by omega)
    have h₀ : Subsingleton (Y ⟶ Tm.obj₁) := hvanish _ hPVm
      (fun q hq ↦ (DerivedCategory.isLE_iff _ _).mp hVm q hq)
    have h₁ : Subsingleton (Y ⟶ Tm.obj₁⟦(1 : ℤ)⟧) := hvanish _ hPVm1
      (fun q hq ↦ (DerivedCategory.isLE_iff _ _).mp hVm1 q (by omega))
    exact unsigned_postcomp_bijective _ (Int.negOnePow m)
      (hom_mor₂_bijective hTm h₀ h₁)
  let e (K : {K : DerivedCategory A // Q K}) :=
    (AddEquiv.ofBijective (a K) (ha K)).symm.trans (AddEquiv.ofBijective (b K) (hb K))
  have he (K : {K : DerivedCategory A // Q K}) (f) : e K (a K f) = b K f := by
    exact congrArg (b K) ((AddEquiv.ofBijective (a K) (ha K)).symm_apply_apply f)
  refine ⟨e, he, ?_⟩
  intro K L f g
  obtain ⟨g', rfl⟩ := (ha K).surjective g
  have hnatA : ((t.truncLEι m).app K.val)⟦m⟧' ≫ f⟦m⟧' =
      ((t.truncLE m).map f)⟦m⟧' ≫ ((t.truncLEι m).app L.val)⟦m⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k ↦ k⟦m⟧') ((t.truncLEι m).naturality f).symm
  have hnatB : ((t.truncLE m).map f)⟦m⟧' ≫
      ((t.truncGEπ (m - (d : ℤ))).app ((t.truncLE m).obj L.val))⟦m⟧' =
      ((t.truncGEπ (m - (d : ℤ))).app ((t.truncLE m).obj K.val))⟦m⟧' ≫
        ((t.truncLE m ⋙ t.truncGE (m - (d : ℤ))).map f)⟦m⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k ↦ k⟦m⟧')
      ((t.truncGEπ (m - (d : ℤ))).naturality ((t.truncLE m).map f))
  change e L ((g' ≫ _) ≫ _) = e K (a K g') ≫ _
  rw [Category.assoc, hnatA, ← Category.assoc]
  change e L (a L (g' ≫ ((t.truncLE m).map f)⟦m⟧')) = _
  rw [he, he]
  change (g' ≫ _) ≫ _ = (g' ≫ _) ≫ _
  rw [Category.assoc, Category.assoc, hnatB]

/-- The truncation zigzag induces a natural additive equivalence on Hom from C,
for a finite subextension of the fixed algebraic closure. The indexing subtype is
the full object class Dic;
its morphisms below are all ambient derived morphisms.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-lem-finite-window/_section.md, equation (6.3)
and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the six DAG steps of the node:
1. (sk-cor-ambient-ind-derived, def-kun-truncations, lem-sf-derived-truncation-triangle,
   def-sbc-standard-tstructure-derived-category, def-weil-t-structure,
   lem-weil-pbc-hom-into-triangle-exact) Dic is stable under truncations and shifts;
   replace K by K[m] to work at m = 0. Put A = tau_le(0) K and U = tau_ge(1) K. In the
   triangle A --> K --> U, Hom(C,U) = Hom(C,U[-1]) = 0 since C is <= 0 and U, U[-1]
   are >= 1, so a_K: Hom(C,A) --> Hom(C,K) is bijective.
2. (sk-cor-ind-heart-ii, def-pc-ext, lem-sfb-degreewise-bounded-devissage,
   lem-weil-pbc-hom-into-triangle-exact) Claim (6.4) for bounded L in Dic with
   H^q(L) = 0 for q > -d_C-1: each layer H^q(L)[-q] has Hom(C,H^q(L)[-q]) =
   Ext^(-q)(C,H^q L) = 0 since -q > d_C; devissage over a finite interval
   gives Hom(C,L) = 0.
3. (sk-thm-pe-weakly-contractible-basis, sk-prop-pe-products, sk-prop-pe-left-complete,
   sk-prop-pe-milnor, lem-weil-pbc-hom-into-triangle-exact) For arbitrary such L,
   L = R lim L_n with L_n = tau_ge(-n) L; the Milnor triangle and the product universal
   property give the exact segment
   prod Hom(C,L_n[-1]) --(1-T)--> prod Hom(C,L_n[-1]) --> Hom(C,L)
   --> prod Hom(C,L_n) --(1-T)--> prod Hom(C,L_n).
4. (lem-pc-derived-lower-truncation-step-triangle, lem-weil-pbc-hom-into-triangle-exact,
   def-pc-ext, sk-cor-ind-heart-ii) Step 2 kills every Hom(C,L_n). The triangle
   H^(-n-1)(L)[n+1] --> L_(n+1) --> L_n, shifted by [-1], has outer terms
   Ext^n(C,H^(-n-1) L) and Ext^(n+1)(C,H^(-n-1) L), zero for n > d_C; so the
   transitions G_(n+1) --> G_n of G_n = Hom(C,L_n[-1]) are bijective for n > d_C.
5. (elementary) The tower G_n is eventually constant by step 4, so its first derived
   inverse limit is zero. The right inverse limit is zero by the bounded case.
   The Milnor exact sequence gives Hom(C,L) = 0, proving (6.4) with no lower bound.
6. (lem-sf-derived-truncation-triangle, sk-cor-ambient-ind-derived,
   lem-weil-pbc-hom-into-triangle-exact, def-kun-truncations) Put V = tau_le(-d_C-1) A,
   B = tau_ge(-d_C) A. In V --> A --> B, (6.4) kills Hom(C,V) and Hom(C,V[1]), so
   b_K: Hom(C,A) --> Hom(C,B) is bijective. The equivalence is b_K a_K^(-1); the first
   equation in FiniteWindowAssertions says e(a(f)) = b(f). Functorial truncation gives
   F a_K = a_L F_A and F_B b_K = b_L F_A, hence F_B b_K a_K^(-1) = b_L a_L^(-1) F: the
   naturality equation in FiniteWindowAssertions. Undoing the shift yields (6.3). -/
theorem finiteWindow_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X)
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X,
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (m : ℤ) :
    FiniteWindowAssertions C (fun K ↦ ∀ q : ℤ,
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by
  let P := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
  have : P.ContainsZero :=
    ⟨HasZeroObject.zero.choose, isZero_zero _,
    ObjectProperty.le_ind _ _
      (constantModelConstructible_of_isZero _ X _ (isZero_zero _))⟩
  exact finiteWindow_of_lowerTail C P d_C m
    (fun L hL hv ↦ finiteWindow_unbounded ℓ E X C hC d_C hExt L hL hv)

/-- The finite-window theorem with a variable coefficient ring in the standing field family.
The coefficient equality is equality of bundled monoid objects, so it includes multiplication.
The positive prime characteristic and its inequality with ell are recorded explicitly.
There is no additional condition on the base field (for example, F_p(t) is allowed).

Source: blueprint latest, sec-compactness/prose-06-02 and sk-lem-finite-window, equation (6.3).
(blueprint: sk-lem-finite-window).
Proof: extend the supplied Ext bound to ind-constructible sheaves. Exact countable
products give left-complete lower-tail devissage; the boundary layer is killed by
the same Ext bound. Apply the two truncation triangles and compose their Hom
equivalences. Their functorial maps give the characterization and naturality. -/
theorem finiteWindow
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : p.Prime) (_hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (C : pulledBackModuleObjects Λ X)
    (hC : IsConstantModelConstructible Λ X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects Λ X,
      IsConstantModelConstructible Λ X N → ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (m : ℤ) :
    FiniteWindowAssertions C (fun K ↦ ∀ q : ℤ,
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by
  let P := ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
  have : P.ContainsZero :=
    ⟨HasZeroObject.zero.choose, isZero_zero _, ObjectProperty.le_ind _ _
      (constantModelConstructible_of_isZero Λ X _ (isZero_zero _))⟩
  let A := pulledBackModuleObjects Λ X
  let : CountableAB4Star A := .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  have : HasExactLimitsOfShape (Discrete ℕ) A := CountableAB4Star.ofShape ℕ
  have hInd : ∀ B : A, P B → ∀ r : ℕ, d_C < r →
      Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
    rcases _hΛ with ⟨E, hE⟩ | hQ
    · exact constructibleInd_extBound ℓ E Λ (Or.inl hE) X C hC d_C hExt
    · exact constructibleInd_extBound ℓ ⟨⊥, inferInstance⟩ Λ (Or.inr hQ)
        X C hC d_C hExt
  exact finiteWindow_of_lowerTail C P d_C m (fun L hL hv ↦
    finiteWindow_hom_lower_tail_of_ext (A := A) P C d_C hInd L hL hv)

/-- Variant of `finiteWindow` for a base field that is finite or algebraically closed,
with ringChar k different from ell (this also covers characteristic zero).
The coefficient equality is equality of bundled monoid objects, so it includes multiplication.

Source: blueprint latest, sec-compactness/prose-06-02 and sk-lem-finite-window, equation (6.3).
(blueprint: sk-lem-finite-window).
Proof: the same as for `finiteWindow`; the base-field hypotheses are not used. -/
theorem finiteWindow_general
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k) (_hkl : ringChar k ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (C : pulledBackModuleObjects Λ X)
    (hC : IsConstantModelConstructible Λ X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects Λ X,
      IsConstantModelConstructible Λ X N → ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (m : ℤ) :
    FiniteWindowAssertions C (fun K ↦ ∀ q : ℤ,
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by
  let P := ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
  have : P.ContainsZero :=
    ⟨HasZeroObject.zero.choose, isZero_zero _, ObjectProperty.le_ind _ _
      (constantModelConstructible_of_isZero Λ X _ (isZero_zero _))⟩
  let A := pulledBackModuleObjects Λ X
  let : CountableAB4Star A := .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  have : HasExactLimitsOfShape (Discrete ℕ) A := CountableAB4Star.ofShape ℕ
  have hInd : ∀ B : A, P B → ∀ r : ℕ, d_C < r →
      Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
    rcases _hΛ with ⟨E, hE⟩ | hQ
    · exact constructibleInd_extBound ℓ E Λ (Or.inl hE) X C hC d_C hExt
    · exact constructibleInd_extBound ℓ ⟨⊥, inferInstance⟩ Λ (Or.inr hQ)
        X C hC d_C hExt
  exact finiteWindow_of_lowerTail C P d_C m (fun L hL hv ↦
    finiteWindow_hom_lower_tail_of_ext (A := A) P C d_C hInd L hL hv)

/-- The truncation zigzag induces a natural additive equivalence on Hom from C,
for the condensed algebraic closure with finite-subextension-valued sections.
The indexing subtype is the full object class Dic;
its morphisms below are all ambient derived morphisms.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-lem-finite-window/_section.md, equation (6.3)
and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the six DAG steps of the node:
1. (sk-cor-ambient-ind-derived, def-kun-truncations, lem-sf-derived-truncation-triangle,
   def-sbc-standard-tstructure-derived-category, def-weil-t-structure,
   lem-weil-pbc-hom-into-triangle-exact) Dic is stable under truncations and shifts;
   replace K by K[m] to work at m = 0. Put A = tau_le(0) K and U = tau_ge(1) K. In the
   triangle A --> K --> U, Hom(C,U) = Hom(C,U[-1]) = 0 since C is <= 0 and U, U[-1]
   are >= 1, so a_K: Hom(C,A) --> Hom(C,K) is bijective.
2. (sk-cor-ind-heart-ii, def-pc-ext, lem-sfb-degreewise-bounded-devissage,
   lem-weil-pbc-hom-into-triangle-exact) Claim (6.4) for bounded L in Dic with
   H^q(L) = 0 for q > -d_C-1: each layer H^q(L)[-q] has Hom(C,H^q(L)[-q]) =
   Ext^(-q)(C,H^q L) = 0 since -q > d_C; devissage over a finite interval
   gives Hom(C,L) = 0.
3. (sk-thm-pe-weakly-contractible-basis, sk-prop-pe-products, sk-prop-pe-left-complete,
   sk-prop-pe-milnor, lem-weil-pbc-hom-into-triangle-exact) For arbitrary such L,
   L = R lim L_n with L_n = tau_ge(-n) L; the Milnor triangle and the product universal
   property give the exact segment
   prod Hom(C,L_n[-1]) --(1-T)--> prod Hom(C,L_n[-1]) --> Hom(C,L)
   --> prod Hom(C,L_n) --(1-T)--> prod Hom(C,L_n).
4. (lem-pc-derived-lower-truncation-step-triangle, lem-weil-pbc-hom-into-triangle-exact,
   def-pc-ext, sk-cor-ind-heart-ii) Step 2 kills every Hom(C,L_n). The triangle
   H^(-n-1)(L)[n+1] --> L_(n+1) --> L_n, shifted by [-1], has outer terms
   Ext^n(C,H^(-n-1) L) and Ext^(n+1)(C,H^(-n-1) L), zero for n > d_C; so the
   transitions G_(n+1) --> G_n of G_n = Hom(C,L_n[-1]) are bijective for n > d_C.
5. (elementary) The tower G_n is eventually constant by step 4, so its first derived
   inverse limit is zero. The right inverse limit is zero by the bounded case.
   The Milnor exact sequence gives Hom(C,L) = 0, proving (6.4) with no lower bound.
6. (lem-sf-derived-truncation-triangle, sk-cor-ambient-ind-derived,
   lem-weil-pbc-hom-into-triangle-exact, def-kun-truncations) Put V = tau_le(-d_C-1) A,
   B = tau_ge(-d_C) A. In V --> A --> B, (6.4) kills Hom(C,V) and Hom(C,V[1]), so
   b_K: Hom(C,A) --> Hom(C,B) is bijective. The equivalence is b_K a_K^(-1); the first
   equation in FiniteWindowAssertions says e(a(f)) = b(f). Functorial truncation gives
   F a_K = a_L F_A and F_B b_K = b_L F_A, hence F_B b_K a_K^(-1) = b_L a_L^(-1) F: the
   naturality equation in FiniteWindowAssertions. Undoing the shift yields (6.3). -/
theorem finiteWindow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X)
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (m : ℤ) :
    FiniteWindowAssertions C (fun K ↦ ∀ q : ℤ,
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by
  let P := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
  have : P.ContainsZero :=
    ⟨HasZeroObject.zero.choose, isZero_zero _,
    ObjectProperty.le_ind _ _
      (constantModelConstructible_of_isZero _ X _ (isZero_zero _))⟩
  exact finiteWindow_of_lowerTail C P d_C m
    (fun L hL hv ↦ finiteWindow_unbounded_padicAlgCl ℓ X C hC d_C hExt L hL hv)

end AlgebraicGeometry.ProEtale
