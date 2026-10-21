/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import Sheaf.Paper.FiniteWindowUnbounded
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# The finite cohomological window for constructible sources

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-finite-window,
statement and sk-lem-finite-window.proof.md (blueprint: sk-lem-finite-window).

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

-- Step 1: use the identity cover and the zero finitely presented condensed module.
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
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)


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
Source: blueprint main-20261015, sk-lem-finite-window, statement and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the four DAG steps:
1. Put A = tau_le(m) K, U = tau_ge(m+1) K, V = tau_le(m-d_C-1) A,
   B = tau_ge(m-d_C) A. The canonical triangles A --> K --> U and V --> A --> B
   are distinguished (lem-sf-derived-truncation-triangle). Good truncation cohomology
   formulas (def-kun-truncations) keep A,V and their shifts in Dic: each cohomology
   sheaf is a cohomology sheaf of K or zero, and zero is constructible.
2. The standard t-structure (def-sbc-standard-tstructure-derived-category) and its
   orthogonality (def-weil-t-structure) kill Hom(C,U[m]) and Hom(C,U[m-1]). Applying
   representable Hom exactness (lem-weil-pbc-hom-into-triangle-exact) to the first
   triangle and its rotations makes a: Hom(C,A[m]) --> Hom(C,K[m]) bijective.
3. V[m] and V[m+1] have cohomology zero above -d_C-1 and -d_C-2 respectively.
   det-finite-window-unbounded kills Hom from C to both, without any lower bound.
   Representable Hom exactness for the second triangle and its rotations makes
   b: Hom(C,A[m]) --> Hom(C,B[m]) bijective.
4. The additive equivalence is b composed with the inverse of a; the first equation
   in FiniteWindowAssertions says e(a(f))=b(f). For K --> L, functoriality
   of the canonical truncations
   gives F a_K = a_L F_A and F_B b_K = b_L F_A. Consequently
   F_B b_K a_K^(-1) = b_L a_L^(-1) F. This is the naturality equation
   in FiniteWindowAssertions. -/
theorem finiteWindow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u})
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

/-- The truncation zigzag induces a natural additive equivalence on Hom from C,
for the condensed algebraic closure with finite-subextension-valued sections.
The indexing subtype is the full object class Dic;
its morphisms below are all ambient derived morphisms.
Source: blueprint main-20261015, sk-lem-finite-window, statement and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the four DAG steps:
1. Put A = tau_le(m) K, U = tau_ge(m+1) K, V = tau_le(m-d_C-1) A,
   B = tau_ge(m-d_C) A. The canonical triangles A --> K --> U and V --> A --> B
   are distinguished (lem-sf-derived-truncation-triangle). Good truncation cohomology
   formulas (def-kun-truncations) keep A,V and their shifts in Dic: each cohomology
   sheaf is a cohomology sheaf of K or zero, and zero is constructible.
2. The standard t-structure (def-sbc-standard-tstructure-derived-category) and its
   orthogonality (def-weil-t-structure) kill Hom(C,U[m]) and Hom(C,U[m-1]). Applying
   representable Hom exactness (lem-weil-pbc-hom-into-triangle-exact) to the first
   triangle and its rotations makes a: Hom(C,A[m]) --> Hom(C,K[m]) bijective.
3. V[m] and V[m+1] have cohomology zero above -d_C-1 and -d_C-2 respectively.
   det-finite-window-unbounded kills Hom from C to both, without any lower bound.
   Representable Hom exactness for the second triangle and its rotations makes
   b: Hom(C,A[m]) --> Hom(C,B[m]) bijective.
4. The additive equivalence is b composed with the inverse of a; the first equation
   in FiniteWindowAssertions says e(a(f))=b(f). For K --> L, functoriality
   of the canonical truncations
   gives F a_K = a_L F_A and F_B b_K = b_L F_A. Consequently
   F_B b_K a_K^(-1) = b_L a_L^(-1) F. This is the naturality equation
   in FiniteWindowAssertions. -/
theorem finiteWindow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u})
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
