/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import WeilConjectures.AlgebraicGeometry.GeometricFiberFiniteEtale
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.WeilSheaf.FiniteEtale
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.VerdierDualLocalization

/-!
# The Verdier dual on a finite reduced scheme

Weil complexes carry the canonical t-structure of the derived category of pro-étale Weil
sheaves (`AlgebraicGeometry.WeilComplex.tStructure`), Weil complexes being stable under the
truncations.

On a finite reduced `k₀`-scheme `Z` (finite étale over `k₀`), every Weil sheaf is lisse, and
`Z` is smooth of dimension zero, so that the Verdier dual of a Weil sheaf placed in degree zero
is again a Weil sheaf placed in degree zero (`𝔻_Z G ≅ G^∨`). By dévissage the Verdier dual
`𝔻_Z` is t-exact: it carries complexes concentrated in degrees `[a, b]` to complexes
concentrated in degrees `[-b, -a]`. In particular `𝓗⁻¹(𝔻_Z A) ≅ (𝓗¹ A)^∨` for every Weil
complex `A` on `Z`, which is step 5 of the local boundary duality
(`lem-a1-local-boundary-duality`).

## Main statements

- `AlgebraicGeometry.WeilComplex.isGE_isLE_verdierDual_of_isFinite`: `𝔻_Z` is t-exact.
- `AlgebraicGeometry.WeilComplex.nonempty_homologySheaf_neg_one_verdierDual_iso`:
  `𝓗⁻¹(𝔻_Z A) ≅ (𝓗¹ A)^∨ ⊗ ℚ̄_ℓ(0) ⊗ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated Triangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- A finite reduced scheme over a perfect field is étale over it: it is the spectrum of a
finite reduced, hence étale, algebra (`Algebra.Etale.of_isReduced_of_perfectField`). -/
theorem etale_of_isFinite_of_isReduced {K : Type u} [Field K] [PerfectField K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [IsFinite f] [IsReduced Z] : Etale f := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  let φ₀ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  let : Algebra K Γ(Z, ⊤) := φ₀.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) :=
    RingHom.Finite.comp f.finite_appTop (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.Etale.of_isReduced_of_perfectField K Γ(Z, ⊤)
  have hf : f = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(Z, ⊤))) := by
    rw [← Iso.inv_comp_eq, ← Category.comp_id f, ← toSpecΓ_SpecMap_ΓSpecIso_inv,
      Scheme.toSpecΓ_naturality_assoc, Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp]
    rfl
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Z, ⊤)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  rw [hf]
  infer_instance

namespace WeilComplex

section TStructure

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Weil complexes are stable under the truncations of the canonical t-structure of the derived
category of pro-étale Weil sheaves: the truncations of a bounded complex are bounded, and their
cohomology objects are those of the complex or zero. -/
instance : (objectProperty k₀ l X).HasInducedTStructure _root_.DerivedCategory.TStructure.t :=
  .mk' fun K hK n ↦ by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncLE hc n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncGE hc n⟩⟩

variable (k₀ l X) in
/-- The canonical t-structure on Weil complexes, induced by the canonical t-structure of the
derived category of pro-étale Weil sheaves. -/
noncomputable def tStructure : TStructure (WeilComplex k₀ l X) :=
  (objectProperty k₀ l X).tStructure _root_.DerivedCategory.TStructure.t

lemma tStructure_isLE_iff (K : WeilComplex k₀ l X) (n : ℤ) :
    (tStructure k₀ l X).IsLE K n ↔ K.obj.IsLE n :=
  ObjectProperty.tStructure_isLE_iff _ _ K n

lemma tStructure_isGE_iff (K : WeilComplex k₀ l X) (n : ℤ) :
    (tStructure k₀ l X).IsGE K n ↔ K.obj.IsGE n :=
  ObjectProperty.tStructure_isGE_iff _ _ K n

instance (G : WeilSheaf k₀ l X) : (tStructure k₀ l X).IsLE (WeilSheaf.toComplex.obj G) 0 :=
  (tStructure_isLE_iff _ _).2
    (inferInstanceAs (((_root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
      G.obj).IsLE 0))

instance (G : WeilSheaf k₀ l X) : (tStructure k₀ l X).IsGE (WeilSheaf.toComplex.obj G) 0 :=
  (tStructure_isGE_iff _ _).2
    (inferInstanceAs (((_root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
      G.obj).IsGE 0))

/-- A Weil complex concentrated in degree `b` is its cohomology sheaf `𝓗ᵇ` placed in
degree `b`. -/
theorem nonempty_iso_shift_toComplex_homologySheaf (K : WeilComplex k₀ l X) (b : ℤ)
    [(tStructure k₀ l X).IsGE K b] [(tStructure k₀ l X).IsLE K b] :
    Nonempty (K ≅ (WeilSheaf.toComplex.obj ((homologySheaf b).obj K))⟦-b⟧) := by
  have : K.obj.IsGE b := (tStructure_isGE_iff _ _).1 inferInstance
  have : K.obj.IsLE b := (tStructure_isLE_iff _ _).1 inferInstance
  obtain ⟨A, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj b
  let eA : A ≅ ((homologySheaf b).obj K).obj :=
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app A).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ b).mapIso e.symm
  exact ⟨ObjectProperty.isoMk _ (e ≪≫ (_root_.DerivedCategory.singleFunctor _ b).mapIso eA ≪≫
    ((_root_.DerivedCategory.singleFunctors _).shiftIso (-b) b 0 (by lia)).symm.app _ ≪≫
    (((objectProperty k₀ l X).ι.commShiftIso (-b)).app
      (WeilSheaf.toComplex.obj ((homologySheaf b).obj K))).symm)⟩

end TStructure

section Finite

variable {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z]

open Pretriangulated.Opposite

/-- On a finite reduced `k₀`-scheme `Z`, the Verdier dual of a Weil sheaf `G` placed in degree
zero is the Weil sheaf `G^∨ ⊗ ℚ̄_ℓ(0) ⊗ ℚ̄_ℓ` placed in degree zero: `G` is lisse and `Z` is étale,
that is smooth of relative dimension zero, over `k₀`. -/
theorem nonempty_verdierDual_toComplex_iso_of_isFinite (G : WeilSheaf k₀ l Z) :
    Nonempty ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G)) ≅
      WeilSheaf.toComplex.obj ((G.dual (WeilSheaf.isLisse_of_isFinite_of_isReduced G)).tensorObj
        ((WeilSheaf.tateTwistSheaf k₀ l Z 0).tensorObj (WeilSheaf.adicConstant k₀ l Z)
          (WeilSheaf.isLisse_tateTwistSheaf k₀ l Z 0))
        (WeilSheaf.isLisse_of_isFinite_of_isReduced G).dual)) := by
  have : Etale (Z ↘ Spec (CommRingCat.of k₀)) :=
    etale_of_isFinite_of_isReduced (Z ↘ Spec (CommRingCat.of k₀))
  obtain ⟨e⟩ := nonempty_verdierDual_toComplex_iso_of_isLisse 0 G
    (WeilSheaf.isLisse_of_isFinite_of_isReduced G)
  exact ⟨e ≪≫ (shiftFunctorZero' _ (2 * (0 : ℕ) : ℤ) (by simp)).app _⟩

theorem isLE_verdierDual_toComplex (G : WeilSheaf k₀ l Z) :
    (tStructure k₀ l Z).IsLE ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G))) 0 :=
  (tStructure k₀ l Z).isLE_of_iso (nonempty_verdierDual_toComplex_iso_of_isFinite G).some.symm 0

theorem isGE_verdierDual_toComplex (G : WeilSheaf k₀ l Z) :
    (tStructure k₀ l Z).IsGE ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G))) 0 :=
  (tStructure k₀ l Z).isGE_of_iso (nonempty_verdierDual_toComplex_iso_of_isFinite G).some.symm 0


/-- The Verdier dual of a shift: `𝔻(Y[-b]) ≅ (𝔻 Y)[b]`. -/
noncomputable def verdierDualShiftIso [(verdierDual k₀ l Z).CommShift ℤ]
    (Y : WeilComplex k₀ l Z) (b : ℤ) :
    (verdierDual k₀ l Z).obj (op (Y⟦-b⟧)) ≅ ((verdierDual k₀ l Z).obj (op Y))⟦b⟧ :=
  (verdierDual k₀ l Z).mapIso
      ((shiftFunctorOpIso (WeilComplex k₀ l Z) b (-b) (by lia)).app (op Y)).symm ≪≫
    ((verdierDual k₀ l Z).commShiftIso b).app (op Y)

/-- The Verdier dual of a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` is a distinguished
triangle `𝔻 K₃ ⟶ 𝔻 K₂ ⟶ 𝔻 K₁ ⟶ 𝔻 K₃[1]`. -/
lemma verdierDual_mapTriangle_distinguished [(verdierDual k₀ l Z).CommShift ℤ]
    [(verdierDual k₀ l Z).IsTriangulated] (T : Triangle (WeilComplex k₀ l Z))
    (hT : T ∈ distTriang _) :
    (verdierDual k₀ l Z).mapTriangle.obj ((triangleOpEquivalence _).functor.obj (op T)) ∈
      distTriang _ :=
  (verdierDual k₀ l Z).map_distinguished _ (op_distinguished T hT)

/-- **Dévissage for the Verdier dual on a finite reduced scheme**: `𝔻_Z` carries Weil complexes
concentrated in degrees `[a, a + n - 1]` to Weil complexes concentrated in degrees
`[-(a + n - 1), -a]`, by induction on `n`, from the truncation triangles and
`𝔻_Z (G[0]) ≅ G^∨[0]`. -/
theorem isGE_isLE_verdierDual_of_isFinite (n : ℕ) : ∀ (a : ℤ) (K : WeilComplex k₀ l Z),
    (tStructure k₀ l Z).IsGE K a → (tStructure k₀ l Z).IsLE K (a + n - 1) →
    (tStructure k₀ l Z).IsGE ((verdierDual k₀ l Z).obj (op K)) (-(a + n - 1)) ∧
      (tStructure k₀ l Z).IsLE ((verdierDual k₀ l Z).obj (op K)) (-a) := by
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated_verdierDual k₀ l Z
  set t := tStructure k₀ l Z
  induction n with
  | zero =>
    intro a K _ hK
    have : t.IsLE K (a - 1) := t.isLE_of_le K (a + ((0 : ℕ) : ℤ) - 1) _ (by push_cast; lia)
    have hD : IsZero ((verdierDual k₀ l Z).obj (op K)) :=
      (verdierDual k₀ l Z).map_isZero (t.isZero K (a - 1) a (by lia)).op
    exact ⟨t.isGE_of_isZero hD _, t.isLE_of_isZero hD _⟩
  | succ n ih =>
    intro a K _ hK
    have : t.IsLE K (a + n) := t.isLE_of_le K (a + ((n + 1 : ℕ) : ℤ) - 1) _ (by push_cast; lia)
    set T := (t.triangleLEGE (a + n - 1) (a + n) (by lia)).obj K
    have hT : T ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ K
    have h₁ : t.IsGE T.obj₁ a := inferInstanceAs (t.IsGE ((t.truncLE (a + n - 1)).obj K) a)
    have h₁' : t.IsLE T.obj₁ (a + n - 1) :=
      inferInstanceAs (t.IsLE ((t.truncLE (a + n - 1)).obj K) (a + n - 1))
    obtain ⟨hD₁, hD₁'⟩ := ih a T.obj₁ h₁ h₁'
    have : t.IsGE T.obj₃ (a + n) := inferInstanceAs (t.IsGE ((t.truncGE (a + n)).obj K) (a + n))
    have : t.IsLE T.obj₃ (a + n) := inferInstanceAs (t.IsLE ((t.truncGE (a + n)).obj K) (a + n))
    obtain ⟨e⟩ := nonempty_iso_shift_toComplex_homologySheaf T.obj₃ (a + n)
    set G := (homologySheaf (a + n)).obj T.obj₃
    have := isLE_verdierDual_toComplex G
    have := isGE_verdierDual_toComplex G
    let e' : (verdierDual k₀ l Z).obj (op T.obj₃) ≅
        ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G)))⟦a + n⟧ :=
      (verdierDual k₀ l Z).mapIso e.symm.op ≪≫ verdierDualShiftIso _ _
    have h₃ : t.IsLE ((verdierDual k₀ l Z).obj (op T.obj₃)) (-(a + n)) := by
      have := t.isLE_shift ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G)))
        0 (a + n) (-(a + n)) (by lia)
      exact t.isLE_of_iso e'.symm _
    have h₃' : t.IsGE ((verdierDual k₀ l Z).obj (op T.obj₃)) (-(a + n)) := by
      have := t.isGE_shift ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G)))
        0 (a + n) (-(a + n)) (by lia)
      exact t.isGE_of_iso e'.symm _
    have hT' := verdierDual_mapTriangle_distinguished T hT
    refine ⟨?_, ?_⟩
    · have h₄ : t.IsGE ((verdierDual k₀ l Z).obj (op T.obj₁)) (-(a + n)) :=
        t.isGE_of_ge _ _ (-(a + n - 1)) (by lia)
      have : t.IsGE ((verdierDual k₀ l Z).obj (op K)) (-(a + n)) :=
        t.isGE₂ _ hT' (-(a + n)) h₃' h₄
      exact t.isGE_of_ge _ _ (-(a + n)) (by push_cast; lia)
    · have h₄ : t.IsLE ((verdierDual k₀ l Z).obj (op T.obj₃)) (-a) :=
        t.isLE_of_le _ (-(a + n)) _ (by lia)
      exact t.isLE₂ _ hT' (-a) h₄ hD₁'

/-- `𝔻_Z` carries Weil complexes in degrees `≤ n` to Weil complexes in degrees `≥ -n`. -/
theorem isGE_verdierDual_of_isLE (K : WeilComplex k₀ l Z) (n : ℤ)
    [(tStructure k₀ l Z).IsLE K n] :
    (tStructure k₀ l Z).IsGE ((verdierDual k₀ l Z).obj (op K)) (-n) := by
  obtain ⟨⟨⟨a, ha⟩, -⟩, -⟩ := K.property
  have : (tStructure k₀ l Z).IsGE K (min a n) := (tStructure_isGE_iff _ _).2
    (_root_.DerivedCategory.TStructure.t.isGE_of_ge K.obj (min a n) a (min_le_left _ _))
  have h := (isGE_isLE_verdierDual_of_isFinite (n - min a n + 1).toNat (min a n) K this
    ((tStructure k₀ l Z).isLE_of_le K n _ (by
      rw [Int.toNat_of_nonneg (by have := min_le_right a n; lia)]; lia))).1
  rwa [Int.toNat_of_nonneg (by have := min_le_right a n; lia),
    show min a n + (n - min a n + 1) - 1 = n by lia] at h

/-- `𝔻_Z` carries Weil complexes in degrees `≥ n` to Weil complexes in degrees `≤ -n`. -/
theorem isLE_verdierDual_of_isGE (K : WeilComplex k₀ l Z) (n : ℤ)
    [(tStructure k₀ l Z).IsGE K n] :
    (tStructure k₀ l Z).IsLE ((verdierDual k₀ l Z).obj (op K)) (-n) := by
  obtain ⟨⟨-, ⟨b, hb⟩⟩, -⟩ := K.property
  have : (tStructure k₀ l Z).IsLE K (max b n) := (tStructure_isLE_iff _ _).2
    (_root_.DerivedCategory.TStructure.t.isLE_of_le K.obj b (max b n) (le_max_left _ _))
  exact (isGE_isLE_verdierDual_of_isFinite (max b n - n + 1).toNat n K inferInstance
    ((tStructure k₀ l Z).isLE_of_le K (max b n) _ (by
      rw [Int.toNat_of_nonneg (by have := le_max_right b n; lia)]; lia))).2


omit [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z] in
lemma isZero_homologyFunctor_of_isGE (K : WeilComplex k₀ l Z) (n i : ℤ) (hi : i < n)
    (h : (tStructure k₀ l Z).IsGE K n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj) :=
  have := (tStructure_isGE_iff _ _).1 h
  _root_.DerivedCategory.isZero_of_isGE _ n i hi

omit [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z] in
lemma isZero_homologyFunctor_of_isLE (K : WeilComplex k₀ l Z) (n i : ℤ) (hi : n < i)
    (h : (tStructure k₀ l Z).IsLE K n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj) :=
  have := (tStructure_isLE_iff _ _).1 h
  _root_.DerivedCategory.isZero_of_isLE _ n i hi

/-- **`𝔻_Z` in degree `-1`** (blueprint: `lem-a1-local-boundary-duality`, step 5): on a finite
reduced `k₀`-scheme `Z`, `𝓗⁻¹(𝔻_Z A) ≅ 𝓗⁰(𝔻_Z (𝓗¹(A)[0]))` for every Weil complex `A`. The
truncation triangles `τ_{≤ 0} A ⟶ A ⟶ τ_{≥ 1} A ⟶` and
`τ_{≤ 1} τ_{≥ 1} A ⟶ τ_{≥ 1} A ⟶ τ_{≥ 2} τ_{≥ 1} A ⟶`, dualized, identify `𝓗⁻¹(𝔻_Z A)` with
`𝓗⁻¹(𝔻_Z(𝓗¹(A)[-1])) = 𝓗⁰(𝔻_Z(𝓗¹(A)[0]))`, `𝔻_Z` being t-exact. -/
theorem nonempty_homologySheaf_neg_one_verdierDual_iso (A : WeilComplex k₀ l Z) :
    Nonempty ((homologySheaf (-1)).obj ((verdierDual k₀ l Z).obj (op A)) ≅
      (homologySheaf 0).obj ((verdierDual k₀ l Z).obj
        (op (WeilSheaf.toComplex.obj ((homologySheaf 1).obj A))))) := by
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated_verdierDual k₀ l Z
  set t := tStructure k₀ l Z
  -- the truncation `τ_{≤ 0} A ⟶ A ⟶ B = τ_{≥ 1} A ⟶`
  set T₁ := (t.triangleLEGE 0 1 (by norm_num)).obj A
  have hT₁ : T₁ ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ A
  have h₁ : t.IsLE T₁.obj₁ 0 := inferInstanceAs (t.IsLE ((t.truncLE 0).obj A) 0)
  have : t.IsGE T₁.obj₃ 1 := inferInstanceAs (t.IsGE ((t.truncGE 1).obj A) 1)
  have hD₁ : t.IsGE ((verdierDual k₀ l Z).obj (op T₁.obj₁)) 0 := by
    simpa using isGE_verdierDual_of_isLE T₁.obj₁ 0
  have i₁ := _root_.DerivedCategory.isIso_homologyMap_mor₁ _
    ((objectProperty k₀ l Z).ι.map_distinguished _ (verdierDual_mapTriangle_distinguished T₁ hT₁)) (-2) (-1) (by norm_num)
    (isZero_homologyFunctor_of_isGE ((verdierDual k₀ l Z).obj (op T₁.obj₁)) 0 (-2) (by norm_num) hD₁)
    (isZero_homologyFunctor_of_isGE ((verdierDual k₀ l Z).obj (op T₁.obj₁)) 0 (-1) (by norm_num) hD₁)
  let E₁ : (homologySheaf (-1)).obj ((verdierDual k₀ l Z).obj (op T₁.obj₃)) ≅
      (homologySheaf (-1)).obj ((verdierDual k₀ l Z).obj (op A)) :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₁)
  -- the truncation `C = τ_{≤ 1} B ⟶ B ⟶ τ_{≥ 2} B ⟶`
  set T₂ := (t.triangleLEGE 1 2 (by norm_num)).obj T₁.obj₃
  have hT₂ : T₂ ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ _
  have : t.IsLE T₂.obj₁ 1 := inferInstanceAs (t.IsLE ((t.truncLE 1).obj T₁.obj₃) 1)
  have : t.IsGE T₂.obj₁ 1 := inferInstanceAs (t.IsGE ((t.truncLE 1).obj T₁.obj₃) 1)
  have h₃ : t.IsGE T₂.obj₃ 2 := inferInstanceAs (t.IsGE ((t.truncGE 2).obj T₁.obj₃) 2)
  have hD₃ : t.IsLE ((verdierDual k₀ l Z).obj (op T₂.obj₃)) (-2) := isLE_verdierDual_of_isGE T₂.obj₃ 2
  have i₂ := _root_.DerivedCategory.isIso_homologyMap_mor₂ _
    ((objectProperty k₀ l Z).ι.map_distinguished _ (verdierDual_mapTriangle_distinguished T₂ hT₂)) (-1) 0 (by norm_num)
    (isZero_homologyFunctor_of_isLE ((verdierDual k₀ l Z).obj (op T₂.obj₃)) (-2) (-1) (by norm_num) hD₃)
    (isZero_homologyFunctor_of_isLE ((verdierDual k₀ l Z).obj (op T₂.obj₃)) (-2) 0 (by norm_num) hD₃)
  let E₂ : (homologySheaf (-1)).obj ((verdierDual k₀ l Z).obj (op T₁.obj₃)) ≅
      (homologySheaf (-1)).obj ((verdierDual k₀ l Z).obj (op T₂.obj₁)) :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₂)
  -- `C ≅ 𝓗¹(C)[-1]`
  obtain ⟨e⟩ := nonempty_iso_shift_toComplex_homologySheaf T₂.obj₁ 1
  let E₃ : (homologySheaf (-1)).obj ((verdierDual k₀ l Z).obj (op T₂.obj₁)) ≅
      (homologySheaf 0).obj ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj
        ((homologySheaf 1).obj T₂.obj₁)))) :=
    (homologySheaf (-1)).mapIso ((verdierDual k₀ l Z).mapIso e.symm.op ≪≫ verdierDualShiftIso _ 1) ≪≫
      homologySheafShiftIso _ 1 (-1) 0 (by norm_num)
  -- `𝓗¹(C) ≅ 𝓗¹(B) ≅ 𝓗¹(A)`
  have i₃ := _root_.DerivedCategory.isIso_homologyMap_mor₁ _ ((objectProperty k₀ l Z).ι.map_distinguished _ hT₂) 0 1
    (by norm_num) (isZero_homologyFunctor_of_isGE T₂.obj₃ 2 0 (by norm_num) h₃)
    (isZero_homologyFunctor_of_isGE T₂.obj₃ 2 1 (by norm_num) h₃)
  have i₄ := _root_.DerivedCategory.isIso_homologyMap_mor₂ _ ((objectProperty k₀ l Z).ι.map_distinguished _ hT₁) 1 2
    (by norm_num) (isZero_homologyFunctor_of_isLE T₁.obj₁ 0 1 (by norm_num) h₁)
    (isZero_homologyFunctor_of_isLE T₁.obj₁ 0 2 (by norm_num) h₁)
  let e₃ : (homologySheaf 1).obj T₂.obj₁ ≅ (homologySheaf 1).obj T₁.obj₃ :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₃)
  let e₄ : (homologySheaf 1).obj A ≅ (homologySheaf 1).obj T₁.obj₃ :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₄)
  let eH : (homologySheaf 1).obj T₂.obj₁ ≅ (homologySheaf 1).obj A := e₃ ≪≫ e₄.symm
  exact ⟨E₁.symm ≪≫ E₂ ≪≫ E₃ ≪≫
    (homologySheaf 0).mapIso ((verdierDual k₀ l Z).mapIso (WeilSheaf.toComplex.mapIso eH.symm).op)⟩

end Finite

end WeilComplex

end AlgebraicGeometry
