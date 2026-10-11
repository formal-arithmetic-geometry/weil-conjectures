/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale
public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import WeilConjectures.CategoryTheory.Sites.InjectiveCocycle
public import WeilConjectures.FieldTheory.CrossedProduct
public import WeilConjectures.RingTheory.TensorProduct.AmitsurGalois

/-!
# The cohomological Brauer group of a `C₁` field vanishes

Let `K` be a quasi-algebraically closed (`C₁`) field. We show `H²(Spec(K)_ét, 𝔾ₘ) = 0` directly,
without comparing `H²(Spec(K)_ét, 𝔾ₘ)` with the Brauer group of central simple algebras.

Embed `𝔾ₘ` into an injective sheaf `I` with cokernel `Q`. Then `H²(𝔾ₘ) ≅ H¹(Q)`, and `H¹(Q)`
vanishes as soon as for every short exact sequence `0 → Q → E → Q' → 0` global sections of `Q'`
lift to `E` (`CategoryTheory.Sheaf.subsingleton_H_one_of_surjective`). A global section `q` of
`Q'` lifts to a section `e` of `E` over `Spec L` for a finite Galois extension `L` of `K`. Its
obstruction to descend is the Čech `1`-cocycle `c = p₁^* e - p₂^* e` of `Q` on
`Spec (L ⊗_K L)`; then:

1. `c` lifts to a cochain `a` of `I` by Hilbert 90 over `Spec (L ⊗_K L)`
   (`AlgebraicGeometry.Scheme.surjective_app_of_shortExact_gmSheaf_of_compactSpace`);
2. the Čech differential of `a` is an Amitsur `2`-cocycle `u ∈ (L ⊗_K L ⊗_K L)ˣ` of `𝔾ₘ`;
3. `u` is a coboundary: it corresponds to a Galois `2`-cocycle of `Gal(L/K)` with values in
   `Lˣ` (`Algebra.TensorProduct.exists_eq_of_cocycle₂`), whose crossed product algebra is split
   since `K` is `C₁` (`IsQuasiAlgClosed.exists_mul_eq_of_galois_cocycle`);
4. after correcting `a` by this coboundary it is a Čech `1`-cocycle of the injective sheaf `I`,
   hence a coboundary (`CategoryTheory.Presheaf.exists_eq_sub_of_injective`), and the
   corresponding correction of `e` descends to a global section of `E` lifting `q`.

Čech cochains on the covering `Spec L → Spec K` are encoded, as in
`WeilConjectures.AlgebraicGeometry.Sites.Hilbert90`, as families of sections over all étale
`K`-schemes `Z` indexed by tuples of morphisms `Z ⟶ Spec L`, which factor uniquely through
`Spec (L ⊗_K ⋯ ⊗_K L)` (`AlgebraicGeometry.Scheme.etaleSpecLift`).

## Main statements

- `AlgebraicGeometry.Scheme.surjective_app_of_shortExact_of_shortExact_gmSheaf`: for
  `0 → 𝔾ₘ → I → Q → 0` exact with `I` injective and `0 → Q → E → Q' → 0` exact, global sections
  of `Q'` lift to `E`.
- `AlgebraicGeometry.Scheme.subsingleton_cohomologicalBrauerGroup_of_isQuasiAlgClosed`:
  `H²(Spec(K)_ét, 𝔾ₘ) = 0` for a `C₁` field `K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct Algebra.TensorProduct

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

/-- The terminal object `𝟙 : Spec K ⟶ Spec K` of the small étale site of `Spec K`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))

section Factor

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [Algebra.Etale K A] [Algebra.Etale K B]

/-- A pair of morphisms `Z ⟶ Spec A` and `Z ⟶ Spec B` in the small étale site of `Spec K`
factors through `Spec (A ⊗_K B)`, the fibre product `Spec A ×_{Spec K} Spec B`. -/
lemma exists_comp_etaleSpecMap_includeLeft_eq_and {Z : (Spec (.of K)).Etale}
    (g₁ : Z ⟶ etaleSpec K A) (g₂ : Z ⟶ etaleSpec K B) :
    ∃ h : Z ⟶ etaleSpec K (A ⊗[K] B),
      h ≫ etaleSpecMap includeLeft = g₁ ∧ h ≫ etaleSpecMap includeRight = g₂ := by
  have w : g₁.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      g₂.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) :=
    (MorphismProperty.Over.w g₁).trans (MorphismProperty.Over.w g₂).symm
  have hfst : (pullbackSpecIso K A B).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := K) (S := K)
        (A := A) (B := B)).toRingHom) = pullback.fst _ _ :=
    pullbackSpecIso_hom_fst K A B
  have hsnd : (pullbackSpecIso K A B).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K)
        (A := A) (B := B)).toRingHom) = pullback.snd _ _ :=
    pullbackSpecIso_hom_snd K A B
  refine ⟨MorphismProperty.Over.homMk (pullback.lift _ _ w ≫ (pullbackSpecIso K A B).hom) ?_,
    ?_, ?_⟩
  · have : (etaleSpec K (A ⊗[K] B)).hom = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := B)).toRingHom) ≫
          (etaleSpec K A).hom := by
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
    rw [this, Category.assoc, reassoc_of% hfst, ← Category.assoc, pullback.lift_fst]
    exact MorphismProperty.Over.w g₁
  · apply MorphismProperty.Over.Hom.ext
    change (_ ≫ _) ≫ Spec.map _ = _
    rw [Category.assoc, hfst, pullback.lift_fst]
  · apply MorphismProperty.Over.Hom.ext
    change (_ ≫ _) ≫ Spec.map _ = _
    rw [Category.assoc, hsnd, pullback.lift_snd]

/-- Two morphisms into `Spec (A ⊗_K B)` agree if they agree after composing with the two
projections to `Spec A` and `Spec B`. -/
lemma etaleSpec_tensorProduct_hom_ext {Z : (Spec (.of K)).Etale}
    {h h' : Z ⟶ etaleSpec K (A ⊗[K] B)}
    (h₁ : h ≫ etaleSpecMap includeLeft = h' ≫ etaleSpecMap includeLeft)
    (h₂ : h ≫ etaleSpecMap includeRight = h' ≫ etaleSpecMap includeRight) : h = h' := by
  apply MorphismProperty.Over.Hom.ext
  have h₁' : h.left ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := B)).toRingHom) =
      h'.left ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := B)).toRingHom) :=
    congrArg (fun φ ↦ φ.left) h₁
  have h₂' : h.left ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := B)).toRingHom) =
      h'.left ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := B)).toRingHom) :=
    congrArg (fun φ ↦ φ.left) h₂
  rw [← cancel_mono (pullbackSpecIso K A B).inv]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_fst]
    exact h₁'
  · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_snd]
    exact h₂'

variable {Z : (Spec (.of K)).Etale}

/-- The morphism `Z ⟶ Spec (A ⊗_K B)` with components `g₁ : Z ⟶ Spec A` and `g₂ : Z ⟶ Spec B`.
-/
noncomputable def etaleSpecLift (g₁ : Z ⟶ etaleSpec K A) (g₂ : Z ⟶ etaleSpec K B) :
    Z ⟶ etaleSpec K (A ⊗[K] B) :=
  (exists_comp_etaleSpecMap_includeLeft_eq_and g₁ g₂).choose

@[reassoc (attr := simp)]
lemma etaleSpecLift_fst (g₁ : Z ⟶ etaleSpec K A) (g₂ : Z ⟶ etaleSpec K B) :
    etaleSpecLift g₁ g₂ ≫ etaleSpecMap includeLeft = g₁ :=
  (exists_comp_etaleSpecMap_includeLeft_eq_and g₁ g₂).choose_spec.1

@[reassoc (attr := simp)]
lemma etaleSpecLift_snd (g₁ : Z ⟶ etaleSpec K A) (g₂ : Z ⟶ etaleSpec K B) :
    etaleSpecLift g₁ g₂ ≫ etaleSpecMap includeRight = g₂ :=
  (exists_comp_etaleSpecMap_includeLeft_eq_and g₁ g₂).choose_spec.2

lemma eq_etaleSpecLift (k : Z ⟶ etaleSpec K (A ⊗[K] B)) :
    k = etaleSpecLift (k ≫ etaleSpecMap includeLeft) (k ≫ etaleSpecMap includeRight) :=
  etaleSpec_tensorProduct_hom_ext (by simp) (by simp)

lemma comp_etaleSpecLift {Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ : Z ⟶ etaleSpec K A)
    (g₂ : Z ⟶ etaleSpec K B) : h ≫ etaleSpecLift g₁ g₂ = etaleSpecLift (h ≫ g₁) (h ≫ g₂) :=
  etaleSpec_tensorProduct_hom_ext (by simp) (by simp)

end Factor


section Galois

variable (K) in
/-- A finite separable field extension `L` of `K` embeds into a finite Galois extension `M` of
`K`, for instance its normal closure in an algebraic closure. -/
lemma exists_isGalois_algHom (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L] :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra K M) (_ : Algebra.Etale K M) (_ : IsGalois K M),
      Nonempty (L →ₐ[K] M) := by
  have : FiniteDimensional K L := Algebra.FormallyUnramified.finite_of_free K L
  have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  let Ω := AlgebraicClosure L
  let M := IntermediateField.normalClosure K L Ω
  have : Algebra.IsSeparable K M := by
    have (f : L →ₐ[K] Ω) : Algebra.IsSeparable K f.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
    change Algebra.IsSeparable K ↥(⨆ f : L →ₐ[K] Ω, f.fieldRange)
    infer_instance
  have : IsGalois K M := ⟨⟩
  have : Algebra.Etale K M :=
    ⟨Algebra.FormallyEtale.of_isSeparable K M, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨IsScalarTower.toAlgHom K L M⟩⟩

end Galois

section Descent

variable {I Q E Q' : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}}
  (ι : (Spec (.of K)).gmSheaf ⟶ I) (ρ : I ⟶ Q) (w₁ : ι ≫ ρ = 0)
  (hS₁ : (ShortComplex.mk ι ρ w₁).ShortExact)
  (κ : Q ⟶ E) (π : E ⟶ Q') (w₂ : κ ≫ π = 0) (hS₂ : (ShortComplex.mk κ π w₂).ShortExact)

include hS₁ hS₂ in
/-- **Descent of a lift along a Galois covering `Spec L → Spec K`, `K` a `C₁` field.** Let
`0 → 𝔾ₘ → I → Q → 0` be exact with `I` injective and `0 → Q → E → Q' → 0` exact. If a global
section `q` of `Q'` lifts to a section `e` of `E` over `Spec L`, for `L` a finite Galois
extension of `K`, then `q` lifts to a global section of `E`. See the module docstring for the
outline. -/
theorem exists_app_eq_of_app_etaleSpec_eq_of_isGalois [IsQuasiAlgClosed K] [Injective I]
    (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L] [IsGalois K L]
    (f : etaleSpec K L ⟶ 𝟙ₑ) (q : Q'.obj.obj (op 𝟙ₑ)) (e : E.obj.obj (op (etaleSpec K L)))
    (he : π.hom.app _ e = Q'.obj.map f.op q) :
    ∃ x, π.hom.app (op 𝟙ₑ) x = q := by
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  have : FiniteDimensional K L := Algebra.FormallyUnramified.finite_of_free K L
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  -- sectionwise exactness of the two short exact sequences
  have hι : ∀ W, Function.Injective (ι.hom.app W) := Sheaf.injective_app_f hS₁
  have hρ : ∀ W x, ρ.hom.app W x = 0 → ∃ y, ι.hom.app W y = x := Sheaf.exists_app_f_eq hS₁
  have hκ : ∀ W, Function.Injective (κ.hom.app W) := Sheaf.injective_app_f hS₂
  have hπ : ∀ W x, π.hom.app W x = 0 → ∃ y, κ.hom.app W y = x := Sheaf.exists_app_f_eq hS₂
  have hιρ : ∀ W x, ρ.hom.app W (ι.hom.app W x) = 0 :=
    Sheaf.app_g_app_f (S := ShortComplex.mk ι ρ w₁)
  have hκπ : ∀ W x, π.hom.app W (κ.hom.app W x) = 0 :=
    Sheaf.app_g_app_f (S := ShortComplex.mk κ π w₂)
  -- Step 1: the Čech `1`-cocycle `c` of `Q` measuring the failure of `e` to descend
  have hπe {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L) :
      π.hom.app _ (E.obj.map g₁.op e - E.obj.map g₂.op e) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, he,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, hT.hom_ext (g₁ ≫ f) (g₂ ≫ f), sub_self]
  choose c hc using fun (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) ↦
    hπ _ _ (hπe g₁ g₂)
  have hc_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      Q.obj.map h.op (c Z g₁ g₂) = c Z' (h ≫ g₁) (h ≫ g₂) := by
    apply hκ
    rw [NatTrans.naturality_apply, hc, hc, map_sub, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
      ← op_comp]
  have hc_add {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      c Z g₁ g₃ = c Z g₁ g₂ + c Z g₂ g₃ := by
    apply hκ
    rw [map_add, hc, hc, hc]
    abel
  -- Step 2: lift `c` to a cochain `a` of `I`, by Hilbert 90 over `Spec (L ⊗_K L)`
  let i₁ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeLeft
  let i₂ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeRight
  have : CompactSpace (etaleSpec K (L ⊗[K] L)).left :=
    inferInstanceAs (CompactSpace (Spec (.of (L ⊗[K] L))))
  obtain ⟨a₀, ha₀⟩ := surjective_app_of_shortExact_gmSheaf_of_compactSpace ι ρ w₁ hS₁
    (etaleSpec K (L ⊗[K] L)) (c _ i₁ i₂)
  let a (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) : I.obj.obj (op Z) :=
    I.obj.map (etaleSpecLift g₁ g₂).op a₀
  have ha_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      I.obj.map h.op (a Z g₁ g₂) = a Z' (h ≫ g₁) (h ≫ g₂) := by
    simp only [a, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      comp_etaleSpecLift]
  have hρa {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L) :
      ρ.hom.app _ (a Z g₁ g₂) = c Z g₁ g₂ := by
    rw [NatTrans.naturality_apply, ha₀, hc_map, etaleSpecLift_fst, etaleSpecLift_snd]
  -- Step 3: the Čech differential of `a` is a `2`-cocycle `b` of `𝔾ₘ`
  have hβ {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      ρ.hom.app _ (a Z g₁ g₂ - a Z g₁ g₃ + a Z g₂ g₃) = 0 := by
    rw [map_add, map_sub, hρa, hρa, hρa, hc_add g₁ g₂ g₃]
    abel
  choose b hb using fun (Z : (Spec (.of K)).Etale) (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) ↦
    hρ _ _ (hβ g₁ g₂ g₃)
  have hb_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      (Spec (.of K)).gmSheaf.obj.map h.op (b Z g₁ g₂ g₃) = b Z' (h ≫ g₁) (h ≫ g₂) (h ≫ g₃) := by
    apply hι
    rw [NatTrans.naturality_apply, hb, hb, map_add, map_sub, ha_map, ha_map, ha_map]
  have hb_coc {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ g₄ : Z ⟶ etaleSpec K L) :
      b Z g₂ g₃ g₄ - b Z g₁ g₃ g₄ + b Z g₁ g₂ g₄ - b Z g₁ g₂ g₃ = 0 := by
    apply hι
    rw [map_zero, map_sub, map_add, map_sub, hb, hb, hb, hb]
    abel
  -- Step 4: the universal `2`-cocycle `b₀` over `Spec (L ⊗_K L ⊗_K L)` and its unit `u`
  let s₂ : L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
    (includeRight : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L)).comp includeLeft
  let s₃ : L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
    (includeRight : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L)).comp includeRight
  let p₁ : etaleSpec K (L ⊗[K] (L ⊗[K] L)) ⟶ etaleSpec K L := etaleSpecMap includeLeft
  let p₂ : etaleSpec K (L ⊗[K] (L ⊗[K] L)) ⟶ etaleSpec K L := etaleSpecMap s₂
  let p₃ : etaleSpec K (L ⊗[K] (L ⊗[K] L)) ⟶ etaleSpec K L := etaleSpecMap s₃
  let b₀ := b _ p₁ p₂ p₃
  let u : (L ⊗[K] (L ⊗[K] L))ˣ := (gmSheafEtaleSpecEquiv _ b₀).toMul
  have hG (δ : L ⊗[K] (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L))) :
      ((gmSheafEtaleSpecEquiv _
        ((Spec (.of K)).gmSheaf.obj.map (etaleSpecMap δ).op b₀)).toMul :
          L ⊗[K] (L ⊗[K] (L ⊗[K] L))) = δ (u : L ⊗[K] (L ⊗[K] L)) := by
    rw [gmSheafEtaleSpecEquiv_map]
    rfl
  have hb₀ (δ : L ⊗[K] (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L))) :
      (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap δ).op b₀ =
        b _ (etaleSpecMap (δ.comp includeLeft)) (etaleSpecMap (δ.comp s₂))
          (etaleSpecMap (δ.comp s₃)) := by
    rw [hb_map]
    simp only [p₁, p₂, p₃, etaleSpecMap_comp]
  -- the cofaces `L ⊗ L ⊗ L → L ⊗ L ⊗ L ⊗ L` and the cocycle identity for `u`
  let r : L ⊗[K] (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L)) := includeRight
  let δ₁ : L ⊗[K] (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L)) :=
    Algebra.TensorProduct.map (AlgHom.id K L) includeRight
  let δ₂ : L ⊗[K] (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L)) :=
    Algebra.TensorProduct.map (AlgHom.id K L) (Algebra.TensorProduct.map (AlgHom.id K L)
      includeRight)
  let δ₃ : L ⊗[K] (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L)) :=
    Algebra.TensorProduct.map (AlgHom.id K L) (Algebra.TensorProduct.map (AlgHom.id K L)
      includeLeft)
  have hu : r (u : L ⊗[K] (L ⊗[K] L)) * δ₂ (u : L ⊗[K] (L ⊗[K] L)) =
      δ₁ (u : L ⊗[K] (L ⊗[K] L)) * δ₃ (u : L ⊗[K] (L ⊗[K] L)) := by
    have h := hb_coc (Z := etaleSpec K (L ⊗[K] (L ⊗[K] (L ⊗[K] L)))) (etaleSpecMap includeLeft)
      (etaleSpecMap (r.comp includeLeft)) (etaleSpecMap (r.comp s₂)) (etaleSpecMap (r.comp s₃))
    have e₁ : (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap δ₁).op b₀ =
        b _ (etaleSpecMap includeLeft) (etaleSpecMap (r.comp s₂)) (etaleSpecMap (r.comp s₃)) := by
      rw [hb₀]
      congr 1
    have e₂ : (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap δ₂).op b₀ =
        b _ (etaleSpecMap includeLeft) (etaleSpecMap (r.comp includeLeft))
          (etaleSpecMap (r.comp s₃)) := by
      rw [hb₀]
      congr 1
    have e₃ : (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap δ₃).op b₀ =
        b _ (etaleSpecMap includeLeft) (etaleSpecMap (r.comp includeLeft))
          (etaleSpecMap (r.comp s₂)) := by
      rw [hb₀]
      congr 1
    rw [← hb₀ r, ← e₁, ← e₂, ← e₃] at h
    have h' := congrArg (fun x ↦ (gmSheafEtaleSpecEquiv _ x).toMul) h
    simp only [map_sub, map_add, map_zero, toMul_sub, toMul_add, toMul_zero] at h'
    rw [div_mul_eq_mul_div, div_div, div_eq_one] at h'
    have h'' := congrArg Units.val h'
    simp only [Units.val_mul] at h''
    rwa [hG, hG, hG, hG] at h''
  -- Step 5: `u` is an Amitsur coboundary, since `H²(Gal(L/K), Lˣ) = 0`
  obtain ⟨v, hv⟩ := Algebra.TensorProduct.exists_eq_of_cocycle₂
    (IsQuasiAlgClosed.exists_mul_eq_of_galois_cocycle K L) u hu
  let v₀ : (Spec (.of K)).gmSheaf.obj.obj (op (etaleSpec K (L ⊗[K] L))) :=
    (gmSheafEtaleSpecEquiv (L ⊗[K] L)).symm (Additive.ofMul v)
  let vZ (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      (Spec (.of K)).gmSheaf.obj.obj (op Z) :=
    (Spec (.of K)).gmSheaf.obj.map (etaleSpecLift g₁ g₂).op v₀
  have hv_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      (Spec (.of K)).gmSheaf.obj.map h.op (vZ Z g₁ g₂) = vZ Z' (h ≫ g₁) (h ≫ g₂) := by
    simp only [vZ, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      comp_etaleSpecLift]
  let d₁₂ : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
    Algebra.TensorProduct.map (AlgHom.id K L) includeLeft
  let d₁₃ : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
    Algebra.TensorProduct.map (AlgHom.id K L) includeRight
  let d₂₃ : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L) := includeRight
  have hb₀v : b₀ = (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap d₁₂).op v₀ -
      (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap d₁₃).op v₀ +
      (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap d₂₃).op v₀ := by
    apply (gmSheafEtaleSpecEquiv (L ⊗[K] (L ⊗[K] L))).injective
    simp only [map_add, map_sub, gmSheafEtaleSpecEquiv_map, v₀, AddEquiv.apply_symm_apply,
      toMul_ofMul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_sub, toMul_ofMul, toMul_ofMul, toMul_ofMul]
    apply Units.ext
    change (u : L ⊗[K] (L ⊗[K] L)) = _
    rw [div_eq_mul_inv, ← map_inv, Units.val_mul, Units.val_mul, Units.coe_map,
      Units.coe_map, Units.coe_map, hv]
    change _ = Algebra.TensorProduct.map (AlgHom.id K L) includeLeft (v : L ⊗[K] L) *
      Algebra.TensorProduct.map (AlgHom.id K L) includeRight (↑v⁻¹ : L ⊗[K] L) *
      (includeRight : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L)) (v : L ⊗[K] L)
    ring
  let p₂₃ : etaleSpec K (L ⊗[K] (L ⊗[K] L)) ⟶ etaleSpec K (L ⊗[K] L) :=
    etaleSpecMap includeRight
  have hbv {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      b Z g₁ g₂ g₃ = vZ Z g₁ g₂ - vZ Z g₁ g₃ + vZ Z g₂ g₃ := by
    let t := etaleSpecLift g₁ (etaleSpecLift g₂ g₃)
    have hS {φ ψ : L →ₐ[K] L ⊗[K] (L ⊗[K] L)} (h : φ = ψ) :
        etaleSpecMap φ = etaleSpecMap ψ := h ▸ rfl
    have ht₁ : t ≫ p₁ = g₁ := etaleSpecLift_fst _ _
    have ht₂ : t ≫ p₂ = g₂ := by
      simp only [t, p₂, s₂, ← etaleSpecMap_comp, etaleSpecLift_snd_assoc, etaleSpecLift_fst]
    have ht₃ : t ≫ p₃ = g₃ := by
      simp only [t, p₃, s₃, ← etaleSpecMap_comp, etaleSpecLift_snd_assoc, etaleSpecLift_snd]
    have h₁₂ : t ≫ etaleSpecMap d₁₂ = etaleSpecLift g₁ g₂ := by
      refine etaleSpec_tensorProduct_hom_ext ?_ ?_
      · rw [Category.assoc, etaleSpecMap_comp, etaleSpecLift_fst, ← ht₁]
        exact congrArg _ (hS (by ext x; rfl))
      · rw [Category.assoc, etaleSpecMap_comp, etaleSpecLift_snd, ← ht₂]
        exact congrArg _ (hS (by ext x; rfl))
    have h₁₃ : t ≫ etaleSpecMap d₁₃ = etaleSpecLift g₁ g₃ := by
      refine etaleSpec_tensorProduct_hom_ext ?_ ?_
      · rw [Category.assoc, etaleSpecMap_comp, etaleSpecLift_fst, ← ht₁]
        exact congrArg _ (hS (by ext x; rfl))
      · rw [Category.assoc, etaleSpecMap_comp, etaleSpecLift_snd, ← ht₃]
        exact congrArg _ (hS (by ext x; rfl))
    have h₂₃ : t ≫ etaleSpecMap d₂₃ = etaleSpecLift g₂ g₃ := by
      refine etaleSpec_tensorProduct_hom_ext ?_ ?_
      · rw [Category.assoc, etaleSpecMap_comp, etaleSpecLift_fst, ← ht₂]
      · rw [Category.assoc, etaleSpecMap_comp, etaleSpecLift_snd, ← ht₃]
    calc b Z g₁ g₂ g₃ = b Z (t ≫ p₁) (t ≫ p₂) (t ≫ p₃) := by rw [ht₁, ht₂, ht₃]
      _ = (Spec (.of K)).gmSheaf.obj.map t.op b₀ := (hb_map t p₁ p₂ p₃).symm
      _ = vZ Z g₁ g₂ - vZ Z g₁ g₃ + vZ Z g₂ g₃ := by
        rw [hb₀v, map_add, map_sub]
        simp only [vZ, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h₁₂, h₁₃,
          h₂₃]
  -- Step 6: the corrected cochain `a'` of `I` is a cocycle, hence a coboundary
  let a' (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) : I.obj.obj (op Z) :=
    a Z g₁ g₂ - ι.hom.app _ (vZ Z g₁ g₂)
  have ha'_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      I.obj.map h.op (a' Z g₁ g₂) = a' Z' (h ≫ g₁) (h ≫ g₂) := by
    simp only [a']
    rw [map_sub, ha_map, ← NatTrans.naturality_apply, hv_map]
  have ha'_coc (Z : (Spec (.of K)).Etale) (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      a' Z g₁ g₂ + a' Z g₂ g₃ = a' Z g₁ g₃ := by
    have h := hb Z g₁ g₂ g₃
    rw [hbv, map_add, map_sub] at h
    simp only [a']
    rw [← sub_eq_zero]
    calc a Z g₁ g₂ - ι.hom.app _ (vZ Z g₁ g₂) + (a Z g₂ g₃ - ι.hom.app _ (vZ Z g₂ g₃)) -
          (a Z g₁ g₃ - ι.hom.app _ (vZ Z g₁ g₃)) =
          (a Z g₁ g₂ - a Z g₁ g₃ + a Z g₂ g₃) - (ι.hom.app _ (vZ Z g₁ g₂) -
            ι.hom.app _ (vZ Z g₁ g₃) + ι.hom.app _ (vZ Z g₂ g₃)) := by abel
      _ = 0 := by rw [h, sub_self]
  obtain ⟨wI, hwI⟩ := Presheaf.exists_eq_sub_of_injective (etaleSpec K L) I.obj a'
    (fun h g₁ g₂ ↦ ha'_map h g₁ g₂) ha'_coc
  -- Step 7: the corrected section `e'` descends
  let e' := e - κ.hom.app _ (ρ.hom.app _ wI)
  have he' : π.hom.app _ e' = Q'.obj.map f.op q := by
    simp only [e']
    rw [map_sub, hκπ, sub_zero, he]
  refine exists_app_eq_of_compatible π L f q e' he' fun {Z} g₁ g₂ ↦ ?_
  have hκρ (g : Z ⟶ etaleSpec K L) :
      E.obj.map g.op (κ.hom.app _ (ρ.hom.app _ wI)) =
        κ.hom.app _ (ρ.hom.app _ (I.obj.map g.op wI)) := by
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  rw [← sub_eq_zero]
  calc E.obj.map g₁.op e' - E.obj.map g₂.op e' =
        (E.obj.map g₁.op e - E.obj.map g₂.op e) -
          κ.hom.app _ (ρ.hom.app _ (I.obj.map g₁.op wI - I.obj.map g₂.op wI)) := by
        simp only [e', map_sub, hκρ]
        abel
    _ = κ.hom.app _ (c Z g₁ g₂) - κ.hom.app _ (ρ.hom.app _ (a' Z g₁ g₂)) := by
        rw [hc, hwI]
    _ = 0 := by
        simp only [a']
        rw [map_sub, hιρ, sub_zero, hρa, sub_self]

include hS₁ hS₂ in
/-- Let `0 → 𝔾ₘ → I → Q → 0` be a short exact sequence of abelian sheaves on the small étale
site of `Spec K`, with `I` injective, for a quasi-algebraically closed field `K`. Then for every
short exact sequence `0 → Q → E → Q' → 0`, global sections of `Q'` lift to `E`. -/
theorem surjective_app_of_shortExact_of_shortExact_gmSheaf [IsQuasiAlgClosed K] [Injective I] :
    Function.Surjective (π.hom.app (op 𝟙ₑ)) := by
  have := hS₂.epi_g
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) π).2 inferInstance
  intro q
  obtain ⟨L, _, _, _, f, e, he⟩ := exists_etaleSpec_field_mem_of_mem_smallEtaleTopology _
    (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology π.hom (U := op 𝟙ₑ) q)
  obtain ⟨M, _, _, _, _, ⟨j⟩⟩ := exists_isGalois_algHom K L
  refine exists_app_eq_of_app_etaleSpec_eq_of_isGalois ι ρ w₁ hS₁ κ π w₂ hS₂ M
    (etaleSpecMap j ≫ f) q (E.obj.map (etaleSpecMap j).op e) ?_
  rw [NatTrans.naturality_apply, he, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end Descent

/-- **The cohomological Brauer group of a `C₁` field vanishes**: `H²(Spec(K)_ét, 𝔾ₘ) = 0` for a
quasi-algebraically closed field `K`.

Embed `𝔾ₘ` into an injective sheaf `I` with cokernel `Q`; then `H²(𝔾ₘ) ≅ H¹(Q)`, and `H¹(Q)`
vanishes by `AlgebraicGeometry.Scheme.surjective_app_of_shortExact_of_shortExact_gmSheaf`.
(blueprint: `lem-sc-c1-brauer-trivial`, with `Br(K) = H²(K, 𝔾ₘ)`) -/
theorem subsingleton_cohomologicalBrauerGroup_of_isQuasiAlgClosed [IsQuasiAlgClosed K] :
    Subsingleton (Spec (.of K)).CohomologicalBrauerGroup := by
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  let S := ShortComplex.mk (Injective.ι (Spec (.of K)).gmSheaf)
    (cokernel.π (Injective.ι (Spec (.of K)).gmSheaf)) (cokernel.condition _)
  have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have : Subsingleton (Sheaf.H S.X₃ 1) := Sheaf.subsingleton_H_one_of_surjective _ hT
    fun _ _ κ π w hS₂ ↦
      surjective_app_of_shortExact_of_shortExact_gmSheaf S.f S.g S.zero hS κ π w hS₂
  exact Sheaf.subsingleton_H_succ_of_comp_extClass hS 1 fun y ↦ by
    rw [Subsingleton.elim y 0, Abelian.Ext.zero_comp]

end AlgebraicGeometry.Scheme
