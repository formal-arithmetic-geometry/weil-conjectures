/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.LinearAlgebra.TensorProduct.Kunneth
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Vanishing of `H¹` of a product of ideal sheaves

Let `X` and `Y` be quasi-compact separated schemes over a field `K`, and let `I ⊆ 𝒪_X`,
`I' ⊆ 𝒪_Y` be quasi-coherent ideals without nonzero global sections. On `X ×_K Y` the ideal
`J = pr_X⁻¹ I ⊓ pr_Y⁻¹ I'` is the external tensor product `I ⊠ I'`, and its first cohomology
vanishes: by the Künneth formula `H¹(X × Y, I ⊠ I') = H⁰(I) ⊗ H¹(I') ⊕ H¹(I) ⊗ H⁰(I')`.

The proof computes `H¹` by the Čech complex of a product of finite affine covers (Leray), on
which the sections of `J` over `U × V` are `I(U) ⊗_K I'(V)`, and applies the Künneth argument
`TensorProduct.exists_eq_rTensor_sub_and_eq_lTensor_sub`.

This is the input of Stacks, Tag 0BF2 used in the proof of the theorem of the cube.

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.subsingleton_H_one_toModules_comap_inf_comap`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.IdealSheafData

namespace Kunneth

variable {K : Type u} [Field K]

/-- The field `Γ(Spec K, ⊤)`. -/
noncomputable abbrev fieldΓ : Field Γ(Spec (.of K), ⊤) :=
  (isField_Γ_Spec (Field.toIsField K)).toField

/-- The sections of a scheme over `S` as an algebra over `Γ(S, ⊤)`. -/
noncomputable abbrev algebraOfOver {S Z : Scheme.{u}} [Z.Over S] (U : Z.Opens) :
    Algebra Γ(S, ⊤) Γ(Z, U) :=
  ((Z ↘ S).appLE ⊤ U le_top).hom.toAlgebra

/-- A fibre product of schemes over `S` is a scheme over `S`, through the first projection. -/
noncomputable abbrev overPullback {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] :
    (pullback (X ↘ S) (Y ↘ S)).Over S :=
  ⟨pullback.fst _ _ ≫ X ↘ S⟩

attribute [local instance] fieldΓ algebraOfOver overPullback

variable {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]

variable (K X Y) in
/-- The product `X ×_K Y`. -/
noncomputable abbrev prod : Scheme.{u} := pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))

variable (K X Y) in
/-- The first projection `X ×_K Y ⟶ X`. -/
noncomputable abbrev prodFst : prod K X Y ⟶ X := pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))

variable (K X Y) in
/-- The second projection `X ×_K Y ⟶ Y`. -/
noncomputable abbrev prodSnd : prod K X Y ⟶ Y := pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))

variable (K X Y) in
/-- The open `U × V = pr_X⁻¹ U ⊓ pr_Y⁻¹ V` of `X ×_K Y`. -/
noncomputable abbrev prodOpen (U : X.Opens) (V : Y.Opens) : (prod K X Y).Opens :=
  prodFst K X Y ⁻¹ᵁ U ⊓ prodSnd K X Y ⁻¹ᵁ V

/-- `Γ(X, U) → Γ(X ×_K Y, U × V)` as a map of `Γ(Spec K, ⊤)`-algebras. -/
noncomputable def fstAlgHom (U : X.Opens) (V : Y.Opens) :
    Γ(X, U) →ₐ[Γ(Spec (.of K), ⊤)] Γ(prod K X Y, prodOpen K X Y U V) where
  __ := ((prodFst K X Y).appLE U (prodOpen K X Y U V) inf_le_left).hom
  commutes' r := by
    change ((prodFst K X Y).appLE U _ _).hom ((X ↘ Spec (.of K)).appLE ⊤ U le_top r) =
      ((prodFst K X Y ≫ X ↘ Spec (.of K)).appLE ⊤ _ le_top) r
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- `Γ(Y, V) → Γ(X ×_K Y, U × V)` as a map of `Γ(Spec K, ⊤)`-algebras. -/
noncomputable def sndAlgHom (U : X.Opens) (V : Y.Opens) :
    Γ(Y, V) →ₐ[Γ(Spec (.of K), ⊤)] Γ(prod K X Y, prodOpen K X Y U V) where
  __ := ((prodSnd K X Y).appLE V (prodOpen K X Y U V) inf_le_right).hom
  commutes' r := by
    change ((prodSnd K X Y).appLE V _ _).hom ((Y ↘ Spec (.of K)).appLE ⊤ V le_top r) =
      ((prodFst K X Y ≫ X ↘ Spec (.of K)).appLE ⊤ _ le_top) r
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, pullback.condition]

/-- The multiplication map `Γ(X, U) ⊗ Γ(Y, V) → Γ(X ×_K Y, U × V)`. -/
noncomputable def mulAlgHom (U : X.Opens) (V : Y.Opens) :
    Γ(X, U) ⊗[Γ(Spec (.of K), ⊤)] Γ(Y, V) →ₐ[Γ(Spec (.of K), ⊤)]
      Γ(prod K X Y, prodOpen K X Y U V) :=
  Algebra.TensorProduct.lift (fstAlgHom U V) (sndAlgHom U V) fun _ _ ↦ Commute.all _ _

lemma mulAlgHom_tmul (U : X.Opens) (V : Y.Opens) (a : Γ(X, U)) (b : Γ(Y, V)) :
    mulAlgHom U V (a ⊗ₜ b) = (prodFst K X Y).appLE U (prodOpen K X Y U V) inf_le_left a *
      (prodSnd K X Y).appLE V (prodOpen K X Y U V) inf_le_right b :=
  rfl

/-- **Sections over a product of affine opens.** For affine opens `U ⊆ X` and `V ⊆ Y`,
`Γ(X ×_K Y, U × V) = Γ(X, U) ⊗_K Γ(Y, V)`. -/
lemma bijective_mulAlgHom {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : Function.Bijective (mulAlgHom (K := K) U V) := by
  set O := prodOpen K X Y U V
  let : Algebra Γ(X, U) Γ(prod K X Y, O) := (fstAlgHom (K := K) U V).toRingHom.toAlgebra
  let : Algebra Γ(Y, V) Γ(prod K X Y, O) := (sndAlgHom (K := K) U V).toRingHom.toAlgebra
  have : IsScalarTower Γ(Spec (.of K), ⊤) Γ(X, U) Γ(prod K X Y, O) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((fstAlgHom U V).commutes r).symm
  have : IsScalarTower Γ(Spec (.of K), ⊤) Γ(Y, V) Γ(prod K X Y, O) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((sndAlgHom U V).commutes r).symm
  have hpush : Algebra.IsPushout Γ(Spec (.of K), ⊤) Γ(X, U) Γ(Y, V) Γ(prod K X Y, O) := by
    have hiso := isIso_pushoutSection_of_isAffineOpen
      (IsPullback.of_hasPullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
      (le_top : V ≤ (Y ↘ Spec (.of K)) ⁻¹ᵁ ⊤) (le_top : U ≤ (X ↘ Spec (.of K)) ⁻¹ᵁ ⊤) (UY := O)
      rfl (isAffineOpen_top _) hV hU
    exact CommRingCat.isPushout_iff_isPushout.mp ((isIso_pushoutSection_iff ..).mp hiso)
  have h : ⇑(mulAlgHom (K := K) U V) =
      ⇑(Algebra.IsPushout.equiv Γ(Spec (.of K), ⊤) Γ(X, U) Γ(Y, V) Γ(prod K X Y, O)) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => rw [Algebra.IsPushout.equiv_tmul, mulAlgHom_tmul]; rfl
  rw [h]
  exact AlgEquiv.bijective _

/-- The ideal `I(U)` as a `Γ(Spec K, ⊤)`-submodule of `Γ(X, U)`. -/
noncomputable abbrev idealSub {Z : Scheme.{u}} [Z.Over (Spec (.of K))] (I : Z.IdealSheafData)
    (U : Z.Opens) : Submodule Γ(Spec (.of K), ⊤) Γ(Z, U) :=
  (I.idealOfOpens U).restrictScalars _

variable (I : X.IdealSheafData) (I' : Y.IdealSheafData)

/-- The multiplication map `I(U) ⊗ I'(V) → Γ(X ×_K Y, U × V)`. -/
noncomputable def mulIdeal (U : X.Opens) (V : Y.Opens) :
    idealSub (K := K) I U ⊗[Γ(Spec (.of K), ⊤)] idealSub (K := K) I' V →ₗ[Γ(Spec (.of K), ⊤)]
      Γ(prod K X Y, prodOpen K X Y U V) :=
  (mulAlgHom U V).toLinearMap ∘ₗ TensorProduct.map (idealSub I U).subtype (idealSub I' V).subtype

lemma mulIdeal_tmul (U : X.Opens) (V : Y.Opens) (a : idealSub (K := K) I U)
    (b : idealSub (K := K) I' V) :
    mulIdeal I I' U V (a ⊗ₜ b) = (prodFst K X Y).appLE U (prodOpen K X Y U V) inf_le_left a.1 *
      (prodSnd K X Y).appLE V (prodOpen K X Y U V) inf_le_right b.1 :=
  rfl

lemma injective_mulIdeal {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : Function.Injective (mulIdeal (K := K) I I' U V) :=
  (bijective_mulAlgHom hU hV).1.comp
    (TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective)

/-- The ideal sheaf `pr_X⁻¹ I ⊓ pr_Y⁻¹ I'` on `X ×_K Y`. -/
noncomputable abbrev prodIdeal : (prod K X Y).IdealSheafData :=
  I.comap (prodFst K X Y) ⊓ I'.comap (prodSnd K X Y)

/-- **Sections of `I ⊠ I'` over a product of affine opens.** For affine opens `U ⊆ X` and
`V ⊆ Y`, the sections of `pr_X⁻¹ I ⊓ pr_Y⁻¹ I'` over `U × V` are the image of
`I(U) ⊗_K I'(V)`. -/
lemma range_mulIdeal {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Set.range (mulIdeal (K := K) I I' U V) =
      ((prodIdeal (K := K) I I').idealOfOpens (prodOpen K X Y U V) : Set _) := by
  have hO : IsAffineOpen (prodOpen K X Y U V) :=
    isAffineOpen_preimage_inf_preimage_pullback _ _ hU hV
  rw [show prodIdeal (K := K) I I' = _ from rfl,
    idealOfOpens_eq_ideal _ ⟨prodOpen K X Y U V, hO⟩, ideal_inf, Pi.inf_apply,
    ideal_comap_appLE I (prodFst K X Y) ⟨U, hU⟩ _ inf_le_left,
    ideal_comap_appLE I' (prodSnd K X Y) ⟨V, hV⟩ _ inf_le_right,
    ← idealOfOpens_eq_ideal, ← idealOfOpens_eq_ideal]
  ext c
  constructor
  · rintro ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul a b =>
      rw [mulIdeal_tmul]
      exact ⟨Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ a.2),
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ b.2)⟩
  · intro hc
    exact Algebra.TensorProduct.exists_map_subtype_eq_of_mem_map_inf_map (fstAlgHom U V)
      (sndAlgHom U V) (bijective_mulAlgHom hU hV) _ _ hc

/-- Restriction of sections of an ideal sheaf, as a `Γ(Spec K, ⊤)`-linear map. -/
noncomputable def resIdeal {Z : Scheme.{u}} [Z.Over (Spec (.of K))] (I : Z.IdealSheafData)
    {U U' : Z.Opens} (h : U' ≤ U) :
    idealSub (K := K) I U →ₗ[Γ(Spec (.of K), ⊤)] idealSub (K := K) I U' where
  toFun a := ⟨Z.presheaf.map (homOfLE h).op a.1, by
    have := a.2
    change a.1 ∈ I.idealOfOpens U at this
    change _ ∈ I.idealOfOpens U'
    rw [mem_idealOfOpens_iff] at this ⊢
    rw [← CommRingCat.comp_apply, I.subschemeι.naturality, CommRingCat.comp_apply, this, map_zero]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext <| by
    change Z.presheaf.map _ ((Z ↘ Spec (.of K)).appLE ⊤ U le_top r * a.1) =
      (Z ↘ Spec (.of K)).appLE ⊤ U' le_top r * Z.presheaf.map _ a.1
    rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

@[simp]
lemma resIdeal_apply_coe {Z : Scheme.{u}} [Z.Over (Spec (.of K))] (I : Z.IdealSheafData)
    {U U' : Z.Opens} (h : U' ≤ U) (a : idealSub (K := K) I U) :
    (resIdeal I h a).1 = Z.presheaf.map (homOfLE h).op a.1 :=
  rfl

/-- The multiplication maps commute with restriction. -/
lemma map_mulIdeal {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (w : idealSub (K := K) I U ⊗[Γ(Spec (.of K), ⊤)] idealSub (K := K) I' V) :
    (prod K X Y).presheaf.map (homOfLE (inf_le_inf ((prodFst K X Y).preimage_mono hU)
      ((prodSnd K X Y).preimage_mono hV))).op (mulIdeal I I' U V w) =
      mulIdeal I I' U' V'
        (TensorProduct.map (resIdeal (K := K) I hU) (resIdeal (K := K) I' hV) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [TensorProduct.map_tmul, mulIdeal_tmul, mulIdeal_tmul, map_mul, resIdeal_apply_coe,
      resIdeal_apply_coe, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]

/-- An ideal sheaf without nonzero global sections has no nonzero compatible families of
sections over an open cover. -/
lemma eq_zero_of_compatible {Z : Scheme.{u}} [Z.Over (Spec (.of K))] (I : Z.IdealSheafData)
    (hI : ∀ s ∈ I.idealOfOpens ⊤, s = 0) {α : Type u} (U : α → Z.Opens) (hU : iSup U = ⊤)
    (f : ∀ a, idealSub (K := K) I (U a))
    (hf : ∀ a a', resIdeal (K := K) I (inf_le_right : U a ⊓ U a' ≤ U a') (f a') =
      resIdeal (K := K) I (inf_le_left : U a ⊓ U a' ≤ U a) (f a)) : f = 0 := by
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun a ↦ homOfLE le_top) hU.ge
    (fun a ↦ (f a).1) fun a a' ↦ (congrArg Subtype.val (hf a a')).symm
  have hg0 : g = 0 := by
    refine hI g ?_
    rw [mem_idealOfOpens_iff]
    refine I.subscheme.sheaf.eq_of_locally_eq' (fun a ↦ I.subschemeι ⁻¹ᵁ U a) ⊤
      (fun a ↦ homOfLE le_top) (fun x _ ↦ ?_) _ _ fun a ↦ ?_
    · obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ (I.subschemeι x)))
      exact Opens.mem_iSup.mpr ⟨a, ha⟩
    · change I.subscheme.presheaf.map _ (I.subschemeι.app ⊤ g) =
        I.subscheme.presheaf.map _ (0 : Γ(I.subscheme, ⊤))
      rw [map_zero, ← CommRingCat.comp_apply, show I.subschemeι.app ⊤ ≫
          I.subscheme.presheaf.map (homOfLE le_top).op = Z.presheaf.map
            (homOfLE (le_top : U a ≤ ⊤)).op ≫ I.subschemeι.app (U a) from
          (I.subschemeι.naturality _).symm, CommRingCat.comp_apply]
      have h1 := hg a
      have h2 := (f a).2
      change (f a).1 ∈ I.idealOfOpens (U a) at h2
      rw [mem_idealOfOpens_iff] at h2
      convert h2
      exact h1
  funext a
  refine Subtype.ext ?_
  rw [← hg a, hg0, map_zero]
  rfl

@[simp]
lemma resIdeal_self {Z : Scheme.{u}} [Z.Over (Spec (.of K))] (I : Z.IdealSheafData)
    (U : Z.Opens) : resIdeal (K := K) I (le_refl U) = LinearMap.id := by
  ext a
  change Z.presheaf.map (homOfLE (le_refl U)).op a.1 = a.1
  rw [show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restrictions along two inclusions between equal opens are inverse to each other. -/
lemma eq_of_presheaf_map_eq {Z : Scheme.{u}} {O₁ O₂ : Z.Opens} (h : O₂ = O₁) {s t : Γ(Z, O₁)}
    (hst : Z.presheaf.map (homOfLE h.le).op s = Z.presheaf.map (homOfLE h.le).op t) : s = t := by
  have key (x : Γ(Z, O₁)) : Z.presheaf.map (homOfLE h.ge).op
      (Z.presheaf.map (homOfLE h.le).op x) = x := by
    rw [Scheme.presheaf_map_homOfLE_map_homOfLE_apply]
    rw [show homOfLE (h.ge.trans h.le) = 𝟙 O₁ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← key s, ← key t, hst]


set_option maxHeartbeats 1600000 in
-- the proof checks many index cases of the Čech cocycle condition
/-- **The Künneth argument on Čech cochains.** Let `U` and `V` be finite affine open covers
of `X` and `Y`, with affine pairwise intersections. If `I` and `I'` have no nonzero global
sections, the Čech complex of `pr_X⁻¹ I ⊓ pr_Y⁻¹ I'` for the cover `U × V` of `X ×_K Y` is
exact in degree one. -/
lemma exactAt_one_cechComplex_prodIdeal {α β : Type u} [Finite α] [Finite β]
    (Ux : α → X.Opens) (Vy : β → Y.Opens) (hUx : ∀ a, IsAffineOpen (Ux a))
    (hVy : ∀ b, IsAffineOpen (Vy b)) (hUx₂ : ∀ a a', IsAffineOpen (Ux a ⊓ Ux a'))
    (hVy₂ : ∀ b b', IsAffineOpen (Vy b ⊓ Vy b')) (hUcov : iSup Ux = ⊤) (hVcov : iSup Vy = ⊤)
    (hI : ∀ s ∈ I.idealOfOpens ⊤, s = 0) (hI' : ∀ s ∈ I'.idealOfOpens ⊤, s = 0) :
    ((TopCat.Presheaf.cechComplex (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).obj
      ((SheafOfModules.toSheaf _).obj (prodIdeal (K := K) I I').toModules).obj).ExactAt 1 := by
  classical
  set J := prodIdeal (K := K) I I'
  set Wc : α × β → (prod K X Y).Opens := fun p ↦ prodOpen K X Y (Ux p.1) (Vy p.2)
  set P := ((SheafOfModules.toSheaf _).obj J.toModules).obj
  rw [TopCat.Presheaf.exactAt_cechComplex_iff Wc P 0]
  intro c hc
  -- the components of `c`, as functions on opens inside the double intersections
  let cres (p q : α × β) (O : (prod K X Y).Opens) (h : O ≤ ⨅ l, Wc (![p, q] l)) :
      Γ(prod K X Y, O) :=
    J.toModulesι.app O (P.map (homOfLE h).op (c ![p, q]))
  have hcres_map (p q : α × β) {O O' : (prod K X Y).Opens} (h : O ≤ ⨅ l, Wc (![p, q] l))
      (h' : O' ≤ O) :
      (prod K X Y).presheaf.map (homOfLE h').op (cres p q O h) = cres p q O' (h'.trans h) := by
    change (prod K X Y).presheaf.map (homOfLE h').op (J.toModulesι.app O
      (J.toModules.presheaf.map (homOfLE h).op (c ![p, q]))) =
      J.toModulesι.app O' (J.toModules.presheaf.map (homOfLE (h'.trans h)).op (c ![p, q]))
    rw [Scheme.Modules.Hom.app_presheaf_map, Scheme.Modules.Hom.app_presheaf_map]
    exact Scheme.presheaf_map_homOfLE_map_homOfLE_apply h' h _
  have hcres_mem (p q : α × β) (O : (prod K X Y).Opens) (h : O ≤ ⨅ l, Wc (![p, q] l)) :
      cres p q O h ∈ J.idealOfOpens O := by
    rw [← SetLike.mem_coe, ← range_toModulesι_app_eq_idealOfOpens]
    exact ⟨_, rfl⟩
  have hcocycle (p r q : α × β) (O : (prod K X Y).Opens) (h : O ≤ ⨅ l, Wc (![p, r, q] l))
      (h₁ : O ≤ ⨅ l, Wc (![p, q] l)) (h₂ : O ≤ ⨅ l, Wc (![p, r] l))
      (h₃ : O ≤ ⨅ l, Wc (![r, q] l)) :
      cres p q O h₁ = cres p r O h₂ + cres r q O h₃ := by
    have h0 := congr_fun hc ![p, r, q]
    rw [TopCat.Presheaf.cechComplex_d_apply, TopCat.Presheaf.cechComplex_zero_apply] at h0
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0
    have h1 := congrArg (fun x ↦ J.toModulesι.app O (P.map (homOfLE h).op x)) h0
    simp only [map_add, map_zsmul, map_zero] at h1
    have e0 : ![p, r, q] ∘ Fin.succAbove 0 = ![r, q] := by
      funext l; fin_cases l <;> simp
    have e1 : ![p, r, q] ∘ (Fin.succ 0).succAbove = ![p, q] := by
      funext l; fin_cases l <;> simp [Fin.succAbove]
    have e2 : ![p, r, q] ∘ (Fin.succ 0).succ.succAbove = ![p, r] := by
      funext l; fin_cases l <;> simp [Fin.succAbove]
    simp only [TopCat.Presheaf.map_homOfLE_map_homOfLE_apply] at h1
    rw [TopCat.Presheaf.map_homOfLE_apply_congr Wc P (k := 1) c e0 _ h₃,
      TopCat.Presheaf.map_homOfLE_apply_congr Wc P (k := 1) c e1 _ h₁,
      TopCat.Presheaf.map_homOfLE_apply_congr Wc P (k := 1) c e2 _ h₂] at h1
    change (-1 : ℤ) ^ 0 • cres r q O h₃ + ((-1 : ℤ) ^ 1 • cres p q O h₁ +
      (-1 : ℤ) ^ 2 • cres p r O h₂) = 0 at h1
    simp only [pow_zero, pow_one, neg_one_sq, one_smul, neg_smul] at h1
    linear_combination (norm := abel_nf) -h1
  -- preimages of the components under `I(U) ⊗ I'(V) → Γ(U × V)`
  have hθ (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      (x : Γ(prod K X Y, prodOpen K X Y U V)) (hx : x ∈ J.idealOfOpens (prodOpen K X Y U V)) :
      ∃ w, mulIdeal I I' U V w = x :=
    (range_mulIdeal I I' hU hV).ge hx
  choose θinv hθinv using hθ
  -- restriction of `mulIdeal` along `U' ≤ U` in the first factor
  have hresL {U U' : X.Opens} {V : Y.Opens} (hU' : U' ≤ U) (w) :
      mulIdeal I I' U' V ((resIdeal (K := K) I hU').rTensor _ w) =
        (prod K X Y).presheaf.map (homOfLE (inf_le_inf ((prodFst K X Y).preimage_mono hU')
          ((prodSnd K X Y).preimage_mono (le_refl V)))).op (mulIdeal I I' U V w) := by
    rw [map_mulIdeal I I' hU' (le_refl V), resIdeal_self]
    rfl
  have hresR {U : X.Opens} {V V' : Y.Opens} (hV' : V' ≤ V) (w) :
      mulIdeal I I' U V' ((resIdeal (K := K) I' hV').lTensor _ w) =
        (prod K X Y).presheaf.map (homOfLE (inf_le_inf ((prodFst K X Y).preimage_mono
          (le_refl U)) ((prodSnd K X Y).preimage_mono hV'))).op (mulIdeal I I' U V w) := by
    rw [map_mulIdeal I I' (le_refl U) hV', resIdeal_self]
    rfl
  -- the opens over which the components live
  have hle {a a' : α} {b b' : β} {a₀ : α} {b₀ : β} (ha : a₀ = a ∨ a₀ = a')
      (hb : b₀ = b ∨ b₀ = b') :
      prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b') ≤ Wc (a₀, b₀) := by
    refine inf_le_inf ((prodFst K X Y).preimage_mono ?_) ((prodSnd K X Y).preimage_mono ?_)
    · rcases ha with rfl | rfl
      exacts [inf_le_left, inf_le_right]
    · rcases hb with rfl | rfl
      exacts [inf_le_left, inf_le_right]
  have hD {a a' : α} {b b' : β} {n : ℕ} (y : Fin n → α × β)
      (hy : ∀ l, ((y l).1 = a ∨ (y l).1 = a') ∧ ((y l).2 = b ∨ (y l).2 = b')) :
      prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b') ≤ ⨅ l, Wc (y l) :=
    le_iInf fun l ↦ hle (hy l).1 (hy l).2
  -- the horizontal and vertical components of `c`
  have hOH (a a' : α) (b : β) :
      prodOpen K X Y (Ux a ⊓ Ux a') (Vy b) ≤ ⨅ l, Wc (![(a, b), (a', b)] l) := by
    refine le_iInf fun l ↦ ?_
    fin_cases l
    · exact (inf_le_inf ((prodFst K X Y).preimage_mono inf_le_left) le_rfl :
        prodOpen K X Y (Ux a ⊓ Ux a') (Vy b) ≤ prodOpen K X Y (Ux a) (Vy b))
    · exact (inf_le_inf ((prodFst K X Y).preimage_mono inf_le_right) le_rfl :
        prodOpen K X Y (Ux a ⊓ Ux a') (Vy b) ≤ prodOpen K X Y (Ux a') (Vy b))
  have hOV (a : α) (b b' : β) :
      prodOpen K X Y (Ux a) (Vy b ⊓ Vy b') ≤ ⨅ l, Wc (![(a, b), (a, b')] l) := by
    refine le_iInf fun l ↦ ?_
    fin_cases l
    · exact (inf_le_inf le_rfl ((prodSnd K X Y).preimage_mono inf_le_left) :
        prodOpen K X Y (Ux a) (Vy b ⊓ Vy b') ≤ prodOpen K X Y (Ux a) (Vy b))
    · exact (inf_le_inf le_rfl ((prodSnd K X Y).preimage_mono inf_le_right) :
        prodOpen K X Y (Ux a) (Vy b ⊓ Vy b') ≤ prodOpen K X Y (Ux a) (Vy b'))
  let h (a a' : α) (b : β) :=
    θinv _ _ (hUx₂ a a') (hVy b) _ (hcres_mem (a, b) (a', b) _ (hOH a a' b))
  let v (a : α) (b b' : β) :=
    θinv _ _ (hUx a) (hVy₂ b b') _ (hcres_mem (a, b) (a, b') _ (hOV a b b'))
  have hh (a a' : α) (b : β) :
      mulIdeal I I' _ _ (h a a' b) = cres (a, b) (a', b) _ (hOH a a' b) := hθinv ..
  have hvv (a : α) (b b' : β) :
      mulIdeal I I' _ _ (v a b b') = cres (a, b) (a, b') _ (hOV a b b') := hθinv ..
  -- the cocycle relation between them
  have hv (a a' : α) (b b' : β) :
      (resIdeal (K := K) I (inf_le_right : Ux a ⊓ Ux a' ≤ Ux a')).rTensor _ (v a' b b') -
        (resIdeal (K := K) I (inf_le_left : Ux a ⊓ Ux a' ≤ Ux a)).rTensor _ (v a b b') =
      (resIdeal (K := K) I' (inf_le_right : Vy b ⊓ Vy b' ≤ Vy b')).lTensor _ (h a a' b') -
        (resIdeal (K := K) I' (inf_le_left : Vy b ⊓ Vy b' ≤ Vy b)).lTensor _ (h a a' b) := by
    apply injective_mulIdeal I I' (hUx₂ a a') (hVy₂ b b')
    rw [map_sub, map_sub, hresL, hresL, hresR, hresR, hh, hh, hvv, hvv, hcres_map, hcres_map,
      hcres_map, hcres_map]
    have hDD {n : ℕ} (y : Fin n → α × β) (hy : ∀ l, y l = (a, b) ∨ y l = (a', b) ∨
        y l = (a, b') ∨ y l = (a', b')) :
        prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b') ≤ ⨅ l, Wc (y l) := by
      refine hD y fun l ↦ ?_
      rcases hy l with h | h | h | h <;> rw [h] <;> simp
    have h1 : (a, b) = (a, b) ∨ (a, b) = (a', b) ∨ (a, b) = (a, b') ∨ (a, b) = (a', b') :=
      .inl rfl
    have h2 : (a', b) = (a, b) ∨ (a', b) = (a', b) ∨ (a', b) = (a, b') ∨ (a', b) = (a', b') :=
      .inr (.inl rfl)
    have h3 : (a, b') = (a, b) ∨ (a, b') = (a', b) ∨ (a, b') = (a, b') ∨ (a, b') = (a', b') :=
      .inr (.inr (.inl rfl))
    have h4 : (a', b') = (a, b) ∨ (a', b') = (a', b) ∨ (a', b') = (a, b') ∨
        (a', b') = (a', b') := .inr (.inr (.inr rfl))
    have c1 := hcocycle (a, b) (a', b) (a', b') (prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b'))
      (hDD _ fun l ↦ by fin_cases l; exacts [h1, h2, h4]) (hDD _ fun l ↦ by
        fin_cases l; exacts [h1, h4]) (hDD _ fun l ↦ by fin_cases l; exacts [h1, h2])
      (hDD _ fun l ↦ by fin_cases l; exacts [h2, h4])
    have c2 := hcocycle (a, b) (a, b') (a', b') (prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b'))
      (hDD _ fun l ↦ by fin_cases l; exacts [h1, h3, h4]) (hDD _ fun l ↦ by
        fin_cases l; exacts [h1, h4]) (hDD _ fun l ↦ by fin_cases l; exacts [h1, h3])
      (hDD _ fun l ↦ by fin_cases l; exacts [h3, h4])
    linear_combination c2 - c1
  obtain ⟨e, he₁, he₂⟩ := TensorProduct.exists_eq_rTensor_sub_and_eq_lTensor_sub
    (fun a a' ↦ resIdeal (K := K) I (inf_le_left : Ux a ⊓ Ux a' ≤ Ux a))
    (fun a a' ↦ resIdeal (K := K) I (inf_le_right : Ux a ⊓ Ux a' ≤ Ux a'))
    (fun f hf ↦ eq_zero_of_compatible I hI Ux hUcov f hf)
    (fun b b' ↦ resIdeal (K := K) I' (inf_le_left : Vy b ⊓ Vy b' ≤ Vy b))
    (fun b b' ↦ resIdeal (K := K) I' (inf_le_right : Vy b ⊓ Vy b' ≤ Vy b'))
    (fun g hg ↦ eq_zero_of_compatible I' hI' Vy hVcov g hg) h v hv
  -- the `0`-cochain
  have hσ (p : α × β) : ∃ s : Γ(J.toModules, Wc p),
      J.toModulesι.app _ s = mulIdeal I I' _ _ (e p.1 p.2) := by
    have hmem : mulIdeal I I' _ _ (e p.1 p.2) ∈ J.idealOfOpens (Wc p) := by
      rw [← SetLike.mem_coe, ← range_mulIdeal I I' (hUx p.1) (hVy p.2)]
      exact ⟨_, rfl⟩
    rw [← SetLike.mem_coe, ← range_toModulesι_app_eq_idealOfOpens] at hmem
    exact hmem
  choose σ hσ using hσ
  refine ⟨fun z ↦ P.map (homOfLE (iInf_le (fun l ↦ Wc (z l)) 0)).op (σ (z 0)), ?_⟩
  funext y
  refine J.injective_toModulesι_app _ ?_
  rw [TopCat.Presheaf.cechComplex_d_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, map_add, map_zsmul,
    TopCat.Presheaf.map_homOfLE_map_homOfLE_apply]
  have key (a a' : α) (b b' : β)
      (hpq : prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b') ≤ ⨅ l, Wc (![(a, b), (a', b')] l)) :
      (prod K X Y).presheaf.map (homOfLE (hle (a₀ := a') (b₀ := b') (.inr rfl) (.inr rfl))).op
          (mulIdeal I I' _ _ (e a' b')) -
        (prod K X Y).presheaf.map (homOfLE (hle (a₀ := a) (b₀ := b) (.inl rfl) (.inl rfl))).op
          (mulIdeal I I' _ _ (e a b)) =
        cres (a, b) (a', b') _ hpq := by
    have h1 : (a, b) = (a, b) ∨ (a, b) = (a', b) ∨ (a, b) = (a, b') ∨ (a, b) = (a', b') :=
      .inl rfl
    have h2 : (a', b) = (a, b) ∨ (a', b) = (a', b) ∨ (a', b) = (a, b') ∨ (a', b) = (a', b') :=
      .inr (.inl rfl)
    have h4 : (a', b') = (a, b) ∨ (a', b') = (a', b) ∨ (a', b') = (a, b') ∨
        (a', b') = (a', b') := .inr (.inr (.inr rfl))
    have hDD {n : ℕ} (y : Fin n → α × β) (hy : ∀ l, y l = (a, b) ∨ y l = (a', b) ∨
        y l = (a, b') ∨ y l = (a', b')) :
        prodOpen K X Y (Ux a ⊓ Ux a') (Vy b ⊓ Vy b') ≤ ⨅ l, Wc (y l) := by
      refine hD y fun l ↦ ?_
      rcases hy l with h | h | h | h <;> rw [h] <;> simp
    rw [hcocycle (a, b) (a', b) (a', b') _ (hDD _ fun l ↦ by fin_cases l; exacts [h1, h2, h4])
      hpq (hDD _ fun l ↦ by fin_cases l; exacts [h1, h2])
      (hDD _ fun l ↦ by fin_cases l; exacts [h2, h4])]
    rw [← hcres_map (a, b) (a', b) (hOH a a' b)
        (inf_le_inf le_rfl ((prodSnd K X Y).preimage_mono inf_le_left)),
      ← hcres_map (a', b) (a', b') (hOV a' b b')
        (inf_le_inf ((prodFst K X Y).preimage_mono inf_le_right) le_rfl),
      ← hh, ← hvv, he₁, he₂]
    simp only [map_sub, hresL, hresR, Scheme.presheaf_map_homOfLE_map_homOfLE_apply]
    abel
  have hιmap {O O' : (prod K X Y).Opens} (hO : O' ≤ O) (s : Γ(J.toModules, O)) :
      J.toModulesι.app O' (P.map (homOfLE hO).op s) =
        (prod K X Y).presheaf.map (homOfLE hO).op (J.toModulesι.app O s) :=
    Scheme.Modules.Hom.app_presheaf_map _ _ _
  change (-1 : ℤ) ^ 0 • J.toModulesι.app _ (P.map (homOfLE _).op (σ (y 1))) +
    (-1 : ℤ) ^ 1 • J.toModulesι.app _ (P.map (homOfLE _).op (σ (y 0))) =
      J.toModulesι.app _ (c y)
  simp only [pow_zero, pow_one, one_smul, neg_smul, ← sub_eq_add_neg]
  rw [hιmap, hιmap, hσ, hσ]
  set p := y 0
  set q := y 1
  have hy : y = ![p, q] := by
    funext l; fin_cases l <;> rfl
  have hyle : ⨅ l, Wc (y l) ≤ ⨅ l, Wc (![p, q] l) := hy ▸ le_rfl
  rw [show c y = P.map (homOfLE hyle).op (c ![p, q]) from
    ((TopCat.Presheaf.map_homOfLE_self_apply P le_rfl (c y)).symm.trans
      (TopCat.Presheaf.map_homOfLE_apply_congr Wc P c hy _ _))]
  change _ = cres p q _ hyle
  -- compare on `U_{a a'} × V_{b b'}`
  set D := prodOpen K X Y (Ux p.1 ⊓ Ux q.1) (Vy p.2 ⊓ Vy q.2)
  have hDy : D = ⨅ l, Wc (y l) := by
    refine le_antisymm (le_iInf fun l ↦ ?_) fun x hx ↦ ?_
    · fin_cases l
      · exact hle (.inl rfl) (.inl rfl)
      · exact hle (.inr rfl) (.inr rfl)
    · have h0 : x ∈ Wc p := (iInf_le (fun l ↦ Wc (y l)) 0) hx
      have h1 : x ∈ Wc q := (iInf_le (fun l ↦ Wc (y l)) 1) hx
      exact ⟨⟨h0.1, h1.1⟩, ⟨h0.2, h1.2⟩⟩
  refine eq_of_presheaf_map_eq hDy ?_
  rw [map_sub, Scheme.presheaf_map_homOfLE_map_homOfLE_apply,
    Scheme.presheaf_map_homOfLE_map_homOfLE_apply, hcres_map]
  exact key p.1 q.1 p.2 q.2 _

/-- A quasi-compact scheme has a finite cover by affine opens. -/
lemma exists_finite_affine_cover (Z : Scheme.{u}) [CompactSpace Z] :
    ∃ s : Set Z.affineOpens, s.Finite ∧ ⨆ a : s, (a.1 : Z.Opens) = ⊤ := by
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : Z.Opens))).mp (by simpa using isCompact_univ)
  exact ⟨s, hs, by rw [hsU, iSup_subtype']⟩

/-- **Vanishing of `H¹(X ×_K Y, I ⊠ I')`.** Let `X` and `Y` be quasi-compact and separated over
a field `K`, and let `I`, `I'` be ideal sheaves on `X`, `Y` without nonzero global sections.
Then `H¹(X ×_K Y, pr_X⁻¹ I ⊓ pr_Y⁻¹ I') = 0` (the Künneth formula in degree one). -/
theorem subsingleton_H_one_toModules_prodIdeal [CompactSpace X] [CompactSpace Y]
    [IsSeparated (X ↘ Spec (.of K))] [IsSeparated (Y ↘ Spec (.of K))]
    (hI : ∀ s ∈ I.idealOfOpens ⊤, s = 0) (hI' : ∀ s ∈ I'.idealOfOpens ⊤, s = 0) :
    Subsingleton ((prodIdeal (K := K) I I').toModules.H 1) := by
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of K))]; infer_instance
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from (Y ↘ Spec (.of K))]; infer_instance
  obtain ⟨sX, hsX, hsXU⟩ := exists_finite_affine_cover X
  obtain ⟨sY, hsY, hsYU⟩ := exists_finite_affine_cover Y
  have := hsX.to_subtype
  have := hsY.to_subtype
  let Ux : sX → X.Opens := fun a ↦ a.1.1
  let Vy : sY → Y.Opens := fun b ↦ b.1.1
  have hUx (a : sX) : IsAffineOpen (Ux a) := a.1.2
  have hVy (b : sY) : IsAffineOpen (Vy b) := b.1.2
  let Wc : sX × sY → (prod K X Y).Opens := fun p ↦ prodOpen K X Y (Ux p.1) (Vy p.2)
  have hWc (p : sX × sY) : IsAffineOpen (Wc p) :=
    isAffineOpen_preimage_inf_preimage_pullback _ _ (hUx p.1) (hVy p.2)
  have hWcov : iSup Wc = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hsXU.ge (Set.mem_univ (prodFst K X Y x)))
    obtain ⟨b, hb⟩ := Opens.mem_iSup.mp (hsYU.ge (Set.mem_univ (prodSnd K X Y x)))
    exact Opens.mem_iSup.mpr ⟨(a, b), ha, hb⟩
  have := Scheme.Modules.isQuasicoherent_toModules (prodIdeal (K := K) I I')
  obtain ⟨e⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (prodFst K X Y ≫ X ↘ Spec (.of K)) Wc hWc hWcov (prodIdeal (K := K) I I').toModules 1
  have hex := exactAt_one_cechComplex_prodIdeal (K := K) I I' Ux Vy hUx hVy
    (fun a a' ↦ (hUx a).inf (hUx a')) (fun b b' ↦ (hVy b).inf (hVy b')) hsXU hsYU hI hI'
  have : Subsingleton ((TopCat.Sheaf.cechCohomologyFunctor Wc 1).obj
      ((SheafOfModules.toSheaf _).obj (prodIdeal (K := K) I I').toModules)) :=
    AddCommGrpCat.subsingleton_of_isZero hex.isZero_homology
  have := (Scheme.Modules.cechComplexHomologyAddEquiv Wc
    (prodIdeal (K := K) I I').toModules 1).toEquiv.subsingleton
  exact e.symm.toEquiv.subsingleton

end Kunneth

end AlgebraicGeometry.Scheme.IdealSheafData
