/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance

/-!
# Common-degree twists on a quasi-compact Proj open

Source: Stacks Project, Constructions, Tags 01MU and 01MW, the characterization of the
invertibility locus and the proof after the finite standard-open cover
(blueprint: lem-trf-proj-common-degree-twist-invertible).

The statement records the open `W_e` by its equivalent union of standard opens and records
the canonical multiplication maps by their action on all local pure tensors. They multiply
homogeneous fractions on the standard-open cover.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

open ProjectiveSpectrum.Twist HomogeneousLocalization Opposite MonoidalCategory
open Scheme.Modules

private abbrev schemeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

attribute [local instance] schemeMonoidal

private theorem powerDegree (e : ℕ) (n : ℤ) :
    ((n.toNat * e : ℕ) : ℤ) = ((-n).toNat * e : ℕ) + n * (e : ℤ) := by
  push_cast
  have h : (n.toNat : ℤ) = ((-n).toNat : ℤ) + n := by omega
  rw [h, add_mul]

private def powerSection {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (n : ℤ)
    {U : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 f) :
    Γ(twist 𝒜 (n * (e : ℤ)), U) :=
  let a : 𝒜 (n.toNat * e) := ⟨f ^ n.toNat, by
    simpa using SetLike.pow_mem_graded (A := 𝒜) n.toNat hf⟩
  let b : 𝒜 ((-n).toNat * e) := ⟨f ^ (-n).toNat, by
    simpa using SetLike.pow_mem_graded (A := 𝒜) (-n).toNat hf⟩
  let hb (x : U) : (b : A) ∉ x.val.asHomogeneousIdeal.toIdeal :=
    fun h ↦ hU x.property (x.val.isPrime.mem_of_pow_mem _ h)
  ⟨fun x ↦ degreePart.mk a b (hb x) (powerDegree e n),
    isLocallyFraction_mk (powerDegree e n) a b hb⟩

private theorem powerSection_val {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (n : ℤ)
    {U : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 f) (x : U) :
    ((powerSection 𝒜 hf n hU).val x :
      Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) =
      Localization.mk (f ^ n.toNat) (⟨f ^ (-n).toNat,
        fun h ↦ hU x.property (x.val.isPrime.mem_of_pow_mem _ h)⟩ :
          x.val.asHomogeneousIdeal.toIdeal.primeCompl) :=
  degreePart.coe_mk _ _ _ (powerDegree e n)

private theorem powerSection_mul {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (n m : ℤ)
    {U : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 f) (x : U) :
    ((powerSection 𝒜 hf n hU).val x :
      Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) *
      (powerSection 𝒜 hf m hU).val x =
      (powerSection 𝒜 hf (n + m) hU).val x := by
  rw [powerSection_val, powerSection_val, powerSection_val,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, ← pow_add]
  congr 1
  omega

private theorem powerSection_zero {e : ℕ} {f : A} (hf : f ∈ 𝒜 e)
    {U : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 f) (x : U) :
    ((powerSection 𝒜 hf 0 hU).val x :
      Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) = 1 := by
  rw [powerSection_val]
  simp

private theorem castSection_val {a b : ℤ} (h : a = b) {U : (Proj 𝒜).Opens}
    (s : Γ(twist 𝒜 a, U)) (x : U) :
    ((h ▸ s).val x : Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) = s.val x := by
  subst b
  rfl

private theorem powerSection_generator {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (n : ℤ)
    {U : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 f) :
    IsFreeGenerator (powerSection 𝒜 hf n hU) := by
  let invsec : Γ(twist 𝒜 (-(n * (e : ℤ))), U) :=
    (neg_mul n (e : ℤ)) ▸ powerSection 𝒜 hf (-n) hU
  apply isFreeGenerator_twist_of_mul_eq_one _ invsec
  intro x
  rw [castSection_val, powerSection_mul]
  rw [show n + -n = 0 by omega]
  exact powerSection_zero 𝒜 hf hU x

private def mulSections (a b c : ℤ) (h : a + b = c)
    (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 a, U)) (t : Γ(twist 𝒜 b, U)) :
    Γ(twist 𝒜 c, U) :=
  ⟨fun x ↦ ⟨s.val x * t.val x, h ▸ mul_mem_degreePart (s.val x).property
    (t.val x).property⟩, isLocallyFraction_mul h s.property t.property⟩

private def mulBilinear (a b c : ℤ) (h : a + b = c) (U : (Proj 𝒜).Opens) :
    Γ(twist 𝒜 a, U) →ₗ[Γ(Proj 𝒜, U)] Γ(twist 𝒜 b, U) →ₗ[Γ(Proj 𝒜, U)]
      Γ(twist 𝒜 c, U) :=
  LinearMap.mk₂ Γ(Proj 𝒜, U) (mulSections 𝒜 a b c h U)
    (by
      intro s s' t
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact add_mul _ _ _)
    (by
      intro r s t
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact mul_assoc _ _ _)
    (by
      intro s t t'
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact mul_add _ _ _)
    (by
      intro r s t
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact mul_left_comm _ _ _)

private theorem mulBilinear_natural (a b c : ℤ) (h : a + b = c)
    {U T : (Proj 𝒜).Opensᵒᵖ} (i : U ⟶ T)
    (s : (twist 𝒜 a).val.obj U) (t : (twist 𝒜 b).val.obj U) :
    mulBilinear 𝒜 a b c h T.unop ((twist 𝒜 a).val.map i s)
        ((twist 𝒜 b).val.map i t) =
      (twist 𝒜 c).val.map i (mulBilinear 𝒜 a b c h U.unop s t) := rfl

@[irreducible] private def tensorLift {X : Scheme.{u}} (F G H : X.Modules)
    (β : ∀ U : X.Opensᵒᵖ,
      F.val.obj U →ₗ[X.sheaf.obj.obj U] G.val.obj U →ₗ[X.sheaf.obj.obj U] H.val.obj U)
    (hβ : ∀ {U T : X.Opensᵒᵖ} (i : U ⟶ T) (s : F.val.obj U) (t : G.val.obj U),
      β T (F.val.map i s) (G.val.map i t) = H.val.map i (β U s t)) :
    F ⊗ G ⟶ H :=
  (SheafOfModules.tensor_bilinear_universal X.sheaf F G H β hβ).choose

private theorem tensorLift_tmul {X : Scheme.{u}} (F G H : X.Modules)
    (β : ∀ U : X.Opensᵒᵖ,
      F.val.obj U →ₗ[X.sheaf.obj.obj U] G.val.obj U →ₗ[X.sheaf.obj.obj U] H.val.obj U)
    (hβ : ∀ {U T : X.Opensᵒᵖ} (i : U ⟶ T) (s : F.val.obj U) (t : G.val.obj U),
      β T (F.val.map i s) (G.val.map i t) = H.val.map i (β U s t))
    (U : X.Opens) (s : Γ(F, U)) (t : Γ(G, U)) :
    (tensorLift F G H β hβ).app U (tmulSection s t) = β (op U) s t := by
  unfold tensorLift
  exact (SheafOfModules.tensor_bilinear_universal X.sheaf F G H β hβ).choose_spec.1
    (op U) s t

@[irreducible] private def ambientMultiplication (a b c : ℤ) (h : a + b = c) :
    twist 𝒜 a ⊗ twist 𝒜 b ⟶ twist 𝒜 c :=
  tensorLift (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)
    (fun U ↦ mulBilinear 𝒜 a b c h U.unop) (mulBilinear_natural 𝒜 a b c h)

private theorem ambientMultiplication_tmul (a b c : ℤ) (h : a + b = c)
    (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 a, U)) (t : Γ(twist 𝒜 b, U)) :
    (ambientMultiplication 𝒜 a b c h).app U (tmulSection s t) =
      mulSections 𝒜 a b c h U s t := by
  unfold ambientMultiplication
  exact tensorLift_tmul _ _ _ _ _ U s t

@[irreducible] private def restrictTensorHom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G H : X.Modules) (φ : F ⊗ G ⟶ H) :
    F.restrict j ⊗ G.restrict j ⟶ H.restrict j :=
  (exists_restriction_tensor_comparison j F G).choose.inv ≫ (restrictFunctor j).map φ

private theorem restrict_map_app {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {F H : X.Modules} (φ : F ⟶ H) (Q : Y.Opens)
    (s : Γ(F.restrict j, Q)) :
    (H.restrictAppIso j Q).hom (((restrictFunctor j).map φ).app Q s) =
      φ.app (j ''ᵁ Q) ((F.restrictAppIso j Q).hom s) := rfl

private theorem restrictTensorHom_tmul {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G H : X.Modules) (φ : F ⊗ G ⟶ H) (Q : Y.Opens)
    (s : Γ(F.restrict j, Q)) (t : Γ(G.restrict j, Q)) :
    (H.restrictAppIso j Q).hom ((restrictTensorHom j F G H φ).app Q (tmulSection s t)) =
      φ.app (j ''ᵁ Q)
        (tmulSection ((F.restrictAppIso j Q).hom s) ((G.restrictAppIso j Q).hom t)) := by
  unfold restrictTensorHom
  rw [Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app,
    (exists_restriction_tensor_comparison j F G).choose_spec]

@[irreducible] private def multiplication (V : (Proj 𝒜).Opens) (a b c : ℤ)
    (h : a + b = c) :
    Scheme.Modules.tensorObj ((twist 𝒜 a).restrict V.ι) ((twist 𝒜 b).restrict V.ι) ⟶
      (twist 𝒜 c).restrict V.ι :=
  restrictTensorHom V.ι (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)
    (ambientMultiplication 𝒜 a b c h)

private theorem multiplication_tmul (V : (Proj 𝒜).Opens) (a b c : ℤ) (h : a + b = c)
    (Q : V.toScheme.Opens)
    (s : Γ((twist 𝒜 a).restrict V.ι, Q))
    (t : Γ((twist 𝒜 b).restrict V.ι, Q)) :
    ((twist 𝒜 c).restrictAppIso V.ι Q).hom
      ((multiplication 𝒜 V a b c h).app Q (tmulSection s t)) =
      mulSections 𝒜 a b c h (V.ι ''ᵁ Q)
        (((twist 𝒜 a).restrictAppIso V.ι Q).hom s)
        (((twist 𝒜 b).restrictAppIso V.ι Q).hom t) := by
  unfold multiplication
  rw [restrictTensorHom_tmul, ambientMultiplication_tmul]

private theorem invertible_of_local_generators {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ s : Γ(M, U), IsFreeGenerator s) :
    M.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, s, hs⟩ := h x
    obtain ⟨j⟩ := nonempty_restrict_iso_unit hs
    exact ⟨U, hx, ⟨(restrictFunctorIsoPullback U.ι).symm.app _ ≪≫ j⟩⟩

private theorem bijective_of_generators {X : Scheme.{u}} {F G H : X.Modules}
    (φ : F ⊗ G ⟶ H) (Q : X.Opens) (s : Γ(F, Q)) (t : Γ(G, Q))
    (w : Γ(H, Q)) (hs : IsFreeGenerator s) (ht : IsFreeGenerator t)
    (hw : IsFreeGenerator w) (hst : φ.app Q (tmulSection s t) = w) :
    Function.Bijective (φ.app Q) := by
  have hcomp : (φ.app Q ∘ fun r : Γ(X, Q) ↦ r • tmulSection s t) =
      fun r : Γ(X, Q) ↦ r • w := by
    funext r
    exact (Hom.app_smul φ r _).trans (congrArg (r • ·) hst)
  apply (Function.Bijective.of_comp_iff (φ.app Q) (hs.tmulSection ht).bijective).1
  rw [hcomp]
  exact hw.bijective

private theorem bijective_restrictTensorHom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G H : X.Modules) (φ : F ⊗ G ⟶ H) (Q : Y.Opens)
    (s : Γ(F, j ''ᵁ Q)) (t : Γ(G, j ''ᵁ Q)) (w : Γ(H, j ''ᵁ Q))
    (hs : IsFreeGenerator s) (ht : IsFreeGenerator t) (hw : IsFreeGenerator w)
    (hst : φ.app (j ''ᵁ Q) (tmulSection s t) = w) :
    Function.Bijective ((restrictTensorHom j F G H φ).app Q) := by
  apply bijective_of_generators (restrictTensorHom j F G H φ) Q
    ((F.restrictAppIso j Q).inv s) ((G.restrictAppIso j Q).inv t)
    ((H.restrictAppIso j Q).inv w)
    ((isFreeGenerator_restrict_iff j F s).2 hs)
    ((isFreeGenerator_restrict_iff j G t).2 ht)
    ((isFreeGenerator_restrict_iff j H w).2 hw)
  apply (ConcreteCategory.bijective_of_isIso (H.restrictAppIso j Q).hom).1
  rw [restrictTensorHom_tmul]
  exact hst

private theorem invertible_restrict_of_generators {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (M : X.Modules)
    (h : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧
      ∃ s : Γ(M, j ''ᵁ U), IsFreeGenerator s) : (M.restrict j).IsInvertible := by
  apply invertible_of_local_generators
  intro x
  obtain ⟨U, hx, s, hs⟩ := h x
  exact ⟨U, hx, (M.restrictAppIso j U).inv s,
    (isFreeGenerator_restrict_iff j M s).2 hs⟩

private theorem invertible_on_degree_cover (V : (Proj 𝒜).Opens) (e : ℕ)
    (hc : ∀ x : V, ∃ f : A, f ∈ 𝒜 e ∧ x.val ∈ basicOpen 𝒜 f) (n : ℤ) :
    ((twist 𝒜 (n * (e : ℤ))).restrict V.ι).IsInvertible := by
  apply invertible_restrict_of_generators
  intro x
  obtain ⟨f, hf, hx⟩ := hc x
  let U := V.ι ⁻¹ᵁ basicOpen 𝒜 f
  have hU : V.ι ''ᵁ U ≤ basicOpen 𝒜 f := V.ι.image_preimage_le _
  exact ⟨U, hx, powerSection 𝒜 hf n hU, powerSection_generator 𝒜 hf n hU⟩

private theorem multiplication_iso (V : (Proj 𝒜).Opens) (e : ℕ)
    (hc : ∀ x : V, ∃ f : A, f ∈ 𝒜 e ∧ x.val ∈ basicOpen 𝒜 f) (n m : ℤ) :
    IsIso (multiplication 𝒜 V (n * (e : ℤ)) (m * (e : ℤ))
      ((n + m) * (e : ℤ)) (add_mul n m (e : ℤ)).symm) := by
  apply Hom.isIso_of_forall_bijective_app
  intro x
  obtain ⟨f, hf, hx⟩ := hc x
  refine ⟨V.ι ⁻¹ᵁ basicOpen 𝒜 f, hx, ?_⟩
  intro Q hQ
  have hQf : V.ι ''ᵁ Q ≤ basicOpen 𝒜 f :=
    (V.ι.image_mono hQ).trans (V.ι.image_preimage_le _)
  unfold multiplication
  apply bijective_restrictTensorHom V.ι (twist 𝒜 (n * (e : ℤ)))
    (twist 𝒜 (m * (e : ℤ))) (twist 𝒜 ((n + m) * (e : ℤ)))
    (ambientMultiplication 𝒜 _ _ _ _) Q
    (powerSection 𝒜 hf n hQf) (powerSection 𝒜 hf m hQf)
    (powerSection 𝒜 hf (n + m) hQf)
    (powerSection_generator 𝒜 hf n hQf) (powerSection_generator 𝒜 hf m hQf)
    (powerSection_generator 𝒜 hf (n + m) hQf)
  rw [ambientMultiplication_tmul]
  apply Subtype.ext
  funext y
  apply Subtype.ext
  exact powerSection_mul 𝒜 hf n m hQf y

private theorem multiplication_iso_of_degrees (V : (Proj 𝒜).Opens) (e : ℕ)
    (hc : ∀ x : V, ∃ f : A, f ∈ 𝒜 e ∧ x.val ∈ basicOpen 𝒜 f)
    (n m a b c : ℤ) (ha : a = n * (e : ℤ)) (hb : b = m * (e : ℤ))
    (hc' : c = (n + m) * (e : ℤ)) (h : a + b = c) :
    IsIso (multiplication 𝒜 V a b c h) := by
  subst a b c
  exact multiplication_iso 𝒜 V e hc n m

/-- The common-degree invertibility and multiplication assertion on an open of `Proj`.

Source: Stacks Project, Constructions, Tags 01MU (lemma-where-invertible) and 01MW
(lemma-ample-on-proj), clauses (1)--(4)
(blueprint: lem-trf-proj-common-degree-twist-invertible).

Proof:
1. Replace each covering element by its positive power of degree `e`; the standard
   open is unchanged because a prime contains a positive power exactly when it contains
   its base. The cover is already an input, so no finite-subcover argument is required.
2. In the union formula for `W`, take a degree-`e` covering element as `a` and take
   `b = 1` of degree zero. This proves `V ≤ W`.
3. On a degree-`e` chart `D_+(a)`, construct the integer-power section as the fraction
   `a^(n.toNat) / a^((-n).toNat)`. Localization identities show that opposite powers
   multiply to one, giving free generators of every `O(ne)` and hence invertibility.
4. Pointwise multiplication is bilinear and commutes with restriction. The sheaf tensor
   universal property constructs its unique morphism on Proj, and the restriction-tensor
   comparison transports it to `V`. It sends the tensor of the two local power generators
   to the power generator of their sum. Thus it is locally bijective on sections and is
   an isomorphism. Taking the integer `n = k` gives the natural-degree assertion.
5. Start with the restricted unit isomorphism to `O(0)` and recursively tensor the
   preceding isomorphism with the identity of `O(e)`, then compose with binary
   multiplication. The unit formula and the successor formula follow from their section
   formulas. This constructs isomorphisms even at `k = 0`. Empty covers cause no problem:
   all local assertions are quantified over points, and the cover then forces `V` empty.
-/
theorem commonDegreeTwistInvertible
    (V : (Proj 𝒜).Opens) [CompactSpace V.toScheme]
    (I : Type v) [Finite I]
    (f : I → A) (d : I → ℕ)
    (hf : ∀ i, f i ∈ 𝒜 (d i))
    (hd : ∀ i, 0 < d i)
    (hcover : V ≤ ⨆ i, basicOpen 𝒜 (f i))
    (e : ℕ) (he : 0 < e)
    (hdiv : ∀ i, d i ∣ e)
    (W : (Proj 𝒜).Opens)
    (hW : W = ⨆ (α : ℕ) (β : ℕ) (a : 𝒜 α) (b : 𝒜 β) (_ : α = β + e),
      basicOpen 𝒜 ((a : A) * (b : A)))
    : V ≤ W ∧
      (∀ n : ℤ, ((twist 𝒜 (n * (e : ℤ))).restrict V.ι).IsInvertible) ∧
      (∀ n m : ℤ,
        ∃ μ : Scheme.Modules.tensorObj
            ((twist 𝒜 (n * (e : ℤ))).restrict V.ι)
            ((twist 𝒜 (m * (e : ℤ))).restrict V.ι) ⟶
            (twist 𝒜 ((n + m) * (e : ℤ))).restrict V.ι,
          IsIso μ ∧ ∀ (Q : V.toScheme.Opens)
            (s : Γ((twist 𝒜 (n * (e : ℤ))).restrict V.ι, Q))
            (t : Γ((twist 𝒜 (m * (e : ℤ))).restrict V.ι, Q)) (x : V.ι ''ᵁ Q),
            (((twist 𝒜 ((n + m) * (e : ℤ))).restrictAppIso V.ι Q).hom
              (μ.app Q (Scheme.Modules.tmulSection s t))).val x =
            ((((twist 𝒜 (n * (e : ℤ))).restrictAppIso V.ι Q).hom s).val x :
              Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) *
              (((twist 𝒜 (m * (e : ℤ))).restrictAppIso V.ι Q).hom t).val x) ∧
      (∀ k : ℕ, 0 < k →
        ((twist 𝒜 (Int.ofNat (e * k))).restrict V.ι).IsInvertible) ∧
      (∃ μ : ∀ k : ℕ,
          ((twist 𝒜 (e : ℤ)).restrict V.ι).tensorPow k ⟶
            (twist 𝒜 (Int.ofNat (e * k))).restrict V.ι,
        (∀ k : ℕ, 0 < k → IsIso (μ k)) ∧
        (∀ (Q : V.toScheme.Opens) (x : V.ι ''ᵁ Q),
          (((twist 𝒜 (Int.ofNat (e * 0))).restrictAppIso V.ι Q).hom
            ((μ 0).app Q (Scheme.Modules.unitSectionsEquiv Q 1))).val x =
              (1 : Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal)) ∧
        (∀ (k : ℕ) (Q : V.toScheme.Opens)
          (s : Γ((twist 𝒜 (e : ℤ)).restrict V.ι, Q))
          (t : Γ(((twist 𝒜 (e : ℤ)).restrict V.ι).tensorPow k, Q))
          (x : V.ι ''ᵁ Q),
          (((twist 𝒜 (Int.ofNat (e * (k + 1)))).restrictAppIso V.ι Q).hom
            ((μ (k + 1)).app Q (Scheme.Modules.tmulSection s t))).val x =
          ((((twist 𝒜 (e : ℤ)).restrictAppIso V.ι Q).hom s).val x :
            Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) *
            (((twist 𝒜 (Int.ofNat (e * k))).restrictAppIso V.ι Q).hom
              ((μ k).app Q t)).val x)) := by
  classical
  let g (i : I) := f i ^ (e / d i)
  have hg (i : I) : g i ∈ 𝒜 e := by
    simpa [g, Nat.div_mul_cancel (hdiv i)] using
      SetLike.pow_mem_graded (A := 𝒜) (e / d i) (hf i)
  have hpos (i : I) : 0 < e / d i :=
    Nat.div_pos (Nat.le_of_dvd he (hdiv i)) (hd i)
  have hopen (i : I) : basicOpen 𝒜 (g i) = basicOpen 𝒜 (f i) :=
    AlgebraicGeometry.Proj.basicOpen_pow 𝒜 (f i) (e / d i) (hpos i)
  have hc : ∀ x : V, ∃ a : A, a ∈ 𝒜 e ∧ x.val ∈ basicOpen 𝒜 a := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover x.property)
    exact ⟨g i, hg i, (hopen i).symm ▸ hi⟩
  have hVW : V ≤ W := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := hc ⟨x, hx⟩
    rw [hW]
    simp only [TopologicalSpace.Opens.mem_iSup]
    refine ⟨e, 0, ⟨a, ha⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩, by omega, ?_⟩
    simpa using hxa
  have hinv := invertible_on_degree_cover 𝒜 V e hc
  refine ⟨hVW, hinv, ?_, ?_, ?_⟩
  · intro n m
    refine ⟨multiplication 𝒜 V (n * (e : ℤ)) (m * (e : ℤ))
      ((n + m) * (e : ℤ)) (add_mul n m (e : ℤ)).symm,
      multiplication_iso 𝒜 V e hc n m, ?_⟩
    intro Q s t x
    rw [multiplication_tmul]
    rfl
  · intro k _
    have hk : Int.ofNat (e * k) = (k : ℤ) * (e : ℤ) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_mul, mul_comm]
    simpa only [hk] using hinv (k : ℤ)
  · let L := (twist 𝒜 (e : ℤ)).restrict V.ι
    have hdeg (k : ℕ) : (e : ℤ) + Int.ofNat (e * k) = Int.ofNat (e * (k + 1)) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    have hiso (k : ℕ) :
        IsIso (multiplication 𝒜 V (e : ℤ) (Int.ofNat (e * k))
          (Int.ofNat (e * (k + 1))) (hdeg k)) := by
      apply multiplication_iso_of_degrees 𝒜 V e hc 1 (k : ℤ)
      · simp only [one_mul]
      · simp only [Int.ofNat_eq_natCast, Nat.cast_mul, mul_comm]
      · simp only [Int.ofNat_eq_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
    let z : L.tensorPow 0 ≅ (twist 𝒜 (Int.ofNat (e * 0))).restrict V.ι :=
      (restrictUnitIso V.ι).symm ≪≫ (restrictFunctor V.ι).mapIso unitIsoTwistZero
    let μ : (k : ℕ) → L.tensorPow k ≅ (twist 𝒜 (Int.ofNat (e * k))).restrict V.ι :=
      fun k ↦ Nat.rec (motive := fun k ↦
        L.tensorPow k ≅ (twist 𝒜 (Int.ofNat (e * k))).restrict V.ι) z (fun k ih ↦
        (Iso.refl L ⊗ᵢ ih) ≪≫ asIso
          (multiplication 𝒜 V (e : ℤ) (Int.ofNat (e * k))
            (Int.ofNat (e * (k + 1))) (hdeg k))) k
    refine ⟨fun k ↦ (μ k).hom, fun k _ ↦ inferInstance, ?_, ?_⟩
    · intro Q x
      change ((((twist 𝒜 0).restrictAppIso V.ι Q).hom
        (z.hom.app Q (unitSectionsEquiv Q 1))).val x :
          Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) = 1
      change (((V.ι.appIso Q).inv 1).val x).val = 1
      rw [map_one]
      simp
    · intro k Q s t x
      change ((((twist 𝒜 (Int.ofNat (e * (k + 1)))).restrictAppIso V.ι Q).hom
        (((Iso.refl L ⊗ᵢ μ k) ≪≫ asIso
          (multiplication 𝒜 V (e : ℤ) (Int.ofNat (e * k))
            (Int.ofNat (e * (k + 1))) (hdeg k))).hom.app Q
              (tmulSection s t))).val x :
                Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) = _
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, asIso_hom,
        Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection,
        Hom.id_app]
      rw [multiplication_tmul]
      rfl

end AlgebraicGeometry.Proj
