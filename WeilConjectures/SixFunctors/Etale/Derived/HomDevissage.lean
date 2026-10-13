/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation

/-!
# Dévissage for comparison maps of internal homs

A comparison map `c_K : F(RHom(K, M)) ⟶ RHom(G K, G M)` is contravariant in `K`. To show that it
is an isomorphism for every `K ∈ Dctf(X, Λ)` it suffices, by the generation of `Dctf`
(`AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`), to
treat the generators `Rg_* Rj_! L`, provided both sides are exact in `K`. This file sets up this
dévissage.

## Main definitions and statements

- `CategoryTheory.Pretriangulated.Triangle.DistinguishedUpToSign`: a triangle is distinguished
  up to sign if it, or the triangle with its third morphism negated, is distinguished. Both
  give the same long exact `Hom` sequences, so the five lemma holds for them
  (`CategoryTheory.Pretriangulated.Triangle.DistinguishedUpToSign.isIso₂_of_isIso₁₃`).
- `CategoryTheory.Functor.contravariantTriangle`: the image `Φ X₃ ⟶ Φ X₂ ⟶ Φ X₁ ⟶ (Φ X₃)⟦1⟧` of a
  triangle under a contravariant functor `Φ : Cᵒᵖ ⥤ D` with isomorphisms
  `e_K : Φ K ≅ (Φ (K⟦1⟧))⟦1⟧`, and `CategoryTheory.Functor.IsTriangulatedUpToSignOp`: `Φ` sends
  distinguished triangles to triangles distinguished up to sign.
- `CategoryTheory.Pretriangulated.isTriangulated_isIso_app`: for `τ : Φ ⟶ Ψ` between two such
  functors, compatible with the `e`, the objects `K` with `τ_K` an isomorphism form a
  triangulated subcategory.
- `AlgebraicGeometry.Etale.isTriangulatedUpToSignOp_derivedHom` (blueprint
  `lem-sf-hom-triangulated`, a node of `sk-prop-sf-rf-shriek-preservation`): `RHom(-, M)` is
  exact in its first variable.
- `AlgebraicGeometry.Etale.isIso_app_of_constructibleFiniteTor`: the dévissage principle on
  `Dctf(X, Λ)`.

## Implementation notes

The sign of the connecting morphism of `RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M) ⟶` depends on
the sign conventions for shifts of complexes, so the exactness of `RHom(-, M)` is stated up to
sign, per triangle. This is enough for two-out-of-three arguments, which only use the long
exact `Hom` sequences. The blueprint node `lem-weil-stratum-ambient-hom`,
`RHom_X(Rs_! P, M) ≅ Rs_* RHom_S(P, Rs^! M)`, is the tensor–Hom exchange
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` (blueprint `lem-sf-tensor-hom`).
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits Opposite Category

namespace CategoryTheory

namespace Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangle

/-- The triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` with its third morphism negated. -/
abbrev negMor₃ (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)

/-- A triangle is distinguished up to sign if it, or the triangle with its third morphism
negated, is distinguished. -/
def DistinguishedUpToSign (T : Triangle C) : Prop :=
  T ∈ distTriang C ∨ T.negMor₃ ∈ distTriang C

namespace DistinguishedUpToSign

lemma of_distinguished {T : Triangle C} (hT : T ∈ distTriang C) : T.DistinguishedUpToSign :=
  Or.inl hT

lemma mor₁_mor₂ {T : Triangle C} (hT : T.DistinguishedUpToSign) : T.mor₁ ≫ T.mor₂ = 0 := by
  rcases hT with hT | hT
  · exact comp_distTriang_mor_zero₁₂ _ hT
  · exact comp_distTriang_mor_zero₁₂ _ hT

lemma mor₂_mor₃ {T : Triangle C} (hT : T.DistinguishedUpToSign) : T.mor₂ ≫ T.mor₃ = 0 := by
  rcases hT with hT | hT
  · exact comp_distTriang_mor_zero₂₃ _ hT
  · simpa using comp_distTriang_mor_zero₂₃ _ hT

lemma mor₃_mor₁ {T : Triangle C} (hT : T.DistinguishedUpToSign) :
    T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
  rcases hT with hT | hT
  · exact comp_distTriang_mor_zero₃₁ _ hT
  · simpa using comp_distTriang_mor_zero₃₁ _ hT

lemma coyoneda_exact₁ {T : Triangle C} (hT : T.DistinguishedUpToSign) {X : C}
    (f : X ⟶ T.obj₁⟦(1 : ℤ)⟧) (hf : f ≫ T.mor₁⟦1⟧' = 0) :
    ∃ (g : X ⟶ T.obj₃), f = g ≫ T.mor₃ := by
  rcases hT with hT | hT
  · exact Triangle.coyoneda_exact₁ _ hT f hf
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hT f hf
    exact ⟨-g, by simpa using hg⟩

lemma coyoneda_exact₂ {T : Triangle C} (hT : T.DistinguishedUpToSign) {X : C}
    (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : ∃ (g : X ⟶ T.obj₁), f = g ≫ T.mor₁ := by
  rcases hT with hT | hT
  · exact Triangle.coyoneda_exact₂ _ hT f hf
  · exact Triangle.coyoneda_exact₂ _ hT f hf

lemma coyoneda_exact₃ {T : Triangle C} (hT : T.DistinguishedUpToSign) {X : C}
    (f : X ⟶ T.obj₃) (hf : f ≫ T.mor₃ = 0) : ∃ (g : X ⟶ T.obj₂), f = g ≫ T.mor₂ := by
  rcases hT with hT | hT
  · exact Triangle.coyoneda_exact₃ _ hT f hf
  · exact Triangle.coyoneda_exact₃ _ hT f (by simpa using hf)

/-- Being distinguished up to sign is invariant under isomorphisms of triangles. -/
lemma of_iso {T T' : Triangle C} (hT : T.DistinguishedUpToSign) (e : T ≅ T') :
    T'.DistinguishedUpToSign := by
  rcases hT with hT | hT
  · exact Or.inl (isomorphic_distinguished _ hT _ e.symm)
  · refine Or.inr (isomorphic_distinguished _ hT _ ?_)
    exact Triangle.isoMk _ _ (Triangle.π₁.mapIso e.symm) (Triangle.π₂.mapIso e.symm)
      (Triangle.π₃.mapIso e.symm) (by simp) (by simp) (by simp)

/-- The five lemma for triangles distinguished up to sign: in a morphism of such triangles,
if the first and third components are isomorphisms, so is the second. -/
lemma isIso₂_of_isIso₁₃ {T T' : Triangle C} (φ : T ⟶ T') (hT : T.DistinguishedUpToSign)
    (hT' : T'.DistinguishedUpToSign) (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₂ := by
  have : Mono φ.hom₂ := by
    rw [mono_iff_cancel_zero]
    intro X f hf
    obtain ⟨x, rfl⟩ := hT.coyoneda_exact₂ f (by
      rw [← cancel_mono φ.hom₃, assoc, φ.comm₂, reassoc_of% hf, zero_comp, zero_comp])
    obtain ⟨y, hy⟩ := hT'.coyoneda_exact₁ ((x ≫ φ.hom₁)⟦(1 : ℤ)⟧') (by
      rw [← Functor.map_comp, assoc, ← φ.comm₁, ← assoc, hf, Functor.map_zero])
    have hx : x⟦(1 : ℤ)⟧' = y ≫ inv φ.hom₃ ≫ T.mor₃ := by
      rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), assoc, assoc, φ.comm₃, IsIso.inv_hom_id_assoc,
        ← hy, Functor.map_comp]
    have h0 : (x ≫ T.mor₁)⟦(1 : ℤ)⟧' = 0 := by
      rw [Functor.map_comp, hx, assoc, assoc, hT.mor₃_mor₁, comp_zero, comp_zero]
    exact (shiftFunctor C (1 : ℤ)).map_injective (by rw [h0, Functor.map_zero])
  obtain ⟨x₂, hx₂⟩ := hT.coyoneda_exact₃ (T'.mor₂ ≫ inv φ.hom₃) (by
    rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), assoc, assoc, φ.comm₃, IsIso.inv_hom_id_assoc,
      hT'.mor₂_mor₃, zero_comp])
  obtain ⟨y₁, hy₁⟩ := hT'.coyoneda_exact₂ (𝟙 _ - x₂ ≫ φ.hom₂) (by
    rw [Preadditive.sub_comp, assoc, ← φ.comm₂, ← reassoc_of% hx₂, IsIso.inv_hom_id,
      comp_id, id_comp, sub_self])
  have : IsSplitEpi φ.hom₂ := IsSplitEpi.mk' ⟨x₂ + y₁ ≫ inv φ.hom₁ ≫ T.mor₁, by
    rw [Preadditive.add_comp, assoc, assoc, φ.comm₁, IsIso.inv_hom_id_assoc, ← hy₁,
      add_sub_cancel]⟩
  exact isIso_of_mono_of_isSplitEpi _

end DistinguishedUpToSign

end Triangle

end Pretriangulated

namespace Functor

open Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The image `Φ X₃ ⟶ Φ X₂ ⟶ Φ X₁ ⟶ (Φ X₃)⟦1⟧` of a triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` under a
contravariant functor `Φ : Cᵒᵖ ⥤ D` equipped with isomorphisms `e_K : Φ K ≅ (Φ (K⟦1⟧))⟦1⟧`:
the connecting morphism is `e_{X₁}` followed by the shift of `Φ` of the connecting morphism. -/
@[simps!]
def contravariantTriangle (Φ : Cᵒᵖ ⥤ D)
    (e : ∀ K : C, Φ.obj (op K) ≅ (Φ.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧) (T : Triangle C) :
    Triangle D :=
  Triangle.mk (Φ.map T.mor₂.op) (Φ.map T.mor₁.op) ((e T.obj₁).hom ≫ (Φ.map T.mor₃.op)⟦1⟧')

/-- A contravariant functor `Φ : Cᵒᵖ ⥤ D` with isomorphisms `e_K : Φ K ≅ (Φ (K⟦1⟧))⟦1⟧` is
exact up to sign if it sends distinguished triangles of `C` to triangles
(`CategoryTheory.Functor.contravariantTriangle`) that are distinguished up to sign. -/
def IsTriangulatedUpToSignOp (Φ : Cᵒᵖ ⥤ D)
    (e : ∀ K : C, Φ.obj (op K) ≅ (Φ.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧) : Prop :=
  ∀ T ∈ distTriang C, (Φ.contravariantTriangle e T).DistinguishedUpToSign

variable {E : Type u₃} [Category.{v₃} E] [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- Composing an exact contravariant functor with a triangulated functor `F` gives an exact
contravariant functor, with the isomorphisms `F e_K` followed by the commutation of `F` with
the shift. -/
lemma IsTriangulatedUpToSignOp.comp {Φ : Cᵒᵖ ⥤ D}
    {e : ∀ K : C, Φ.obj (op K) ≅ (Φ.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧}
    (hΦ : Φ.IsTriangulatedUpToSignOp e) (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated] :
    (Φ ⋙ F).IsTriangulatedUpToSignOp
      (fun K ↦ F.mapIso (e K) ≪≫ (F.commShiftIso (1 : ℤ)).app _) := by
  intro T hT
  have iso : F.mapTriangle.obj (Φ.contravariantTriangle e T) ≅
      (Φ ⋙ F).contravariantTriangle (fun K ↦ F.mapIso (e K) ≪≫ (F.commShiftIso (1 : ℤ)).app _)
        T :=
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by
      simp [Functor.map_comp, (F.commShiftIso (1 : ℤ)).hom.naturality])
  rcases hΦ T hT with h | h
  · exact Or.inl (isomorphic_distinguished _ (F.map_distinguished _ h) _ iso.symm)
  · refine Or.inr (isomorphic_distinguished _ (F.map_distinguished _ h) _ ?_)
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by
      simp [Functor.map_comp, (F.commShiftIso (1 : ℤ)).hom.naturality])

/-- Precomposing an exact contravariant functor with a triangulated functor `G` gives an exact
contravariant functor, with the isomorphisms `e_{G K}` followed by `Φ` of the commutation of `G`
with the shift. -/
lemma IsTriangulatedUpToSignOp.op_comp {Φ : Cᵒᵖ ⥤ D}
    {e : ∀ K : C, Φ.obj (op K) ≅ (Φ.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧}
    (hΦ : Φ.IsTriangulatedUpToSignOp e) (G : E ⥤ C) [G.CommShift ℤ] [G.IsTriangulated] :
    (G.op ⋙ Φ).IsTriangulatedUpToSignOp
      (fun K ↦ e (G.obj K) ≪≫
        (shiftFunctor D (1 : ℤ)).mapIso (Φ.mapIso ((G.commShiftIso (1 : ℤ)).app K).op)) := by
  intro T hT
  refine (hΦ _ (G.map_distinguished _ hT)).of_iso ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by
    simp [← Functor.map_comp])

end Functor

namespace Pretriangulated

open Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The objects `K` at which a natural transformation `τ : Φ ⟶ Ψ` of contravariant functors
is an isomorphism are closed under isomorphisms. -/
lemma isClosedUnderIsomorphisms_isIso_app {Φ Ψ : Cᵒᵖ ⥤ D} (τ : Φ ⟶ Ψ) :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : C ↦ IsIso (τ.app (op K))) where
  of_iso {K K'} e h := by
    rw [← NatIso.isIso_app_iff_of_iso τ e.op.symm] at h
    exact h

/-- The objects `K` at which a natural transformation `τ : Φ ⟶ Ψ` of contravariant functors
is an isomorphism are stable under retracts. -/
lemma isStableUnderRetracts_isIso_app {Φ Ψ : Cᵒᵖ ⥤ D} (τ : Φ ⟶ Ψ) :
    ObjectProperty.IsStableUnderRetracts (fun K : C ↦ IsIso (τ.app (op K))) where
  of_retract h hY :=
    (MorphismProperty.isomorphisms D).of_retract (NatTrans.retractArrowApp τ h.op) hY

/-- For a natural transformation `τ : Φ ⟶ Ψ` of exact contravariant functors compatible with
the isomorphisms `e_K : Φ K ≅ (Φ (K⟦1⟧))⟦1⟧`, the objects `K` with `τ_K` an isomorphism form a
triangulated subcategory. -/
theorem isTriangulated_isIso_app {Φ Ψ : Cᵒᵖ ⥤ D} (τ : Φ ⟶ Ψ)
    (eΦ : ∀ K : C, Φ.obj (op K) ≅ (Φ.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧)
    (eΨ : ∀ K : C, Ψ.obj (op K) ≅ (Ψ.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧)
    (hΦ : Φ.IsTriangulatedUpToSignOp eΦ) (hΨ : Ψ.IsTriangulatedUpToSignOp eΨ)
    (hτ : ∀ K : C, τ.app (op K) ≫ (eΨ K).hom = (eΦ K).hom ≫ (τ.app (op (K⟦(1 : ℤ)⟧)))⟦1⟧') :
    ObjectProperty.IsTriangulated (fun K : C ↦ IsIso (τ.app (op K))) := by
  let P : ObjectProperty C := fun K ↦ IsIso (τ.app (op K))
  have := isClosedUnderIsomorphisms_isIso_app τ
  -- `Φ` and `Ψ` vanish on zero objects
  have hzero {F : Cᵒᵖ ⥤ D}
      {e : ∀ K : C, F.obj (op K) ≅ (F.obj (op (K⟦(1 : ℤ)⟧)))⟦(1 : ℤ)⟧}
      (hF : F.IsTriangulatedUpToSignOp e) : IsZero (F.obj (op (0 : C))) := by
    have h := (hF _ (contractible_distinguished (0 : C))).mor₁_mor₂
    rw [IsZero.iff_id_eq_zero, ← h]
    dsimp
    rw [(isZero_zero C).eq_of_src (0 : (0 : C) ⟶ 0) (𝟙 _), op_id, Functor.map_id, id_comp]
  -- `P` is invariant under the shift by `1`
  have hshift (K : C) : P K ↔ P (K⟦(1 : ℤ)⟧) := by
    dsimp only [P]
    rw [← isIso_comp_right_iff (τ.app (op K)) (eΨ K).hom, hτ, isIso_comp_left_iff]
    exact ⟨fun _ ↦ isIso_of_fully_faithful (shiftFunctor D (1 : ℤ)) _,
      fun _ ↦ inferInstance⟩
  have hshift' (K : C) (a : ℤ) : P K → P (K⟦a⟧) := by
    intro hK
    induction a using Int.induction_on with
    | zero => exact ObjectProperty.prop_of_iso P ((shiftFunctorZero C ℤ).app K).symm hK
    | succ n hn =>
      exact ObjectProperty.prop_of_iso P ((shiftFunctorAdd' C (n : ℤ) 1 (n + 1) rfl).app K).symm
        ((hshift _).1 hn)
    | pred n hn =>
      refine (hshift _).2 (ObjectProperty.prop_of_iso P
        ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app K) hn)
  refine
    { exists_zero := ⟨0, isZero_zero C, ?_⟩
      isStableUnderShiftBy a := ⟨fun K hK ↦ hshift' K a hK⟩
      ext₂' := ?_ }
  · exact ⟨(hzero hΨ).to_ _, (hzero hΦ).eq_of_src _ _, (hzero hΨ).eq_of_src _ _⟩
  · intro T hT h₁ h₃
    refine ObjectProperty.le_isoClosure _ _ ?_
    let φ : Φ.contravariantTriangle eΦ T ⟶ Ψ.contravariantTriangle eΨ T :=
      Triangle.homMk _ _ (τ.app _) (τ.app _) (τ.app _) (τ.naturality _) (τ.naturality _) (by
        dsimp
        rw [assoc, reassoc_of% hτ, ← Functor.map_comp, ← Functor.map_comp, τ.naturality])
    exact Triangle.DistinguishedUpToSign.isIso₂_of_isIso₁₃ φ (hΦ T hT) (hΨ T hT) h₃ h₁

end Pretriangulated

end CategoryTheory
