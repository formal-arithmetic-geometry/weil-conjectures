/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import WeilConjectures.AlgebraicGeometry.Sites.FieldPoints
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The trace along a finite separable field extension

Let `L/K` be a finite separable field extension of degree `d`, `a : Spec L ⟶ Spec K`, and `M`
an étale sheaf on `Spec K`. The sheaf `a_* a^* M` has sections `M(V ×_K L)` over `V`. There is a
trace `a_* a^* M ⟶ M` whose composite with the unit `M ⟶ a_* a^* M` is multiplication by `d`:
over `V ×_K N`, for a finite Galois extension `N/K` containing `L`, the trace of a section `t`
is the sum of the pullbacks of `t` along the `d` embeddings `L → N`, and this sum descends to
`V` by Galois descent (`AlgebraicGeometry.Scheme.exists_map_etaleBaseChangeFst_eq`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_unit_comp_eq_nsmul`: there is a morphism
  `r : a_* a^* M ⟶ M` with `unit ≫ r = d • 𝟙`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] [Algebra.Etale K L]
  [FiniteDimensional K L]
  (N : Type u) [Field N] [Algebra K N] [Algebra.Etale K N] [IsGalois K N]
  (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})

omit [Algebra.Etale K L] [FiniteDimensional K L] [Algebra.Etale K N] [IsGalois K N] in
/-- Restriction along `V ×_K A ⟶ V` is injective. -/
lemma injective_map_etaleBaseChangeFst (A : Type u) [CommRing A] [Algebra K A]
    [Algebra.Etale K A] [Nontrivial A] (V : (Spec (.of K)).Etale) :
    Function.Injective (M.obj.map (etaleBaseChangeFst A V).op) :=
  injective_map_of_surjective M _ (surjective_etaleBaseChangeFst V)

open scoped Classical in
/-- The sum of the pullbacks of a section over `V ×_K L` along the embeddings `L → N`. -/
noncomputable def traceSum {V : (Spec (.of K)).Etale}
    (t : M.obj.obj (op (etaleBaseChange L V))) : M.obj.obj (op (etaleBaseChange N V)) :=
  ∑ τ : L →ₐ[K] N, M.obj.map (etaleBaseChangeMap τ V).op t

omit [IsGalois K N] in
lemma traceSum_invariant {V : (Spec (.of K)).Etale} (t : M.obj.obj (op (etaleBaseChange L V)))
    (σ : N ≃ₐ[K] N) :
    M.obj.map (etaleBaseChangeMap σ.toAlgHom V).op (traceSum N M t) = traceSum N M t := by
  rw [traceSum, map_sum]
  refine Fintype.sum_equiv (AlgEquiv.arrowCongr (AlgEquiv.refl) σ) _ _ fun τ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, etaleBaseChangeMap_comp]
  rfl

include N in
/-- The trace of a section over `V ×_K L`: the section over `V` whose pullback to `V ×_K N` is
`AlgebraicGeometry.Scheme.traceSum`. -/
noncomputable def traceSection {V : (Spec (.of K)).Etale}
    (t : M.obj.obj (op (etaleBaseChange L V))) : M.obj.obj (op V) :=
  (exists_map_etaleBaseChangeFst_eq M V _ (traceSum_invariant N M t)).choose

lemma map_traceSection {V : (Spec (.of K)).Etale} (t : M.obj.obj (op (etaleBaseChange L V))) :
    M.obj.map (etaleBaseChangeFst N V).op (traceSection N M t) = traceSum N M t :=
  (exists_map_etaleBaseChangeFst_eq M V _ (traceSum_invariant N M t)).choose_spec

lemma traceSection_eq_iff {V : (Spec (.of K)).Etale} (t : M.obj.obj (op (etaleBaseChange L V)))
    (s : M.obj.obj (op V)) :
    traceSection N M t = s ↔ M.obj.map (etaleBaseChangeFst N V).op s = traceSum N M t := by
  refine ⟨fun h ↦ h ▸ map_traceSection N M t, fun h ↦ ?_⟩
  exact injective_map_etaleBaseChangeFst M N V ((map_traceSection N M t).trans h.symm)

include N in
/-- The trace as an additive map on sections. -/
noncomputable def traceHom (V : (Spec (.of K)).Etale) :
    M.obj.obj (op (etaleBaseChange L V)) →+ M.obj.obj (op V) where
  toFun := traceSection N M
  map_zero' := by
    rw [traceSection_eq_iff, map_zero, traceSum]
    simp
  map_add' t t' := by
    rw [traceSection_eq_iff, map_add, map_traceSection, map_traceSection, traceSum, traceSum,
      traceSum, ← Finset.sum_add_distrib]
    simp

lemma traceHom_naturality {V₁ V₂ : (Spec (.of K)).Etale} (f : V₁ ⟶ V₂)
    (t : M.obj.obj (op (etaleBaseChange L V₂))) :
    traceHom N M V₁ (M.obj.map (etaleBaseChangeHom L f).op t) =
      M.obj.map f.op (traceHom N M V₂ t) := by
  change traceSection N M _ = _
  rw [traceSection_eq_iff, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← etaleBaseChangeHom_fst, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  change M.obj.map _ (M.obj.map _ (traceSection N M t)) = _
  rw [map_traceSection, traceSum, traceSum, map_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, etaleBaseChangeMap_hom]

variable (L) in
/-- The sheaf `a_* a^* M` for `a : Spec L ⟶ Spec K`, with sections `M(V ×_K L)` over `V`. -/
noncomputable abbrev baseChangeSheaf : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (etaleSpec K L).hom).obj
    ((Etale.localizationRestriction AddCommGrpCat.{u + 1} (etaleSpec K L).hom
      (etaleSpec K L).prop).obj M)

/-- The trace `a_* a^* M ⟶ M` along `a : Spec L ⟶ Spec K`, computed with the help of the Galois
extension `N/K`. -/
noncomputable def traceMorphism : baseChangeSheaf L M ⟶ M where
  hom :=
    { app V := AddCommGrpCat.ofHom (traceHom N M V.unop)
      naturality V₁ V₂ f := by
        ext t
        exact traceHom_naturality N M f.unop t }

variable (L) in
/-- The unit `M ⟶ a_* a^* M` for `a : Spec L ⟶ Spec K`. -/
noncomputable abbrev baseChangeUnit : M ⟶ baseChangeSheaf L M :=
  (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} (etaleSpec K L).hom
    (etaleSpec K L).prop).unit.app M

lemma baseChangeUnit_comp_traceMorphism :
    baseChangeUnit L M ≫ traceMorphism N M = Fintype.card (L →ₐ[K] N) • 𝟙 M := by
  classical
  ext V s
  change traceSection N M (M.obj.map (etaleBaseChangeFst L V.unop).op s) = _
  rw [traceSection_eq_iff]
  rw [traceSum, Sheaf.nsmul_hom_app_apply, map_nsmul]
  change _ = ∑ τ : L →ₐ[K] N, (M.obj.map (etaleBaseChangeFst L V.unop).op ≫
    M.obj.map (etaleBaseChangeMap τ V.unop).op) s
  simp only [← Functor.map_comp, ← op_comp, etaleBaseChangeMap_fst, Finset.sum_const,
    Finset.card_univ]
  rfl

omit [Algebra.Etale K L] [Algebra.Etale K N] in
/-- If `L` embeds into the Galois extension `N`, there are `[L : K]` embeddings `L → N`. -/
lemma card_algHom_eq_finrank [Algebra.IsSeparable K L] (ι : L →ₐ[K] N) :
    Fintype.card (L →ₐ[K] N) = Module.finrank K L := by
  refine AlgHom.card_of_splits K L N fun x ↦ ?_
  rw [← minpoly.algHom_eq ι ι.injective x]
  exact Normal.splits inferInstance (ι x)

variable (L) in
/-- **The trace along a finite separable extension.** If `L/K` is finite separable and embeds
into a finite Galois extension of `K`, there is a morphism `r : a_* a^* M ⟶ M` with
`unit ≫ r = [L : K] • 𝟙`. -/
theorem exists_baseChangeUnit_comp_eq_nsmul (ι : L →ₐ[K] N) :
    ∃ r : baseChangeSheaf L M ⟶ M, baseChangeUnit L M ≫ r = Module.finrank K L • 𝟙 M := by
  have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  refine ⟨traceMorphism N M, ?_⟩
  classical
  rw [baseChangeUnit_comp_traceMorphism, ← card_algHom_eq_finrank N ι]

end AlgebraicGeometry.Scheme

namespace CategoryTheory

/-- In a preadditive category, if `f ≫ r = d • 𝟙` and `m • 𝟙 X = 0` for coprime `d` and `m`,
then `f` is a split monomorphism. -/
lemma Preadditive.exists_comp_eq_id_of_coprime {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) (r : Y ⟶ X) {d m : ℕ} (hr : f ≫ r = d • 𝟙 X) (hm : m • 𝟙 X = 0)
    (hdm : Nat.Coprime d m) : ∃ r' : Y ⟶ X, f ≫ r' = 𝟙 X := by
  refine ⟨Nat.gcdA d m • r, ?_⟩
  have h := Nat.gcd_eq_gcd_ab d m
  rw [hdm, Nat.cast_one] at h
  have hm' : (m : ℤ) • 𝟙 X = 0 := by rw [natCast_zsmul, hm]
  rw [Preadditive.comp_zsmul, hr, ← natCast_zsmul, smul_smul]
  calc ((Nat.gcdA d m * d : ℤ)) • 𝟙 X
      = ((d * Nat.gcdA d m + m * Nat.gcdB d m : ℤ) - (m * Nat.gcdB d m : ℤ)) • 𝟙 X := by ring_nf
    _ = 𝟙 X := by rw [← h, sub_smul, one_smul, mul_comm, mul_smul, hm', smul_zero, sub_zero]

end CategoryTheory
