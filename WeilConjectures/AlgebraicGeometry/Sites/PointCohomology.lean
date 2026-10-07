/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Étale cohomology of the constant sheaf `ℤ` on the spectrum of a field

The étale cohomology of the spectrum of a field `K` is the Galois cohomology of
`Gal(Kˢᵉᵖ/K)`. For the constant sheaf `ℤ` this gives:

- in degree `1`, `H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`, since a continuous
  homomorphism from a profinite group to the discrete torsion-free group `ℤ` has finite, hence
  trivial, image;
- in every positive degree, `Hⁿ(Spec k_ét, ℤ) = 0` for `k` separably closed, since then the
  Galois group is trivial.

For `k` separably closed we do not go through Galois cohomology: every étale covering of
`Spec k` has a section, so the global sections functor is exact and the constant sheaf `ℤ`,
which corepresents it, is a projective sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.surjective_app_of_epi_of_isSepClosed`: for `k` separably closed,
  an epimorphism of abelian étale sheaves on `Spec k` is surjective on global sections.
- `AlgebraicGeometry.Scheme.subsingleton_H_constantSheaf_of_isSepClosed`:
  `H^q(Spec k_ét, ℤ) = 0` for `q ≥ 1` and `k` separably closed.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_isField`:
  `H¹(Spec K_ét, ℤ) = 0` for every field `K`. The proof is `sorry`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

section IsSepClosed

variable (k : Type u) [Field k] [IsSepClosed k]

/-- The terminal object `𝟙 : Spec k ⟶ Spec k` of the small étale site of `Spec k`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of k)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of k)))

/-- Over a separably closed field `k`, every covering sieve of `Spec k` in the small étale site
contains the identity: some member of an étale covering is nonempty, and a nonempty étale
`k`-scheme has a `k`-point. -/
lemma id_mem_of_mem_smallEtaleTopology_of_isSepClosed (R : Sieve 𝟙ₑ)
    (hR : R ∈ (Spec (.of k)).smallEtaleTopology 𝟙ₑ) : R.arrows (𝟙 _) := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (default : Spec (.of k))
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) (𝟙 _) y (by rw [hy]; rfl)
  have hmem : R.arrows ((𝒰.f j).asOverProp _) := hle _ _ (Presieve.ofArrows.mk j)
  convert R.downward_closed hmem (MorphismProperty.Over.homMk (A := 𝟙ₑ)
    (B := (𝒰.X j).asOverProp _ (p j)) l (by
      change l ≫ (𝒰.X j ↘ _) = 𝟙 _
      rw [← comp_over (𝒰.f j), ← Category.assoc, hl, Category.id_comp]
      rfl))
  exact MorphismProperty.Over.Hom.ext hl.symm

/-- Over a separably closed field `k`, an epimorphism of abelian étale sheaves on `Spec k` is
surjective on global sections. -/
lemma surjective_app_of_epi_of_isSepClosed
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op 𝟙ₑ)) := by
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isSepClosed k _
    (Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology φ.hom (U := op 𝟙ₑ) s)
  exact ⟨t, ht.trans (by simp)⟩

instance preservesEpimorphisms_sheafSections_of_isSepClosed :
    ((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op 𝟙ₑ)).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).2
    (surjective_app_of_epi_of_isSepClosed k φ)

/-- Over a separably closed field `k`, the constant sheaf `ℤ` on the small étale site of
`Spec k` is projective: it corepresents the global sections functor, which is exact. -/
instance projective_constantSheaf_of_isSepClosed :
    Projective ((constantSheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) := by
  have hT : Limits.IsTerminal 𝟙ₑ := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  exact @Adjunction.map_projective _ _ _ _ _ _ (constantSheafAdj _ _ hT)
    (preservesEpimorphisms_sheafSections_of_isSepClosed k) _ AddCommGrpCat.projective_of_uliftInt

/-- **Cohomology of `ℤ` on a geometric point.** For a separably closed field `k` (in
particular an algebraically closed one), `H^q(Spec k_ét, ℤ) = 0` for all `q ≥ 1`. The
blueprint argues via the equivalence of étale sheaves on `Spec k` with discrete Galois modules,
the Galois group being trivial; we use directly that the constant sheaf `ℤ` is projective
(`AlgebraicGeometry.Scheme.projective_constantSheaf_of_isSepClosed`).
(blueprint: `lem-sc-point-z-cohomology`) -/
theorem subsingleton_H_constantSheaf_of_isSepClosed (q : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) (q + 1)) :=
  Abelian.Ext.subsingleton_of_projective _ _ _

end IsSepClosed

section Field

variable {K : Type u} [Field K]

/-- The terminal object `𝟙 : Spec K ⟶ Spec K` of the small étale site of `Spec K`. -/
local notation "𝟙ₖ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))

/-- A finite subset of `ℤ` which is closed under addition is contained in `{0}`. -/
private lemma eq_zero_of_finite_of_add_mem {S : Set (ULift.{u + 1} ℤ)} (hS : S.Finite)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {a : ULift.{u + 1} ℤ} (ha : a ∈ S) : a = 0 := by
  by_contra h
  have hmem (n : ℕ) : (n + 1) • a ∈ S := by
    induction n with
    | zero => simpa using ha
    | succ n ih => simpa [add_smul, one_smul] using hadd _ ih _ ha
  refine Set.not_infinite.2 hS (Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ (n + 1) • a)
    (fun n m hnm ↦ ?_) hmem)
  have hd : ((n : ℤ) + 1) * a.down = ((m : ℤ) + 1) * a.down := by
    simpa using congrArg ULift.down hnm
  have ha' : a.down ≠ 0 := fun h' ↦ h (ULift.ext _ _ h')
  exact_mod_cast add_right_cancel (mul_right_cancel₀ ha' hd)

open Algebra.TensorProduct TensorProduct in
/-- **Every `ℤ`-torsor on `Spec K` is trivial.** For a short exact sequence
`0 → ℤ → E → Q → 0` of abelian sheaves on the small étale site of the spectrum of a field `K`,
every global section of `Q` lifts to `E`.

A global section `q` of `Q` lifts to a section `e` of `E` over `Spec L` for a finite separable
extension `L` of `K`. The difference of the two pullbacks of `e` to
`Spec (L ⊗_K L) = Spec L ×_{Spec K} Spec L` is a section `c` of `ℤ`, that is, a function on the
finite set of points of `Spec (L ⊗_K L)`, since every étale `K`-scheme is discrete
(`AlgebraicGeometry.Scheme.isIso_constantSheafToPointFunctionSheaf`). The cocycle identity shows
that the finite set of values of `c` is closed under addition, so `c = 0`: this is the
vanishing of `Hom(Gal(L/K), ℤ)` for the finite Galois group, without naming the group. Hence `e`
descends to `Spec K` (`AlgebraicGeometry.Scheme.exists_app_eq_of_compatible`). -/
theorem surjective_app_of_shortExact_constantSheaf_int
    {E Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ E) (π : E ⟶ Q) (w : ι ≫ π = 0)
    (hS : (ShortComplex.mk ι π w).ShortExact) : Function.Surjective (π.hom.app (op 𝟙ₖ)) := by
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let P := (Spec (.of K)).pointFunctionSheaf M
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  have := (Spec (.of K)).isIso_constantSheafToPointFunctionSheaf M
    discreteTopology_of_etale_of_unique
  -- replace `ℤ` by the isomorphic sheaf `P : V ↦ (V → ℤ)` of functions on points
  let ι' : P ⟶ E := inv ((Spec (.of K)).constantSheafToPointFunctionSheaf M) ≫ ι
  have w' : ι' ≫ π = 0 := by simp [ι', w]
  have hS' : (ShortComplex.mk ι' π w').ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk ι π w) (ShortComplex.isoMk
      (asIso ((Spec (.of K)).constantSheafToPointFunctionSheaf M)) (Iso.refl _) (Iso.refl _)
      (by simp [ι']) (by simp)) hS
  have := hS'.mono_f
  have := hS'.epi_g
  have (U : (Spec (.of K)).Etaleᵒᵖ) : Limits.PreservesLimits
      ((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) :=
    inferInstanceAs
      (Limits.PreservesLimits (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U))
  have hι (U) : Function.Injective (ι'.hom.app U) :=
    (AddCommGrpCat.mono_iff_injective _).1
      (((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U).map_mono ι')
  have hexact (U) (x : E.obj.obj U) (hx : π.hom.app U x = 0) : ∃ g, ι'.hom.app U g = x :=
    (ShortComplex.ab_exact_iff _).1 (hS'.exact.map_of_mono_of_preservesKernel
      ((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U)
      hS'.mono_f inferInstance) x hx
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) π).2 inferInstance
  intro q
  obtain ⟨L, _, _, _, f, e, he⟩ := exists_etaleSpec_field_mem_of_mem_smallEtaleTopology _
    (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology π.hom (U := op 𝟙ₖ) q)
  refine exists_app_eq_of_compatible π L f q e he ?_
  -- the difference of two pullbacks of `e` is a section of `P`
  have hπ {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L) :
      π.hom.app _ (E.obj.map g₁.op e - E.obj.map g₂.op e) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, he,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, hT.hom_ext (g₁ ≫ f) (g₂ ≫ f), sub_self]
  choose c hc using fun (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) ↦
    hexact _ _ (hπ g₁ g₂)
  have hc_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      P.obj.map h.op (c Z g₁ g₂) = c Z' (h ≫ g₁) (h ≫ g₂) := by
    apply hι
    rw [NatTrans.naturality_apply, hc, hc, map_sub, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
      ← op_comp]
  have hc_add {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      c Z g₁ g₃ = c Z g₁ g₂ + c Z g₂ g₃ := by
    apply hι
    rw [map_add, hc, hc, hc]
    abel
  -- the Čech cocycle on `Spec (L ⊗_K L)`, a function on a finite set of points
  let i₁ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeLeft
  let i₂ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeRight
  let c₀ : (etaleSpec K (L ⊗[K] L)).left → ULift.{u + 1} ℤ := c _ i₁ i₂
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have : IsArtinianRing (L ⊗[K] L) := IsArtinianRing.of_finite K _
  have hfin : Finite (etaleSpec K (L ⊗[K] L)).left :=
    inferInstanceAs (Finite (PrimeSpectrum (L ⊗[K] L)))
  have hadd : ∀ a ∈ Set.range c₀, ∀ b ∈ Set.range c₀, a + b ∈ Set.range c₀ := by
    rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩
    obtain ⟨Z, p₁, p₂, z, hp, rfl, rfl⟩ := exists_eq_of_apply_eq i₂ i₁ w₁ w₂
      (@Subsingleton.elim (Spec (.of L)) _ _ _)
    obtain ⟨h, hh₁, hh₂⟩ := exists_comp_etaleSpecMap_includeLeft_eq (p₁ ≫ i₁) (p₂ ≫ i₂)
    refine ⟨h.left z, ?_⟩
    have e₁ : c Z (p₁ ≫ i₁) (p₂ ≫ i₂) = P.obj.map h.op c₀ := by
      have := hc_map h i₁ i₂
      rw [hh₁, hh₂] at this
      exact this.symm
    have e₂ : c Z (p₁ ≫ i₁) (p₁ ≫ i₂) = P.obj.map p₁.op c₀ := (hc_map _ _ _).symm
    have e₃ : c Z (p₁ ≫ i₂) (p₂ ≫ i₂) = P.obj.map p₂.op c₀ := by
      rw [hp]
      exact (hc_map _ _ _).symm
    have := hc_add (p₁ ≫ i₁) (p₁ ≫ i₂) (p₂ ≫ i₂)
    rw [e₁, e₂, e₃] at this
    exact congrFun this z
  have hc₀ : c₀ = 0 := funext fun w ↦ eq_zero_of_finite_of_add_mem (Set.finite_range c₀) hadd
    ⟨w, rfl⟩
  intro Z g₁ g₂
  obtain ⟨h, rfl, rfl⟩ := exists_comp_etaleSpecMap_includeLeft_eq g₁ g₂
  have h₀ : c Z (h ≫ i₁) (h ≫ i₂) = 0 := by
    rw [← hc_map]
    change P.obj.map h.op c₀ = 0
    rw [hc₀, map_zero]
  rw [← sub_eq_zero, ← hc, h₀, map_zero]

variable (K) in
/-- **`H¹` of `ℤ` on the spectrum of a field vanishes.** For every field `K`,
`H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`, since a continuous homomorphism from the
profinite group `Gal(Kˢᵉᵖ/K)` to the discrete group `ℤ` has finite image, hence is trivial.
Here the comparison with Galois cohomology is bypassed: every `ℤ`-torsor on `Spec K` is
trivial by descent along a finite separable extension
(`AlgebraicGeometry.Scheme.surjective_app_of_shortExact_constantSheaf_int`). -/
theorem subsingleton_H_one_constantSheaf_of_field :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of K)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) 1) :=
  Sheaf.subsingleton_H_one_of_surjective _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K)))
    (fun _ _ ι π w hS ↦ surjective_app_of_shortExact_constantSheaf_int ι π w hS)

end Field

/-- **`H¹` of `ℤ` on the spectrum of a field vanishes.** For every field `K`,
`H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`: étale cohomology of `Spec K` is Galois
cohomology, and a continuous homomorphism from the profinite group `Gal(Kˢᵉᵖ/K)` to the
discrete group `ℤ` has finite image, hence is trivial. This is the version for a commutative
ring which is a field, see `AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_field`.
(blueprint: `lem-sc-brauer-injectivity`, Step 2) -/
theorem subsingleton_H_one_constantSheaf_of_isField (K : CommRingCat.{u}) (hK : IsField K) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec K).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) 1) := by
  let := hK.toField
  exact subsingleton_H_one_constantSheaf_of_field K

end AlgebraicGeometry.Scheme
