/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianComponents
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.StalkCardinality
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation

/-!
# Constructible sheaves on Noetherian schemes

Let `Λ` be a finite commutative ring and `X` a Noetherian scheme. This file collects the
stalkwise criteria for constructible étale sheaves of `Λ`-modules on `X`:

- `AlgebraicGeometry.Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf` (blueprint
  `lem-weil-pbc-lisse-generic-kernel`): on an irreducible scheme, a morphism out of a locally
  constant sheaf which is injective on the stalk at a geometric generic point is a monomorphism.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
  (blueprint `lem-weil-pbc-irreducible-lisse-strata`): a constructible sheaf is finite locally
  constant on the strata of a stratification by irreducible strata.
- `AlgebraicGeometry.Etale.exists_finset_mono_pi_lift` (blueprint
  `lem-weil-pbc-constructible-noetherian-finite-selection`): finitely many maps out of a
  constructible sheaf jointly detect the nonzero stalk elements detected by a family of maps.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono` (blueprint
  `lem-weil-pbc-constructible-subobjects-noetherian`): subsheaves of constructible sheaves are
  constructible.
- `AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_isConstructible_card` (blueprint
  `fin4-lem-stalk-constructibility-criterion`): a sheaf with finite stalks is constructible if and
  only if the loci where its stalks have a given cardinality are constructible.

The blueprint states these for abelian étale sheaves; a constructible abelian sheaf on a
Noetherian scheme has finite stalks and finitely many strata, hence is killed by some `N`, so it
is a constructible sheaf of `ℤ/N`-modules, an instance of the present setting.

The geometric stalk at a point `x : X` is taken at the geometric point
`AlgebraicGeometry.Scheme.algClosurePoint x`, with values in an algebraic closure of the residue
field of `x`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-weil-pbc-lisse-generic-kernel`: A generic stalk detects kernels in a locally
constant sheaf.

Let `S` be an irreducible scheme and `s` a geometric point of `S` lying over its generic point.
Let `F` be a locally constant sheaf of `Λ`-modules and `φ : F ⟶ G` a morphism of sheaves. If the
stalk of `φ` at `s` is injective, then `φ` is a monomorphism. -/
theorem Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf {S : Scheme.{u}}
    [IrreducibleSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ x, s.base x = genericPoint S)
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [IsLocallyConstantSheaf F]
    (φ : F ⟶ G) (hφ : Mono ((pointSmallEtale s).sheafFiber.map φ)) : Mono φ :=
  sorry

variable [Finite Λ]

/-- Blueprint `lem-weil-pbc-irreducible-lisse-strata`: Irreducible lisse strata.

Let `X` be Noetherian and `F` a constructible sheaf of `Λ`-modules on `X_ét`. Then there is a
stratification of `X` all of whose strata are (nonempty) irreducible and on each of which `F` is
finite locally constant. -/
theorem Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible {X : Scheme.{u}}
    [IsNoetherian X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ S : Stratification X, (∀ i, IsIrreducible (S.stratum i)) ∧
      ∀ i, IsFiniteLocallyConstantSheaf ((S.immersion i)^*[ModuleCat.{u + 1} Λ].obj F) :=
  sorry

/-- Blueprint `lem-weil-pbc-constructible-noetherian-finite-selection`: Noetherian finite
selection of stalk tests.

Let `X` be Noetherian, `F` a constructible sheaf of `Λ`-modules and `(φ_l : F ⟶ G_l)_{l ∈ L}` a
family of morphisms to arbitrary sheaves. Assume that at every point `x` of `X` every nonzero
element of the geometric stalk `F_x̄` is not killed by some `φ_l`. Then for a finite subset
`L₀ ⊆ L` the morphism `(φ_l)_{l ∈ L₀} : F ⟶ ∏_{l ∈ L₀} G_l` is a monomorphism. -/
theorem Etale.exists_finset_mono_pi_lift {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    {L : Type*} (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (φ : ∀ l, F ⟶ G l)
    (h : ∀ (x : X) (v : (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F), v ≠ 0 →
      ∃ l, ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.map (φ l)).hom v ≠ 0) :
    ∃ L₀ : Finset L, Mono (Pi.lift fun l : L₀ ↦ φ l) :=
  sorry

/-- Blueprint `lem-weil-pbc-constructible-subobjects-noetherian`: Subsheaves of a constructible
sheaf on a Noetherian scheme.

Let `T` be Noetherian. Every subsheaf of a constructible sheaf of `Λ`-modules on `T_ét` is
constructible. -/
theorem Scheme.IsConstructibleSheaf.of_mono {T : Scheme.{u}} [IsNoetherian T]
    {G F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ι : G ⟶ F) [Mono ι]
    [IsConstructibleSheaf F] : IsConstructibleSheaf G :=
  sorry

/-- Blueprint `fin4-lem-stalk-constructibility-criterion`: Constructibility from the
cardinalities of finite stalks.

Let `X` be Noetherian and `F` a sheaf of `Λ`-modules on `X_ét` with finite geometric stalks. For
`n ≥ 1` let `C_n` be the set of points `x` with `|F_x̄| = n`. Then `F` is constructible if and
only if every `C_n` is a constructible subset of `X`. -/
theorem Scheme.isConstructibleSheaf_iff_isConstructible_card {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteSheaf F] :
    IsConstructibleSheaf F ↔ ∀ n : ℕ, 1 ≤ n →
      IsConstructible {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj F) = n} := by
  refine ⟨fun _ n _ ↦ IsConstructibleSheaf.isConstructible_setOf_natCard F n, fun hC ↦ ?_⟩
  classical
  -- `F` is a quotient of a sum of constructible sheaves `v_! Λ`
  let G : Etale.SectionIndex F → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun i ↦ Etale.lowerShriekUnit (Λ := Λ) i.1.1.hom i.1.1.prop
  have hG (i : Etale.SectionIndex F) : IsConstructibleSheaf (G i) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.left) := i.1.2
    have : Etale i.1.1.hom := i.1.1.prop
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (X := X) i.1.1.hom
  have := Etale.epi_sigmaDesc_sectionHom F
  let φ := fun i : Etale.SectionIndex F ↦ Etale.sectionHom F i.1.1.hom i.1.1.prop i.2
  let d (S : Finset (Etale.SectionIndex F)) := finsetSigmaDesc G φ S
  -- the images of the finite subsums are constructible
  have hI (S : Finset (Etale.SectionIndex F)) : IsConstructibleSheaf (Abelian.coimage (d S)) := by
    have := isConstructibleSheaf_finsetSigma G S
    have := IsConstructibleSheaf.of_mono (kernel.ι (d S))
    exact IsConstructibleSheaf.cokernel _
  have hfin (x : X) : Finite ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F) :=
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) _ (X.algClosurePoint x))
    Module.finite_of_finite Λ
  -- the locus where the subsum indexed by `S` is surjective on stalks
  let E (S : Finset (Etale.SectionIndex F)) : Set X :=
    ⋃ n : ℕ, ({x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj (Abelian.coimage (d S))) = n + 1} ∩
      {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj F) = n + 1})
  have hE (S : Finset (Etale.SectionIndex F)) (x : X) : x ∈ E S ↔
      Function.Surjective ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.map (d S)) := by
    have := hfin x
    rw [surjective_sheafFiber_map_iff_natCard_coimage]
    simp only [E, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, h₁, h₂⟩ ↦ h₁.trans h₂.symm, fun h ↦ ?_⟩
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.card_pos (α := 
      ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj F))).ne'
    exact ⟨n, h.trans hn, hn⟩
  have hcov : (Set.univ : Set X) ⊆ ⋃ S, E S := by
    intro x _
    obtain ⟨S, hS⟩ := exists_finset_surjective_sheafFiber_map G φ (X.algClosurePoint x)
      ((ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) _ _))
    exact Set.mem_iUnion.mpr ⟨S, (hE S x).2 hS⟩
  obtain ⟨T, hT₀⟩ := (isCompact_univ (X := WithConstructibleTopology X)).elim_finite_subcover
    (fun S ↦ WithTopology.ofTopology ⁻¹' E S)
    (fun S ↦ by
      rw [WithConstructibleTopology.isOpen_iff]
      refine @isOpen_iUnion X _ (constructibleTopology X) _ fun n ↦ ?_
      exact @IsOpen.inter X (constructibleTopology X) _ _
        (IsConstructibleSheaf.isConstructible_setOf_natCard _ _).isClopen_constructibleTopology.2
        (hC _ (Nat.le_add_left 1 n)).isClopen_constructibleTopology.2)
    (fun w _ ↦ by simpa using hcov (Set.mem_univ (WithTopology.ofTopology w)))
  have hT (x : X) : x ∈ ⋃ S ∈ T, E S := by
    simpa using hT₀ (Set.mem_univ (WithTopology.toTopology _ x))
  -- the subsum indexed by `T.sup id` is an epimorphism
  have hall (x : X) : IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
      (cokernel (d (T.sup id)))) := by
    obtain ⟨S, hST, hx⟩ := Set.mem_iUnion₂.mp (hT x)
    rw [isZero_sheafFiber_cokernel_iff]
    intro m
    obtain ⟨y, hy⟩ := (hE S x).1 hx m
    exact range_sheafFiber_map_finsetSigmaDesc_mono G φ _ (Finset.le_sup (f := id) hST) ⟨y, hy⟩
  have : IsIso (0 : cokernel (d (T.sup id)) ⟶ _) :=
    isIso_of_isIso_sheafFiber_map _ fun x ↦ by
      have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj (cokernel (d (T.sup id)))) :=
        (hall x).of_iso (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app _)
      exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  have : Epi (d (T.sup id)) := Preadditive.epi_of_isZero_cokernel _ (by
    rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : cokernel (d (T.sup id)) ⟶
      cokernel (d (T.sup id))), zero_comp])
  have := hI (T.sup id)
  exact IsConstructibleSheaf.of_iso (asIso (Abelian.factorThruCoimage (d (T.sup id))))

end AlgebraicGeometry

end
