/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianComponents
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

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
        (A := ModuleCat.{u + 1} Λ) |>.obj F) = n} :=
  sorry

end AlgebraicGeometry

end
