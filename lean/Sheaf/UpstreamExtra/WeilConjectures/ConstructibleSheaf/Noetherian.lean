module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.AlgebraicGeometry.NoetherianComponents
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.StalkCardinality
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation
public import WeilConjectures.AlgebraicGeometry.IrreducibleStratificationRefinement

/-! Declarations of ours that lived in the upstream file `WeilConjectures.ConstructibleSheaf.Noetherian` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Constructible sheaves on Noetherian schemes

Let `Λ` be a finite commutative ring and `X` a Noetherian scheme. This file collects the
stalkwise criteria for constructible étale sheaves of `Λ`-modules on `X`:

- `AlgebraicGeometry.Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf` (blueprint
  `lem-weil-pbc-lisse-generic-kernel`): on an irreducible scheme, a morphism out of a locally
  constant sheaf which is injective on the stalk at a geometric generic point is a monomorphism.
- `AlgebraicGeometry.Etale.exists_isConstructible_sheafFiber_map_eq_zero`: a morphism into a
  constructible sheaf whose stalk at a point vanishes has vanishing stalks on a constructible
  neighbourhood of that point.
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

open CategoryTheory Limits Topology Opposite
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

variable [Finite Λ]

private theorem mono_map_iff_of_natIso {C D : Type*} [Category* C] [Category* D]
    {P Q : C ⥤ D} (e : P ≅ Q) {M N : C} (f : M ⟶ N) :
    Mono (P.map f) ↔ Mono (Q.map f) := by
  constructor
  · intro h
    have hc : Mono (e.inv.app M ≫ P.map f) := inferInstance
    rw [← e.inv.naturality f] at hc
    exact @mono_of_mono _ _ _ _ _ _ (e.inv.app N) hc
  · intro h
    have hc : Mono (e.hom.app M ≫ Q.map f) := inferInstance
    rw [← e.hom.naturality f] at hc
    exact @mono_of_mono _ _ _ _ _ _ (e.hom.app N) hc

end AlgebraicGeometry

end
