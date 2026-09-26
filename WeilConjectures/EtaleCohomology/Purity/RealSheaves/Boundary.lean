/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

@[expose] public section

/-!
# Boundary extension of a lisse Weil sheaf on a curve

Let `j : U₀ ↪ C₀` be a nonempty open of a curve with finite complement `S₀` and let `ℱ` be
lisse Weil on `U₀`. The ordinary direct image `J = j_* ℱ` is constructible, its stalk at a
boundary point `s` is the inertia invariants `V^{I_s}` of the local generic stalk, and a
residue Frobenius lift acts on those invariants.

Neither the henselization of a local ring of a scheme nor the inertia subgroup of a boundary
point exists in Mathlib, so a *boundary datum* (`AlgebraicGeometry.BoundaryDatum`) records
them as data: the open immersion with finite complement, the restriction map of Weil groups,
and at every boundary point an inertia subgroup of the geometric fundamental group of `U`
together with a residue Frobenius lift normalising it.

## Main definitions

- `AlgebraicGeometry.BoundaryDatum` : the boundary extension datum of `sk-d-real-boundary`.
- `AlgebraicGeometry.BoundaryDatum.boundaryStalk` : the boundary stalk `V^{I_s}`.

## Main statements

- `AlgebraicGeometry.BoundaryDatum.isConstructibleSheaf_lowerStar_and_surjective`
-/

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}}
  {p : C ⟶ Spec (.of K)} {pU : U ⟶ Spec (.of K)}

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

A *boundary datum* for a nonempty open `j : U₀ ↪ C₀` of a curve with finite complement `S₀`:
the restriction map `W(U₀) → W(C₀)` of Weil groups, and, at every point `s` of `C₀`, the
inertia subgroup `I_s = ker (Gal(K̄_s / K_s) → Gal(k(s)‾ / k(s)))` inside the geometric
fundamental group of `U`, together with a residue Frobenius lift of degree `e_s`
normalising it.

The henselization `𝒪_{C₀, s}^h`, its fraction field `K_s` and the inertia subgroup are not
available in Mathlib, so they are recorded as data here. -/
structure BoundaryDatum (j : U ⟶ C) (WU : WeilGroup pU) (WC : WeilGroup p) where
  /-- `j` is an open immersion. -/
  isOpenImmersion : IsOpenImmersion j
  /-- `j` is a morphism of curves over `𝔽_q`. -/
  comp_eq : j ≫ p = pU
  /-- The boundary `S₀ = C₀ \ U₀` is finite. -/
  finite_boundary : (Set.range j.base)ᶜ.Finite
  /-- The restriction map `W(U₀) → W(C₀)` of Weil groups. -/
  restrict : WU.carrier →* WC.carrier
  /-- The restriction map preserves degrees. -/
  deg_restrict : WC.deg.comp restrict = WU.deg
  /-- The inertia subgroup `I_s` at a point `s` of `C₀`. -/
  inertia : C → Subgroup WU.carrier
  /-- Inertia is contained in the geometric fundamental group `π₁(U)`. -/
  inertia_le : ∀ s, inertia s ≤ WU.geometric
  /-- A residue Frobenius lift at `s`. -/
  residueFrobenius : C → WU.carrier
  /-- The residue Frobenius lift at `s` has degree `e_s = [k(s) : 𝔽_q]`. -/
  deg_residueFrobenius (s : C) :
    WU.deg (residueFrobenius s) = Multiplicative.ofAdd (p.degreeOver s : ℤ)
  /-- The residue Frobenius lift normalises inertia, so that it acts on the invariants. -/
  normalizes_inertia (s : C) : (inertia s).map (MulAut.conj (residueFrobenius s)) = inertia s

namespace BoundaryDatum

variable {j : U ⟶ C} {WU : WeilGroup pU} {WC : WeilGroup p} (D : BoundaryDatum j WU WC)
variable (l : ℕ) [Fact l.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

The boundary stalk of `J = j_* ℱ` at a geometric point over `s`: the inertia invariants
`V^{I_s}` of the local generic stalk `V`. The residue Frobenius lift
`AlgebraicGeometry.BoundaryDatum.residueFrobenius` normalises `I_s`, hence acts on it
unambiguously. -/
noncomputable def boundaryStalk (ρ : Representation (PadicAlgCl l) WU.carrier V) (s : C) :
    Submodule (PadicAlgCl l) V :=
  Representation.invariants (ρ.comp (D.inertia s).subtype)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-i-real-boundary`: Boundary stalks and restriction to an open.

For a boundary datum: the direct image `J = j_* ℱ` of a finite locally constant sheaf is
constructible; a finite locally constant sheaf `𝒢` on all of `C₀` is the direct image of its
restriction, i.e. the unit of `j^* ⊣ j_*` at `𝒢` is an isomorphism; and the map
`π₁(U) → π₁(C)` is surjective, hence so is the Weil-group map `W(U₀) → W(C₀)`.

The identification `J_s̄ = V^{I_s}` of the boundary stalk is
`AlgebraicGeometry.BoundaryDatum.boundaryStalk`, which is equivariant for the residue
Frobenius lift by `AlgebraicGeometry.BoundaryDatum.normalizes_inertia`. -/
theorem isConstructibleSheaf_lowerStar_and_surjective
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf G] :
    Scheme.IsConstructibleSheaf (((j)_*[ModuleCat.{u + 1} Λ]).obj F) ∧
      IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) ∧
      Function.Surjective D.restrict := by
  sorry

end BoundaryDatum

end AlgebraicGeometry
