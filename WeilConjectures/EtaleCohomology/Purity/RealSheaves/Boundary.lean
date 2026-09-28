/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

/-!
# Boundary extension of a lisse Weil sheaf on a curve

Let `j : U₀ ↪ C₀` be a nonempty open of a curve with finite complement `S₀` and let `ℱ` be
lisse Weil on `U₀`. The ordinary direct image `J = j_* ℱ` is constructible, its stalk at a
boundary point `s` is the inertia invariants `V^{I_s}` of the local generic stalk, and a
residue Frobenius lift acts on those invariants.

Neither the henselization of a local ring of a scheme nor the inertia subgroup of a boundary
point exists in Mathlib, so a *boundary datum* (`AlgebraicGeometry.BoundaryDatum`) records
them as data on top of a `AlgebraicGeometry.WeilGroup.Restriction`: the finiteness of the
boundary, and at every boundary point an inertia subgroup of the geometric fundamental group
of `U` together with a residue Frobenius lift normalising it and restricting into the
Frobenius class of that point.

Inertia and the residue Frobenius are indexed by the boundary `S₀ = C₀ \ U₀` alone: they carry
no meaning at a point of `U₀`, and `deg_residueFrobenius` would be a statement about the junk
value of `AlgebraicGeometry.Scheme.Hom.degreeOver` at a non-closed point. The field
`boundary_subset_finitePoints` records that the boundary of an open subcurve consists of closed
points, which is what makes the residue degree `e_s` meaningful.

## Main definitions

- `AlgebraicGeometry.BoundaryDatum` : the boundary extension datum of `sk-d-real-boundary`.
- `AlgebraicGeometry.BoundaryDatum.boundaryStalk` : the boundary stalk `V^{I_s}`.

## Main statements

- `AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerStar`
- `AlgebraicGeometry.Scheme.isIso_unit_upperStarLowerStarAdjunction`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}}
  {p : C ⟶ Spec (.of K)} [IsCurve p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

A *boundary datum* for a nonempty open `j : U₀ ↪ C₀` of a curve: a restriction
`AlgebraicGeometry.WeilGroup.Restriction` of Weil groups along `j`, the finiteness of the
boundary `S₀ = C₀ \ U₀`, and, at every boundary point `s`, the inertia subgroup
`I_s = ker (Gal(K̄_s / K_s) → Gal(k(s)‾ / k(s)))` inside the geometric fundamental group of `U`,
together with a residue Frobenius lift of degree `e_s` normalising it and lying, after
restriction to `W(C₀)`, in the Frobenius conjugacy class at `s`.

The henselization `𝒪_{C₀, s}^h`, its fraction field `K_s` and the inertia subgroup are not
available in Mathlib, so they are recorded as data here. -/
structure BoundaryDatum (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] (WU : WeilGroup pU)
    (WC : WeilGroup p) extends WeilGroup.Restriction j WU WC where
  /-- The boundary `S₀ = C₀ \ U₀` is finite. -/
  finite_boundary : (Set.range j.base)ᶜ.Finite
  /-- Every boundary point is a closed point of `C₀`, so its residue degree `e_s` is
  meaningful. -/
  boundary_subset_finitePoints : (Set.range j.base)ᶜ ⊆ C.finitePoints
  /-- The inertia subgroup `I_s` at a boundary point `s`. -/
  inertia : ↥((Set.range j.base)ᶜ) → Subgroup WU.carrier
  /-- Inertia is contained in the geometric fundamental group `π₁(U)`. -/
  inertia_le (s : ↥((Set.range j.base)ᶜ)) : inertia s ≤ WU.geometric
  /-- A residue Frobenius lift at a boundary point `s`. -/
  residueFrobenius : ↥((Set.range j.base)ᶜ) → WU.carrier
  /-- The residue Frobenius lift at `s` has degree `e_s = [k(s) : 𝔽_q]`. -/
  deg_residueFrobenius (s : ↥((Set.range j.base)ᶜ)) :
    WU.deg (residueFrobenius s) = Multiplicative.ofAdd (p.degreeOver s.1 : ℤ)
  /-- The residue Frobenius lift at `s` restricts into the Frobenius conjugacy class at `s`;
  this is what makes `V ^ (I_s)` with its residue-Frobenius action compute the stalk of
  `j_* ℱ`. -/
  restrict_residueFrobenius (s : ↥((Set.range j.base)ᶜ)) :
    IsConj (WC.frobenius ⟨s.1, boundary_subset_finitePoints s.2⟩)
      (restrict (residueFrobenius s))
  /-- The residue Frobenius lift normalises inertia, so that it acts on the invariants. -/
  normalizes_inertia (s : ↥((Set.range j.base)ᶜ)) :
    (inertia s).map (MulAut.conj (residueFrobenius s)) = inertia s

namespace BoundaryDatum

variable {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} {WC : WeilGroup p}
  (D : BoundaryDatum j WU WC)
variable (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

The boundary stalk of `J = j_* ℱ` at a geometric point over a boundary point `s`: the inertia
invariants `V^{I_s}` of the local generic stalk `V`. The residue Frobenius lift
`AlgebraicGeometry.BoundaryDatum.residueFrobenius` normalises `I_s`, hence acts on it
unambiguously. -/
noncomputable def boundaryStalk (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) : Submodule (PadicAlgCl l) V :=
  Representation.invariants (ρ.comp (D.inertia s).subtype)

end BoundaryDatum

namespace Scheme

variable {j : U ⟶ C} [IsOpenImmersion j] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-i-real-boundary`: Boundary stalks and restriction to an open.

The direct image `j_* ℱ` of a finite locally constant sheaf along an open immersion with finite
complement is constructible: it is finite locally constant on `U₀`, and on the finite boundary
its stalks are the inertia invariants of the generic stalk, which are finite. -/
theorem isConstructibleSheaf_lowerStar (hfin : (Set.range j.base)ᶜ.Finite)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F] :
    Scheme.IsConstructibleSheaf (((j)_*[ModuleCat.{u + 1} Λ]).obj F) := by
  sorry

/-- Blueprint `sk-i-real-boundary`: Boundary stalks and restriction to an open.

A finite locally constant sheaf `𝒢` on a smooth curve `C₀` is the direct image of its
restriction to a dense open `U₀`: the unit of the adjunction `j^* ⊣ j_*` is an isomorphism
at `𝒢`,

```
    𝒢 ──────▶ j_* j^* 𝒢
```

because `C₀` is normal and `U₀` is dense, so a finite étale cover of `U₀` extends uniquely to
a finite étale cover of `C₀`. -/
theorem isIso_unit_upperStarLowerStarAdjunction [SmoothOfRelativeDimension 1 p]
    (hdense : Dense (Set.range j.base)) (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf G] :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) := by
  sorry

end Scheme

end AlgebraicGeometry
