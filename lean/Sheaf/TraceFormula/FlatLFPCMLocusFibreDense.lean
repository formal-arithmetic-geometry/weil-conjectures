module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Sheaf.TraceFormula.GenericCMLocusField

/-!
# Density of the fibrewise Cohen--Macaulay locus

Source: Stacks Project, More on Morphisms, Tag 045U, label
`lemma-flat-finite-presentation-CM-open`, assertions (1) and (3)
(blueprint: lem-trf-flat-lfp-cm-locus-fibre-dense).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/-- For a flat locally finitely presented morphism, Cohen--Macaulay points are dense
in every scheme-theoretic fibre.
Source: Stacks Project, More on Morphisms, Tag 045U, assertions (1) and (3)
(blueprint: lem-trf-flat-lfp-cm-locus-fibre-dense).

Proof:
1. Fix `s` and a nonempty open `O` in the fibre, and choose a point of `O`.
   By `def-pc-scheme-fibre`, identify the fibre with the subspace over `s`, so
   `O` is the intersection with an open `W` of `X`. Choose an affine base open
   `V = Spec R` containing `s`, then use `lem-weil-pbc-affine-opens-basis` to
   choose an affine `U = Spec A` inside `W ∩ f⁻¹(V)` containing the chosen point.
   Its fibre `U_s` is nonempty and contained in `O`. Empty fibres are vacuous.
2. By `lem-weil-pbc-lfp-affine-opens-finite-presentation`, `A` has a finite
   presentation over `R`. Apply `lem-weil-pbc-affine-chart-base-change-iso` with
   `T = Spec κ(s)`; the inverse image of `V` is all of `T`. It identifies `U_s`
   with `Spec (κ(s) ⊗[R] A)`. Tensor symmetry identifies this ring with
   `B = A ⊗[R] κ(s)`. The images of the finitely many presentation generators
   generate `B` over `κ(s)`: expand elements of `A` as polynomials and tensors
   as sums of pure tensors. Thus `B` satisfies `def-weil-pbc-finite-type-algebra`.
3. Apply `lem-trf-generic-cm-locus-field` to the nonempty spectrum of `B` to
   obtain a prime with Cohen--Macaulay localization, and its point `y` in `U_s`.
   By `lem-weil-pbc-affine-open-stalk-localization`, that localization is
   isomorphic to the fibre stalk at `y`. Ring isomorphisms transport ideals,
   prime chains, and regular sequences, hence Noetherianity, Krull dimension
   (`def-weil-pbc-krull-dimension-ring`), and depth (`def-weil-pbc-depth`).
   Therefore `y` belongs to `O` and has the two asserted ring properties.
   Since `s` and `O` were arbitrary, this proves density in every fibre.
-/
theorem flat_lfp_cm_locus_fibre_dense
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] :
    ∀ (s : S) (O : Set (f.fiber s)), IsOpen O → O.Nonempty →
      ∃ x : f.fiber s, x ∈ O ∧
        IsNoetherianRing ((f.fiber s).presheaf.stalk x) ∧
        (IsLocalRing.depth (R := (f.fiber s).presheaf.stalk x)
          ((f.fiber s).presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber s).presheaf.stalk x) := by
  sorry

end
