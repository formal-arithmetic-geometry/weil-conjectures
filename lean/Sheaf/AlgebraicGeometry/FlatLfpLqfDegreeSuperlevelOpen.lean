module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.QuasiFinite.Basic
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.FlatQuasiFiniteStratification

/-!
# Open superlevel sets of finite fibre degrees

Source: Stacks Project, More on Morphisms, Tag 086R, lemma-stratify-flat-fp-lqf,
restricted to morphisms with finite scheme-theoretic fibres
(blueprint: lem-sfb-flat-lfp-lqf-degree-superlevel-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The finite fibre degree of a flat, locally finitely presented, separated, locally
quasi-finite morphism has open superlevel sets. Neither quasi-compactness nor a uniform
bound on the degrees is required.

Source: Stacks Project, More on Morphisms, Tag 086R, lemma-stratify-flat-fp-lqf,
restricted to finite fibres (blueprint: lem-sfb-flat-lfp-lqf-degree-superlevel-open).

Proof (the node's six steps):
1. Work over an affine open `V` of the target. The inverse image is the base change
along `V.ι` by `lem-weil-pbc-open-preimage-fibre-product`. Flatness, local finite
presentation, separatedness and local quasi-finiteness persist by
`lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence` (3),
and `lem-weil-pbc-separated-lqf-base-change`. Pullback pasting identifies the fibres
and their degrees. Openness can be checked on these affine opens.
2. For a quasi-compact open `W` of the inverse image, `W → V` is quasi-compact by
`lem-weil-pbc-affine-scheme-qcqs` and `lem-weil-pbc-qcqs-morphism-permanence` (1).
It is locally quasi-finite by `lem-weil-pbc-lqf-restriction-to-opens`, hence quasi-finite
by `pqf-lem-qf-locqf-qc`. Flatness restricts because the stalk maps are unchanged;
local finite presentation restricts by principal localization, adjoining a variable
`z` with relation `gz - 1`. The diagonal is a base change of the original diagonal,
so separatedness follows from `lem-weil-pbc-closed-immersion-base-change`.
3. Each finite fibre is affine with finite-dimensional coordinate algebra by
`lem-weil-pbc-finite-over-field-affine-finite-dim`. Its underlying space is finite
discrete by `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, applied over
the residue field. The fibre of `W` and its complementary open are affine by
`lem-weil-pbc-finite-discrete-scheme-affine`. Gluing gives the product decomposition
of the original coordinate algebra into their section algebras. Thus the fibre of
`W` is finite, and its degree is at most the original degree, including multiplicities.
4. Apply `lem-weil-pbc-flat-fp-qf-stratification` to `W → V`. Test its universal property
on `Spec κ(t)`: the degree-`r` stratum consists exactly of fibres of degree `r`.
A finite-dimensional algebra over a field is finite locally free of its dimension:
a basis makes it free, and its multiplication table and unit give a finite algebra
presentation (the zero algebra is presented by the unit relation). Thus the degree
superlevel set at positive `d` is the complement of the closed set `Z_{d-1}`;
at `d = 0` it is all of `V`.
5. Choose an affine neighbourhood of each of the finitely many points of a fixed
fibre. Their finite union `W` is quasi-compact by `lem-weil-pbc-affine-scheme-qcqs`
and contains the entire fibre as an open subscheme. Hence its fibre degree is the
original degree. For the empty fibre take the empty open.
6. The desired superlevel set over `V` is the union of those for all quasi-compact
opens `W`: step 3 gives one inclusion and step 5 the other. Step 4 makes every term
open, hence the union open. Glue over the affine cover of the target. This handles
zero threshold, empty source and empty target, with no global degree bound. -/
theorem isOpen_fiber_degree_ge_of_flat_lfp_lqf {Y T : Scheme.{u}} (f : Y ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (h_lqf : f.IsLocallyQuasiFinite)
    (h_finite : ∀ t : T, IsFinite (f.fiberToSpecResidueField t)) (d : ℕ) :
    IsOpen {t : T | d ≤ (f.fiberToSpecResidueField t).finrankΓ} := by
  sorry

end AlgebraicGeometry.Scheme.Hom
