## What changed

Proved `AlgebraicGeometry.fppf_family_isEffective_of_affine_singletons` in
`Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction`, preserving its full public
signature and all three public imports. Added a proved private coproduct-case helper
and direct private constructions restricting descent data and their isomorphisms.
The item node now records the actual proof, including the universe reduction described below.
No other library module, public definition, or target statement changes.

Change record: `coord/changes/M4-fppf-family-affine-proof-context.md` documents the extra
universes for the private helpers and `open Opposite`, which preflight classifies as a
command-interface change. The sole downstream theorem consumer retains the same signature
and public imports and needs no adaptation. The first delivery attempt was refused solely
for the missing record; nothing was pushed.

The coproduct helper follows the four existing DAG steps. It uses the specified
`fppf_family_coproduct_descent_encoding` and
`exists_fppf_affine_refinement_pullback_model` declarations. Their transport equations match:
an Over morphism with the prescribed underlying map is the encoded local point by extensionality.
For each finite affine model, `P.pullback_snd` proves P for each component, `hfinite` proves P
for their finite coproduct, and `P.cancel_left_of_respectsIso` transfers P along the model
isomorphism. All five required hypotheses on its affine singleton map are supplied by the
refinement lemma. The given affine-effectivity hypothesis applies. Base change of the fpqc
singleton uses `Precoverage.mem_coverings_of_isPullback`; the existing refinement-reflection
and affine-open-local-effectivity theorems then give singleton, and hence family, effectivity.

The public proof chooses one covering member above each point of T. This gives an fppf
subfamily with u-small indices and hence both required scheme coproducts. The local schemes,
representations, transitions and all cocycle laws are restricted directly, with P inherited.
For both families, `fppfSheafRepresentabilityDescentData` gives a global sheaf and the full
descent-data comparison. Restrict the original comparison to the selected indices and compose
with the comparison for the small family. Full faithfulness of `setSheafCoverDescent` gives an
isomorphism between the two global sheaves. The small family's effectivity makes its sheaf
representable; this transfers along the isomorphism, giving original-family effectivity.
This is the full-faithfulness step under refinement of Stacks Tag 02W0, implemented through
Tag 02W5's existing sheaf interface. It does not bypass any affine or open-local proof step.

Sources read: `descent.tex`, Tags 02W3 (`lemma-descending-types-morphisms`, affine case and
general-base gluing), 02W0 (`lemma-refine-coverings-fully-faithful`), and 023X
(`lemma-family-is-one`). The unit's realized routes are unchanged. The two new proof
dependencies have no DAG path back to this item, and the sheaf comparison module has no
Lean import path back to it (checked with `tools/import_direction.py may`).

The existing off-unit tools `lem-galois-fpqc-covering-base-change`,
`lem-galois-fpqc-refinement-reflects-effectivity`, and
`lem-galois-fpqc-effectivity-open-local` retain their approved uses. The additional
`lem-pe-set-sheaf-cover-descent` is a generic tool for unique gluing of sheaf morphisms;
the curve-zero unit supplies no such theorem. Its full-faithfulness clause is used only
for the universe reduction. Approval of that additional off-unit use is left to the
maintainer, as required; no entry was added to `tool_uses`.

LeanFinder, Loogle and grep searches ran through `msearch.py`; they found no direct
Mathlib scheme-effectivity reduction. The existing declared construction lemmas provide
the shortest route after addressing the index universe.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.fppf_family_isEffective_of_affine_singletons`.
The private helpers `isEffective_of_hasCoproducts` and `restrictData_ofObj` are proved;
`restrictData` and `restrictIso` construct all fields directly, with no holes.
Original holes: 1. Remaining holes in the item: 0. Holes added anywhere: 0.
No new intermediate statement or node was split off.

The final clean module compiled without warnings in 8.7 seconds via `lcompile.py`. The two comparison
isomorphisms are normalized with only functor-composition and forgetful-object equations;
this prevents unnecessary unfolding of the concrete sheaf pseudofunctor. Diagnostics and
the temporary reduced heartbeat setting have been removed for the delivery.

The proof uses existing named statements, including the still-unproved
`AlgebraicGeometry.fppf_family_coproduct_descent_encoding`,
`AlgebraicGeometry.exists_fppf_affine_refinement_pullback_model`, and
`AlgebraicGeometry.fppfSheafRepresentabilityDescentData`. These are existing DAG-backed
proof dependencies, not new holes or unconditional axiom-free completion of the targets.

The empty base selects an empty subfamily. The existing coproduct/refinement statements
include empty families and zero finite components, and `hfinite` is applied at the actual m,
including zero. No nonemptiness or finiteness is imposed on the original index type.

## No longer needed

Removed these unused private imports from the item:

- `Mathlib.AlgebraicGeometry.Gluing`;
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`;
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`;
- `Sheaf.AlgebraicGeometry.FppfAffineRefinement`;
- `WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs`;
- `WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum`;
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`.

The proof uses the two stated construction nodes instead of duplicating their internal
affine refinement, finite-coproduct presentation and canonical pullback arguments.
Deleted the obsolete direct approvals `lem-pc-fppf-affine-refinement`,
`lem-weil-pbc-finite-coproduct-lfp-qcqs`, and `lem-galois-fpqc-canonical-pullback-datum`
from this node's `tool_uses`. These nodes may still be needed transitively by the construction
lemmas or elsewhere. No module is withdrawn, and no global pruning claim is made.
All five original direct proof dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The item allows `I : Type (u + 1)` without coproduct hypotheses. Mathlib's scheme coproduct
instance requires `Small.{u} I`; the encoding theorem properly requires the two coproducts
explicitly. The old DAG implicitly formed these coproducts for an arbitrary large family.
An fppf cover need not have a u-small original index set (even repeated identity covers
can have large indexing types), so coverage alone cannot supply that instance. The new
point-indexed subcover and full-faithfulness transfer repair this proof gap without
changing any statement or definition. The updated node records both parts explicitly.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
