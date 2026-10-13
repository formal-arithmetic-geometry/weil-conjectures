## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.LocalFiniteFreeScalarHomology` with a
comparison through one bounded-below K-injective resolution of the structure sheaf on Y.
The proof restricts that same resolution to U, computes there in
`HasDerivedCategory.standard`, applies the existing bounded-above finite-free model,
and composes the homology isomorphisms. The original declaration and public imports
are unchanged. Exactness and additivity are supplied through overFunctor and overEquiv;
no derived-category instance on U in the ambient universe w is assumed.

Added proof imports for `BoundedBelowInjectiveResolution`, `DerivedHomFiniteFreeModel`,
`KInjectiveRestrictOpen`, the upstream right-adjoint K-injective preservation theorem,
and the new `HomComplexRestrictScheme`. Updated the item's DAG proof to this route.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.local_finite_free_scalar_homology`
(node `lem-sc-local-finite-free-scalar-homology`) by a complete Lean assembly from
existing comparisons and one new ordinary-complex comparison. No sorry remains in
the item's module.

Added exactly one hole: `AlgebraicGeometry.homComplex_restrict_scheme`, in
`Sheaf.AlgebraicGeometry.HomComplexRestrictScheme`, node
`lem-sc-hom-complex-restrict-scheme`. Its entire proof is `by sorry`.
This is a decomposition: one upper hole closed and one strictly smaller lower hole added,
not an unconditional proof or a net hole reduction. The new assertion concerns arbitrary
ordinary complexes and restriction only; it has no derived categories, resolution,
finite-freeness, augmentation or homology-degree assumption. Existing imported declarations
may still have transitive sorry dependencies; those are not newly added holes.

## No longer needed

No original import was removed: each provides symbols or exactness instances used by the
statement or proof. The proof does not use the planned direct dependency
`lem-sc-derived-internal-hom-restrict-open` / `Sheaf.Paper.DerivedInternalHomRestrictOpen`.
Its same-universe derived restriction is replaced by ordinary complex restriction and
the common-resolution calculation. This is pruning of this item's direct route only;
other users may still need that module.

The old direct proof edge to `def-pur-hom-complex` is also unnecessary as a proof step:
its definitions remain statement dependencies, and the new ordinary-complex node still
uses it. The existing ordinary over-site comparison
`lem-sc-hom-complex-restrict-open` remains needed in the new node's plan and is not pruned.
No finite truncation of E or additional boundedness of E is used: the existing finite-free
model already handles a bounded-above source and the bounded-below unit target.

## Where the brief, the DAG or earlier work was wrong

The existing derived-open-restriction interface requires a derived category on the
over-U site in the same morphism universe w. The item intentionally supplies no such
instance. Thus that theorem alone cannot close the planned universe-changing step.
The representative computation with the same restricted K-injective complex avoids it.

The ordinary Hom restriction theorem already in the library lands on the over-U site,
whereas E lives on U.toScheme. The missing comparison is transport by the concrete
scheme over-site equivalence, not another finite-free or derived-Hom theorem.

The proof follows the existing local computation route within `sk-thm-picard-duality`;
no unit statement or unit step is bypassed. The new assertion was checked on empty U,
zero L or M, and unbounded complexes: restriction and the site equivalence preserve
all integer-indexed products, so no boundedness assumption is necessary. Its source
construction was read at https://stacks.math.columbia.edu/tag/08DL and
https://stacks.math.columbia.edu/tag/0A8X. The local literature files are absent on this
worker checkout. LeanSearch returned an internal-server error; LeanFinder and the
Mathlib grep ran and yielded no exact ordinary scheme Hom-complex comparison.

## New nodes

`lem-sc-hom-complex-restrict-scheme` states only the ordinary Hom-complex comparison
for restriction to an open subscheme. Its module is
`lean/Sheaf/AlgebraicGeometry/HomComplexRestrictScheme.lean`. The node and docstring
spell out transport of local module maps, the integer-indexed product isomorphisms,
compatibility with both compositions in the differential, and replacement of the
composite over-site functor by scheme restriction. It is a strict part of the original
argument, not the original scalar-homology assertion under another name.
No existing definition, statement or exported visibility changed. The conservative
interface checker requires `coord/changes/local-finite-free-scalar-homology-proof-context.md`
for the added local attributes; that record documents their file-local scope and the
unchanged consumer interface. No forced adaptation was needed.

## Second reading by N3

1. Compared the complete original module with the repository version using `diff`.
   The only existing declaration's signature is byte for byte identical, as is its
   docstring. All original public imports remain; all imports added to the item are
   plain proof imports. No definition or target statement changed. The change record
   correctly records file-local attributes and the theorem-local transparency option.
   Verdict: pass.
2. Read the complete assembly: ambient representative comparison, exact restriction,
   K-injectivity under the over-site functor and equivalence, computation in the
   standard local derived universe, finite-free model, and homology transport. The
   existential resolution is unpacked only inside a proof, not used to define an
   arbitrary public object. The sole new sorry is the named ordinary-complex theorem;
   no prohibited declaration or hollow definition is added. Verdict: pass, conditional
   on the explicitly reported ordinary-complex hole and existing open dependencies.
3. Read the new statement, docstring, node, and the existing open-restriction theorem.
   Restriction retains every open contained in U; conjugation by the structure-sheaf
   isomorphisms identifies local linear maps and both compositions. Products and
   additivity then identify each degree and differential, including empty opens,
   rank-zero/zero complexes, U = Y, and unbounded complexes. This statement is strictly
   the ordinary restriction part, not a restatement of scalar derived Hom homology.
   Independently searched LeanFinder, Loogle, Mathlib grep and both local source roots
   with transport/equivalence queries. No exact comparison was found; the Loogle query
   with a local identifier was unavailable to its index. Read Stacks Tags
   [08DL](https://stacks.math.columbia.edu/tag/08DL) and
   [0A8X](https://stacks.math.columbia.edu/tag/0A8X): the latter gives the product and
   signed differential used in the argument. The missing scheme-site transport is
   not a short application of the existing over-site theorem. Verdict: pass.
4. Checked the old proof dependencies against the new route. The report lists both
   removed direct edges (derived open restriction and the Hom-complex definition);
   the latter remains a statement dependency and a dependency of the new node. The
   bounded-above finite-free computation is retained. Every original public import
   supplies a signature symbol: in particular Mayer--Vietoris supplies `moduleRings`.
   The new module's public Additive import supplies `mapHomologicalComplex` in its
   signature. No realized unit statement or step is bypassed: the unit's realized
   arrays are currently empty and are unchanged. Verdict: pass.
5. Compared both node proof plans and proof-dependency unions with the Lean assembly.
   The new node has its source, searches, creation, blueprint ancestry, chapter/unit,
   Lean declaration and complete proof plan. Corrected its Lean statement field to
   the actual multiline signature verbatim. Added a plain import of
   `Sheaf.Algebra.Homology.HomComplexRestrictOpen` to the new module because its planned
   first step uses that existing theorem; it was missing from the worker's skeleton.
   Verdict: pass after these repairs.

Second reading changed only the new module's missing proof-dependency import and
its node's verbatim Lean statement record, plus this report. No additional hole was
closed or added: `AlgebraicGeometry.local_finite_free_scalar_homology` is assembled,
`AlgebraicGeometry.homComplex_restrict_scheme` remains split off (net zero).

Validation: both delivered modules compiled with `lcompile.py` (exit code 0, no
compiler warnings). Scratch copies with explicit `#print axioms` for both public
declarations compiled and reported exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`; no other axiom. The remaining `sorryAx` is consistent
with the documented new hole and imported open proof dependencies.
