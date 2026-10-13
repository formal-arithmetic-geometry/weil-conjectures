## What changed

Proved `AlgebraicGeometry.Scheme.exists_dimension_one_generalization_in_locallyPrincipal_support`
in `Sheaf.AlgebraicGeometry.Morphisms.LocallyPrincipalSupportDimensionOne`, with its signature
and existing public imports unchanged. Added the proof-only import
`Mathlib.RingTheory.Spectrum.Prime.LTSeries`.

On an affine principal chart, stalk dimension is prime height. A chain of length equal to
that height is reordered by Mathlib so its second prime contains the generator. Its second
prime has height one. The affine morphism transports that prime, its specialization, and
its support membership to the scheme. Updated the existing node's proof and proof origin
to this route. No new declarations or nodes were needed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.exists_dimension_one_generalization_in_locallyPrincipal_support`
(node `lem-sbc-locally-principal-support-dimension-one`). No `sorry` remains in the delivered
module, and no holes were added or split off.

The proof uses no other Sheaf statements. Mathlib supplies Noetherian prime finite height,
existence of a chain attaining it, chain reordering, and the height/index equality. The
argument includes the zero generator, reducible and nonreduced schemes. Positive stalk
dimension ensures the chain's index one is an actual second element; zero dimension is
excluded by the original hypothesis.

## No longer needed

No imports, nodes, or modules were removed: the original node had no proof dependencies,
and both original public imports remain necessary for its statement. The original plan's
induction on local dimension, punctured-spectrum closed point selection, and localization
transitivity are replaced by Mathlib's maximal-length chain argument; no new project
modules for those steps are needed. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier search found `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal` but missed its
chain-level consequence `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last`. Together with
`Order.height_eq_index_of_length_eq_height_last`, this proves the needed height-one detection
without splitting off the algebraic argument. The source statement in Stacks Tags 0BJG and
0BJH was checked and agrees with the unchanged theorem. There were no statement or interface
faults.

Searches: LeanFinder for a positive-dimensional Noetherian local ring and a prime containing
an element; Loogle for `ringKrullDim`; grep for stalk/height and height-one existence; local
`rg` through both library roots and Mathlib. The successful route uses the exact Mathlib
chain and affine-stalk APIs inspected in their sources.

## Second reading by G1

1. Interface: PASS. Compared the entire delivered module with the repository using
   `diff -u`: the single existing theorem signature, namespace, universes, visibility,
   docstrings and both public imports are byte-for-byte unchanged. Only its proof and
   a plain proof-only import of `Mathlib.RingTheory.Spectrum.Prime.LTSeries` were added.
   No definitions, new declarations, other modules or change records are delivered.
2. Proof: PASS. Independently compiled the module through `lcompile.py` (2.4 seconds,
   exit 0, no warnings). An item scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound` for
   `AlgebraicGeometry.Scheme.exists_dimension_one_generalization_in_locallyPrincipal_support`.
   The source contains no `sorry`, prohibited declarations, or hollow definitions.
   The auxiliary axiom command alone exceeded the line limit in the scratch copy;
   the delivered module has no such warning.
3. Split statements: PASS, vacuous. None were added or left open. Read the actual Mathlib
   sources of `Ideal.exists_ltSeries_length_eq_height`,
   `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last`, and
   `Order.height_eq_index_of_length_eq_height_last`. Positive height forces a positive
   chain length, so the `Fin` literal 1 cannot wrap to index 0. For height one the chosen
   prime is the endpoint; for generator zero all membership conditions remain valid.
   Nonreduced and reducible schemes require no extra assumptions, and the zero ring
   has no point to which the hypotheses apply. No arbitrary data is taken from a hole.
4. Route and pruning: PASS. Re-searched Mathlib with the launcher grep query
   `height.*= 1` and searched both library roots for dimension-one generalizations,
   height-one existence and the chain API. Found no shorter direct replacement.
   Read the locally-principal definition and both affine/stalk conversions used by the
   proof. The Noetherian public import supplies the hypothesis in the statement; the
   invertible-ideal public import supplies `IsLocallyPrincipal`. The new plain import
   supplies the chain-reordering proof. No imports are unused. The original node's
   `proof_deps` was empty, so `## No longer needed` is complete. Read
   `dag/units/sk-prop-input-spreading.json`: its `realized` arrays are empty and unchanged;
   this auxiliary dimension-detection proof replaces no unit statement or proof step.
   Read [Stacks Tag 0BJG](https://stacks.math.columbia.edu/tag/0BJG) and the affine
   discriminant passage in [Tag 0BJH](https://stacks.math.columbia.edu/tag/0BJH): the
   positive-dimensional local-ring result agrees with the unchanged scheme statement.
5. DAG: PASS after metadata repair. The three updated proof steps follow the Lean:
   affine support and stalk-height comparison, maximal-chain reordering and height one,
   then specialization/support/stalk transport. No project proof dependency is used.
   All other node fields match the repository. Corrected `proof_origin.kind` from
   `from-document` to `written-by-agent` and named Mathlib alongside Stacks: the actual
   argument replaces the source's induction by Mathlib's chain theorem.

Second reading changed only proof-origin metadata and added this review report.
The Lean proof needed no repair. Net holes closed: one; holes added: zero; split off: zero.
