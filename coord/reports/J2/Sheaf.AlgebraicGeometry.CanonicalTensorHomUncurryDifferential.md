## What changed

Proved `AlgebraicGeometry.schemeTensorHomUncurryGraded_comm` in
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential` without changing any existing
signature, visibility, definition, or public import. Four proved private helpers implement the
additive uncurrying identity, the tensor summand differential, coproduct assembly with abstract
projections, and specialization to the fixed Hom-complex projections. Added proof-only imports
`WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` and
`Sheaf.Algebra.Homology.HomComplexProjections`; both are used.

The argument follows [Stacks 0A90](https://stacks.math.columbia.edu/tag/0A90), whose proof refers
to the signed calculation in [Stacks 0A5Y](https://stacks.math.columbia.edu/tag/0A5Y), in the
representative setting of [Stacks 08DJ](https://stacks.math.columbia.edu/tag/08DJ). Updated only
the item's node proof fields to match the Lean argument. No unit route is bypassed.

Validation: the complete module compiled through `lcompile.py` with no errors or warnings
(48.6 seconds). All lines are at most 100 characters. Both new proof imports pass the import
cycle check. The argument handles non-adjacent degrees by the complex shape axiom; arbitrary
negative degrees, unbounded complexes, zero complexes, and zero morphisms require no extra
hypothesis. The final dry run performs the compiler and declaration probe checks again.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.schemeTensorHomUncurryGraded_comm`
(node `lem-pc-tensor-hom-uncurry-differential`).

All four private helpers are proved. The assigned module contains zero `sorry`s; this delivery
adds zero holes and splits off zero statements. This is a proof, not a decomposition into new
unproved statements. Imported declarations retain their existing dependency status.

## No longer needed

None. No original import, planned dependency node, or module is pruned. The proof adds the
already-proved projection API node `lem-sc-hom-complex-projections` to the original two proof
dependencies. No K-flat or K-injective property is used, but the fixed resolution construction
remains part of the unchanged statement and component definitions.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The original plan is correct. Direct rewrites
with the large `homComplex_exists` specification, and scheme-specific transparency checks,
were expensive. Abstracting the calculation over a ringed site and its projections, then using
the existing `homComplex_projections_exists` API, makes the proof compile within the file limit.
This requires no definition repair or adaptation of another module. The existing public theorem
is proved by specializing the complete private calculation, with no new unproved equivalent
statement. The local Stacks checkout was absent, so the cited source pages were read online.

## Second reading by J2

1. **Interface preservation — pass.** Read the entire delivered module and its diff against
   the repository version. All four existing declaration signatures, both definition bodies,
   visibility, existing options and docstrings are byte-for-byte unchanged. The sole existing
   proof replacement closes `AlgebraicGeometry.schemeTensorHomUncurryGraded_comm`; additions
   are four proved private helpers, two plain proof imports, and the author credit. The
   `stage3_delivery.diff_module` check reports no statement changes, one original hole and
   zero remaining or added holes. No change record or forced adaptation is required.
2. **Proof and axioms — pass.** Independently compiled the delivered file with `lcompile.py`
   (42.4 seconds, no errors or warnings). Compiled a scratch copy with `#print axioms` for
   every helper and all four public declarations (42.6 seconds): each lists precisely
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the proof bodies:
   no forbidden declaration, hidden hole, or data construction from an unproved existence
   theorem was added. The selected projections specialize the already-proved
   `homComplex_projections_exists`, itself `Classical.choose_spec homComplex_exists`;
   proof irrelevance makes this precisely the selection in the unchanged component.
3. **Split statements and mathematics — pass.** No statement is split off and there is no
   new node or new public statement. Read Stacks [0A90](https://stacks.math.columbia.edu/tag/0A90),
   [0A5Y](https://stacks.math.columbia.edu/tag/0A5Y), and
   [08DJ](https://stacks.math.columbia.edu/tag/08DJ). The first reduces to the signed
   module calculation in the second; the third supplies the derived representative context.
   The helper `uncurry_differential` transports exactly the projected chain-map identity,
   using additivity and braiding naturality, without a new premise on the public theorem.
   `tensor_total_d` uses the totalization summand formulas with sign `p.negOnePow`.
   `graded_uncurry_comm` checks all summands with `p+q=n`, then uses the shape axiom when
   `m` differs from `n+1`; hence negative degrees, unbounded complexes, zero complexes,
   and zero morphisms require no excluded case. No flatness or injectivity assumption is
   used in this chain-level calculation.
4. **Shortest route, imports, and units — pass.** Searched via `msearch.py` LeanFinder for
   evaluation from a Hom complex giving a chain map from the tensor total complex, and
   searched the project, upstream monoidal/Algebra sources, and Mathlib homology sources
   with `rg` for evaluation/uncurrying differential identities. LeanFinder returns tensor
   morphism and totalization constructors, not this evaluation theorem. The Loogle query
   `MonoidalClosed.uncurry` reports an unknown identifier, not a substantive no-match.
   Read `HomTensorTotal` and `HomTensorDifferential`: their Hom-complex comparison does
   not directly assert the prescribed external component equation; the present argument
   avoids an unnecessary conversion through an iterated Hom complex. Both added imports
   are proof-only and used: additive uncurrying comes from `Closed.Preadditive`, and the
   differential specification comes from `HomComplexProjections`. The original sole
   public import is needed by the unchanged signatures. Both old dependency nodes remain
   used, so `## No longer needed` is complete. Read `dag/units/sk-thm-picard-duality.json`:
   its `realized` entries are empty on the baseline and are not changed by this delivery.
   This local component calculation preserves the existing unit route. The referenced
   blueprint section source is absent on this machine; its imported text is in that record.
5. **DAG agreement — pass.** Compared the item JSON to the repository JSON: only `proof`,
   `proof_deps`, and `proof_origin` change. Read the Hom-complex specification, sheaf
   tensor-closed API and projection API against the proof. The three dependencies supply
   the fixed Hom complex, additive monoidal closed structure, and its projection
   differential formula. The node describes all four private calculations and the final
   specialization, accurately retaining the unchanged scheme statement. No new node
   metadata requires repair.

Second reading changed only this report by appending the independent review. No Lean or DAG
repair was needed. Confirmed: one of one original holes closed, zero holes added, zero
statements split off, and no import or module pruned.
