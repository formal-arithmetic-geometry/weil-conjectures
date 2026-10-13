## What changed

Corrected the false arbitrary-completion interface of
`CategoryTheory.Functor.leftDerived_value_triangle_extension_compat` to existence
of a completion satisfying both distinguishedness and the shifted cone equation.
The change record is
`coord/changes/leftDerived_value_triangle_extension_compat.md`.
The one caller, `Sheaf.CategoryTheory.DerivedFunctorValueTriangle`, now consumes
that existential witness and reorders its conjuncts. Its signature is unchanged.
The compatibility theorem remains an open construction obligation with a complete
source-based proof in words. Its proof-dependency imports are private imports.

The completion module is unchanged: it provides distinguishedness only. The
first report's claim that it also supplies compatibility was false. Removed
unchanged dependency copies from the sandbox to avoid delivering stale sources.

## Proved and sorry left

Holes closed: none (0 of 1 in the item). Holes added: none. No new split-off
statement is introduced. The remaining hole is
`CategoryTheory.Functor.leftDerived_value_triangle_extension_compat`, node
`lem-pur-derived-functor-triangles-05sc-value-triangle-compatibility`.
`CategoryTheory.Functor.leftDerived_value_triangle_extension` was already
syntactically proved; its adapted proof still depends on the remaining hole.

This is an interface correctness repair, not proof progress or a decomposition.
The corrected compatibility conclusion is equivalent to the value-triangle
conclusion up to conjunct order; its application closes no existing hole. The
old false universal implication has not been proved. The ledger must measure
import-closure changes against its pinned baseline; no net hole reduction is
claimed here.

## No longer needed

Removed proof-only imports from the adapted value-triangle wrapper:
`Sheaf.CategoryTheory.LeftDerivedValueMorphism`,
`Sheaf.CategoryTheory.DerivedFunctorShift`, and
`Sheaf.CategoryTheory.DerivedFunctorValueTriangleCompletion`.
The first two remain imported by the compatibility construction plan.
The completion node is not used by the repaired wrapper or compatibility theorem:
`lem-pur-derived-functor-triangles-05sc-value-triangle-completion`.
Its statement is unchanged and its construction cannot establish compatibility.
Source import search shows the completion module's only importer was the wrapper;
its private chain `Sheaf.CategoryTheory.DerivedFunctorFixedConeHomColimit` and
`Sheaf.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit` likewise has
no other importers. These three modules leave this branch of the import closure.
This pruning accompanies the correctness repair and is not a claimed proof.

The following old value-triangle proof dependencies are no longer directly used
by that wrapper; they remain the plan of the still-open compatibility construction:

- `lem-pur-derived-functor-morphisms-05sa` (now part of the compatibility construction plan, not used by the wrapper proof).
- `def-pur-saturated-triangulated-localization` (now part of the compatibility construction plan, not used by the wrapper proof).
- `def-pc-essentially-constant-pro-diagram` (now part of the compatibility construction plan, not used by the wrapper proof).
- `def-weil-triangulated-category` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-pur-triangle-morphism-category-05r9` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-pur-essential-constant-cofinal-0a1s` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-weil-pbc-five-lemma` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-pc-essentially-constant-pro-hom-colimit` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-pur-essential-constant-pro-criterion-05py` (now part of the compatibility construction plan, not used by the wrapper proof).
- `lem-pur-derived-functor-shift-05su` (now part of the compatibility construction plan, not used by the wrapper proof).

Removed the spurious completion dependency added to the compatibility node by
the first worker. Removed the redundant direct EssentiallyConstantPro import;
the statement's public saturated-system import supplies its definitions.

## Where the brief, the DAG or earlier work was wrong

The old theorem is false: for the identity functor and isomorphism denominators,
the split triangle X → 0 → X[1] has distinguished completions with third map
both identity and negative identity. The fixed cone equation at identity
denominators requires identity. Over ℚ these differ. The scratch SignAmbiguity
proof certifies the distinguished negative-identity completion and, assuming
identity differs from negative identity, its difference from the original map.
It does not instantiate every hypothesis of the old theorem in a concrete
rational triangulated category; that instantiation is the mathematical
counterexample above. Its axiom printout uses only the three standard axioms.

The first worker's report and completion-node signature said that the completion
construction supplied compatibility, although its Lean signature and proof do
not. Its revised compatibility docstring invoked that nonexistent result. All
three errors are repaired. The corrected existential obligation is the full
construction, so it must not be advertised as a strictly smaller split.
The source [Stacks 05SC](https://stacks.math.columbia.edu/tag/05SC) constructs a
triangle comparison and transports its third square; it does not deduce that
square from distinguishedness alone.

## Forced adaptations

`Sheaf.CategoryTheory.DerivedFunctorValueTriangle` (unclaimed): the original proof
passes `lh` and `hdist` to a theorem that now returns an existential pair, so
the original application no longer type-checks. The adapted proof obtains
`lh`, `hdist`, `hcompat` from the corrected construction and returns
`⟨lh, hcompat, hdist⟩`. Removing the imports for the superseded calls leaves
only the interface import and the corrected construction import. No signature,
visibility, or definition changes in this module. The delivery tool records the
original compiler failure against the changed dependencies and verifies the
adapted file.

## New nodes

None. The existing compatibility node has a proper statement-change record,
its exact Lean signature, and the complete construction plan. The value-triangle
node now records the existential elimination actually present in its Lean proof.
The unchanged completion node is excluded from this delivery.

## Earlier second reading (a previous round; superseded)

1. Compared every sandbox source with the repository. Only the compatibility
   signature changes, explicitly recorded with its full old and new signatures.
   The caller's signature is byte-for-byte unchanged; there are no definition
   changes or target-statement changes. Unchanged source copies were excluded.
2. Compiled the supplied files through lcompile.py. There is one named open
   theorem in the delivered files, as listed above; no forbidden declarations,
   hollow definitions, or arbitrary data from an unproved existence theorem.
   The axiom checks allow only the three standard axioms and the reported open
   theorem's sorryAx. This is a correctness repair, not a complete proof.
3. No new or split-off statements. Checked the isomorphism-denominator case,
   split and zero triangles. The old universal assertion fails the sign test;
   the existential repair permits the compatible sign. Searched via LeanFinder,
   msearch grep and repository rg with third-vertex, retraction, fixed-cone and
   shift-cone queries. The existing Kan comparison assumes the third equation
   and global pointwise Kan existence; the weaker core supplies no third
   equation. Neither closes this construction obligation.
4. Read top-down: no shorter noncircular proved result supplies compatibility.
   Removed the wrapper's obsolete proof imports, retained only the pending
   construction's proof-dependency imports, and recorded every discarded old
   wrapper dependency above. The unit sk-def-sf-operations has empty realized
   statement/step arrays, so this repair bypasses no realized unit route.
5. Repaired the exact compatibility Lean signature in its node, removed the
   incorrect completion-node edit, and updated both proof plans and dependency
   unions. The corrected node explicitly records the false universal premise,
   its replacement, its source and all base DAG citers. The value-triangle node
   describes its actual existential elimination. No new nodes are needed.

Second reading changed the false completion claims and docstring, the malformed
statement-change record, stale completion-node edit, dependency plans and
imports, and the report's progress accounting. The mathematical interface repair
and minimal forced caller adaptation are retained.

Verification: both delivered files compile without errors or warnings. Scratch
copies with `#print axioms` show exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` for both the remaining compatibility obligation and
the repaired value-triangle wrapper. The SignAmbiguity counterexample lemmas
use only the three standard axioms. The delivery dry run prints OK, including
the original-caller failure against the changed compatibility interface and the
adapted-caller compile. Review class is CODEX because this is an interface repair.

## Forced adaptations

### Sheaf.CategoryTheory.DerivedFunctorValueTriangle
Original against changed dependencies failed:
```
/tmp/forced-adaptation-2m076zha/lean/Sheaf/CategoryTheory/DerivedFunctorValueTriangle.lean:103:8: error: Function expected at
  leftDerived_value_triangle_extension_compat F S hS T hT LX LY LZ hX hY hZ uX uY uZ huX huY huZ lf lg hf hg
but this term has type
  ∃ lh,
    Triangle.mk lf lg lh ∈ distinguishedTriangles ∧
      ∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁) (h' : s.left ⟶ (shiftFunctor C 1).obj s'.left),
        s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C 1).map s'.hom →
          uZ.app s ≫ F.map h' = lh ≫ (shiftFunctor D 1).map (uX.app s') ≫ (commShiftIso F 1).inv.app s'.left

Note: Expected a function because this term is being applied to the argument
  lh

(with the modules compiled into /tmp/forced-adaptation-2m076zha/.lbuild) [1.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by J3

1. Compared both delivered Lean files and both node files with the repository
   using textual diffs. The only changed existing signature is
   `CategoryTheory.Functor.leftDerived_value_triangle_extension_compat`, whose
   old and new signatures match the change record verbatim. The caller's
   signature and docstring are byte-for-byte unchanged. No definitions or
   targets change. The sole source caller is the forced adaptation in
   `Sheaf.CategoryTheory.DerivedFunctorValueTriangle`. Verdict: recorded
   interface correction, with no accidental visible change.
2. Independently compiled the delivered set with lcompile.py, then compiled
   ReviewAxioms and SignAmbiguity scratch files. Both delivered declarations
   have exactly propext, Classical.choice, Quot.sound and the reported sorryAx;
   the two sign-ambiguity lemmas have only the standard three axioms. Exactly
   one named theorem remains sorry; no forbidden declaration, hollow definition
   or witness-selection definition occurs in either delivered file. Verdict:
   valid partial delivery, zero holes closed and zero holes added.
3. No new statements or split-off nodes are delivered. Read the corrected
   existential construction against Stacks 05SC's triangle comparison and
   five-lemma argument (https://stacks.math.columbia.edu/tag/05SC). For identity
   denominators, the cone equation fixes the original third map; the split
   triangle with a zero middle vertex permits both signs as distinguished
   completions. At the zero triangle these agree and the existential conclusion
   holds. Changing the signs of supplied value-cone identifications transports
   the entire triangle, rather than imposing an arbitrary third map. Fresh
   LeanFinder search for local derived values and connecting-map compatibility
   returns specialized cochain-complex/short-exact-sequence constructions;
   msearch grep returns general triangulated-functor APIs, which presuppose a
   globally constructed functor. Repository searches confirm that the existing
   completion core supplies no third-square equation. Verdict: true correction;
   no short noncircular proof of the remaining full construction found.
4. Read the wrapper first, then the compatibility plan and the completion core.
   The wrapper is existential elimination and conjunct reordering, explicitly
   not new proof progress. Its removed imports and all eleven old direct DAG
   dependencies appear under No longer needed. The completion module and its
   fixed-cone/retraction Hom-colimit chain have no other source importers;
   their removal prunes this branch. The compatibility imports are public only
   for its signature, private for its pending proof plan. The unit
   sk-def-sf-operations has empty realized statement and step lists. Verdict:
   no realized unit route bypassed and no equivalent split advertised as a proof.
5. Checked both node signatures against the Lean text exactly and checked that
   each proof_deps list equals the union of its proof steps' uses. The wrapper
   node records its actual single dependency; the compatibility node records
   the remaining construction plan. The base DAG has no citers of the old
   compatibility node, matching statement_change.citers. There are no new
   nodes requiring creation metadata. Verdict: records agree with the delivery.

This reading clarified that the compiled sign test is conditional, rather
than a fully instantiated Lean refutation of the old theorem. No Lean proof or
signature needed a further edit. A trial correction of the statement-change
author label to "J3 stage 3" was rejected by preflight: the metadata convention
requires "<G> stage 2" even for a stage-3 statement repair. Restored the required
"J3 stage 2" label. The existing interface repair is retained as a correctness
repair, with one remaining construction obligation and no claimed net proof
progress.

## Forced adaptations

### Sheaf.CategoryTheory.DerivedFunctorValueTriangle
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ekacgyy_/lean/Sheaf/CategoryTheory/DerivedFunctorValueTriangle.lean:103:8: error: Function expected at
  leftDerived_value_triangle_extension_compat F S hS T hT LX LY LZ hX hY hZ uX uY uZ huX huY huZ lf lg hf hg
but this term has type
  ∃ lh,
    Triangle.mk lf lg lh ∈ distinguishedTriangles ∧
      ∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁) (h' : s.left ⟶ (shiftFunctor C 1).obj s'.left),
        s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C 1).map s'.hom →
          uZ.app s ≫ F.map h' = lh ≫ (shiftFunctor D 1).map (uX.app s') ≫ (commShiftIso F 1).inv.app s'.left

Note: Expected a function because this term is being applied to the argument
  lh

(with the modules compiled into /tmp/forced-adaptation-ekacgyy_/.lbuild) [1.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
