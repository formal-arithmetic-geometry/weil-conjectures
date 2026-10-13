## What changed

Replaced the sole proof hole in `Sheaf.Paper.CartierEquality.cartier_equality`
(the declaration is global `cartier_equality`) by a compiling reduction. The proof
chooses and enumerates a finite transcendence basis and field-generating set, applies
`FieldTheory.exists_completeIntersection_fractionField_model`, identifies the two
cotangent modules with the kernel and cokernel of a finite linear map, and performs
rank-nullity and the finite-extension specialization in Lean.

Corrected the hypothesis `[Algebra.FiniteType k K]` to the explicit field-generation
hypothesis `(hfg : (⊤ : IntermediateField k K).FG)`. All conclusions are identical.
This recovers the source's full scope; the natural-language node already had this
scope. No target statement or definition changed. The current direct importer, `Sheaf.RingTheory.GeometricallyRegularH1Injective`,
contains no application of `cartier_equality`, so it requires no adaptation. The
first worker recorded two direct importers at its earlier repository snapshot. All 223
transitive importers and their claim snapshots are listed in
`coord/changes/cartier-equality-field-generation.md`.

Added `Sheaf.RingTheory.FractionFieldCompleteIntersectionCotangent`, with the
geometric comparison isolated as a named theorem, and updated the parent DAG proof,
proof dependencies, proof origin, and Lean signature record. Proof imports of
`Mathlib.FieldTheory.FinTrdeg`, `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`,
`Mathlib.LinearAlgebra.Dimension.Constructions`, and the new module supply the proof.
The field-generation definition is a public import because the signature uses it.

## Proved and sorry left

Closed: `cartier_equality` (node `lem-weil-pbc-cartier-equality`), 1 of 1 original
holes. Its proof has no `sorry`; it proves finiteness of both modules, the full
Cardinal-valued equality, and the finite-extension consequence from the named models.

Added and left: `Algebra.exists_fractionField_completeIntersection_cotangent_model`
(node `lem-weil-pbc-complete-intersection-fraction-field-cotangent-model`), exactly
one public theorem with proof `:= by sorry`. This is a decomposition, not a standalone
sorry-free proof of Cartier equality: one upper hole is replaced by one lower hole,
so the delivered closed-minus-added count is zero. The pre-existing model theorem
`FieldTheory.exists_completeIntersection_fractionField_model` is also still sorried
upstream; it is used unchanged and is not a new hole of this delivery.

The new theorem only identifies the cotangent objects for a specified polynomial
complete-intersection fraction-field model. It neither asserts their dimensions nor
mentions finite field generation, transcendence degree, or the Cartier conclusion.
The combining proof genuinely supplies these omitted parts. The module's one remaining
hole has its full source and natural-language proof in both docstring and DAG node.

Validation: the delivered pair compiles with `lcompile.py --all`, with no warnings
other than the permitted named theorem hole. Compiler-guided checks covered basis
reindexing, all finiteness instances, dependent lengths, Cardinal universe casts, and
the algebraic/finite-extension specialization. No definitions or arbitrary chosen
objects were added. The existential linear map is used only within a proposition proof.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.RegularSequenceConormal` from
`CartierEquality`. Its result remains needed in the proof plan of the new comparison
node; this is a transfer of the geometric subargument, not a claim that conormal theory
has been proved or discarded. The original geometric proof dependencies (presentation
functoriality, conormal freeness, polynomial differential bases, Jacobi–Zariski, and
localization) now belong to the new node rather than directly to the parent.

No complete mathematical subargument is pruned. No unit statement or realized unit
proof step is bypassed. No claim of global import-closure pruning is made.
The broad exploratory import `Mathlib.Tactic` was removed after compilation showed
that the existing imports already provide the arithmetic and cast tactics.


The complete list removed from the parent proof_deps (all retained in the new
comparison node) is:

- `def-weil-pbc-module-localization`
- `def-weil-pbc-mv-polynomial-ring`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-h1-cotangent-localization`
- `lem-weil-pbc-jacobi-zariski-differential-maps`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-nl-presentation-h1-functoriality`
- `lem-weil-pbc-polynomial-ring-kahler-basis`
- `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`
- `lem-weil-pbc-regular-sequence-conormal-free`

The new comparison module imports `Sheaf.RingTheory.RegularSequenceConormal`
as a proof dependency, preserving the available conormal result and its route.

## Where the brief, the DAG or earlier work was wrong

The original Lean signature equated finite algebra generation with finite field
generation. Zariski's lemma shows these differ: k(t)/k is field-finitely-generated
and has positive transcendence degree, but is not a finite-type k-algebra. The source
Tag 07E1 and the DAG state the field-generation hypothesis. The change record repairs
only this Lean mismatch; the node's mathematical statement stays unchanged.

The supplied model and conormal statements alone do not expose the needed localized
kernel/cokernel comparison. That gap is now a separate, strictly geometric theorem.
Mathlib searches found component results (`Generators.equivH1Cotangent`,
`LinearMap.tensorKerEquiv`, `tensorH1CotangentOfIsLocalization`), not the assembled
complete-intersection model. LeanSearch returned HTTP 500 and is recorded as
unavailable, not as evidence of no match. Loogle and grep succeeded. Searching all
blueprint records for “cotangent complex” returned no duplicate blueprint node.
The local source TeX was absent; the official Stacks Tag 07E1 page was read directly.

Edge cases checked mathematically for the new statement: for f empty the domain of
δ is zero, H₁ vanishes, and Ω is the free n-dimensional fraction-field module. At
n = 0 with an empty sequence the fraction field is k and both modules vanish. A
nonzero regular equation over an imperfect field can have zero Jacobian, giving
nonzero kernel and cokernel; no separability or injective-Jacobian assumption was
introduced. For example, the purely inseparable presentation T^p-a correctly permits
δ=0. The supplied fraction-field equivalence prevents a spurious mismatch of fields.

## New nodes

`lem-weil-pbc-complete-intersection-fraction-field-cotangent-model`, in
`Sheaf.RingTheory.FractionFieldCompleteIntersectionCotangent`, isolates steps 2–5
of the original node's proof. It computes the kernel and cokernel of one finite
linear map for a given regular-sequence quotient domain and its fraction field.
It preserves the source's geometric argument, has no dimension assertion, and leaves
rank-nullity and the transcendence-degree calculation to the completed parent proof.
Its four proof steps cite the existing geometric nodes; its three actual search kinds
are recorded, including the unavailable LeanSearch attempt.

Change record: `coord/changes/cartier-equality-field-generation.md`.

## Second reading by V3

1. Compared both delivered modules with the repository. The sole existing signature
   change is the declared field-generation correction in
   `cartier-equality-field-generation.md`; all conclusions are byte-for-byte unchanged.
   Tag 07E1 assumes finite field generation, so the correction restores its scope.
   No definitions or targets change. A fresh search of lean/ finds only the theorem's
   declaration and one direct importer, with no applications to adapt. Verdict: accepted.
2. Compiled both modules in import order through lcompile.py. Scratch-copy
   `#print axioms` checks for `cartier_equality` and
   `Algebra.exists_fractionField_completeIntersection_cotangent_model` return only
   propext, Classical.choice, Quot.sound and sorryAx. The latter is expected from the
   explicitly reported comparison hole and existing model hole. There is exactly one
   new sorry, in its named public theorem, and no new definitions or forbidden commands.
   Witnesses of the model and comparison existence assertions are eliminated only
   inside a proposition proof; no data definition selects an arbitrary witness.
   Verdict: valid conditional proof/decomposition, not a sorry-free Cartier theorem.
3. Read the new statement, its full proof docstring and node against Stacks 07E1 and
   00LN. Checked the empty sequence, zero variables, and inseparable T^p-a cases:
   the kernel may be nonzero, and no false separability assumption is present.
   Independent Lean Finder, Loogle and grep searches with presentation/Jacobian/kernel
   terminology found Generators.equivH1Cotangent and component comparison results,
   not this assembled theorem. Searched lean/ for existing comparisons. The lemma is
   strictly the geometric comparison part: it supplies neither the field model,
   transcendence-degree identity, rank-nullity calculation nor finite specialization.
   Closing this comparison requires substantial formalization, not a few-minute repair.
   Verdict: true, needed, strictly smaller, adequately documented.
4. Read the complete parent proof: finite field generators and transcendence basis,
   existing complete-intersection model, new comparison, finite submodule/quotient
   instances, two dimension identities, natural-number cancellation, Cardinal cast,
   and trdeg zero for a finite extension. No shorter assembled result was found.
   Public imports serve signatures; the other imports serve proofs. Inspected
   sk-thm-p1.realized: no unit statement or realized step is bypassed or modified.
   Enumerated all eleven old parent proof_deps removed; each is retained in the new
   comparison node. Restored its plain conormal-module import so the available proved
   dependency stays in the planned route. Verdict: accepted; no global pruning claimed.
5. Checked both nodes' statements, Lean signatures, proof steps, dependency unions,
   source, origin, chapter/unit and new-node creation/blueprint/search records.
   The parent record had accidentally included preceding comment text in lean.statement;
   replaced it with the exact declaration signature. The new node's statement and
   proof_deps agree with its geometric comparison. Verdict: accepted after metadata fix.

Second-reading changes: restored the new comparison module's proof import of
RegularSequenceConormal; listed every removed parent dependency explicitly; corrected
parent lean.statement and the Old/New signature blocks in the change record; clarified
that the current snapshot has one direct importer. No mathematical proof or statement
was changed by the second reader. Net hole change remains zero (one closed, one added).
