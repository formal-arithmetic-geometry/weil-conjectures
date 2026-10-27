## What changed

Replaced the proof hole of
`WeilConjectures.PurStrictScalar.reductionBalancing_existsUnique` by a complete
Lean proof from two separate universal-property statements. The ordinary balancing
isomorphism is applied degreewise and localized. Mathlib's
`Functor.rightKanExtensionUniqueOfIso` then constructs the derived isomorphism;
`liftOfIsRightKanExtension_fac_app` proves its exact whole-cochain counit equation,
and `hom_ext_of_isRightKanExtension` proves uniqueness.

Added proof-only imports of `Sheaf.Paper.ScalarSourceCounitUniversal` and
`Sheaf.Paper.ScalarTargetCounitUniversal`. Each new module has one named public
proof hole, with an explicit component formula, source, proof in words and node.
The formulas are written using theorem-local lets, so no existing construction
is moved, redefined or given a different public signature. The local existential
counits are used only inside a theorem proof, never to define arbitrary data.

The source lemma concerns only E reduction followed by finite free tensor and
has no ramification condition. The target lemma concerns only completed
extension followed by F reduction and arithmetic restriction, for arbitrary e.
Neither asserts a comparison between those two composites. Their assembly is the
proved mathematical step. Existing theorem signatures, definitions and public
imports remain unchanged. No downstream Lean adaptation is needed. The metadata
attachment partition is documented in
`coord/changes/C3-scalar-balancing-coefficient-data-attachments.md`.

## Proved and sorry left

Decomposition, not a net proof gain: closed 1 original hole, added 2 holes.

Closed:
- `WeilConjectures.PurStrictScalar.reductionBalancing_existsUnique`
  (`def-pur-strict-scalar-reduction-balancing`), by the compiled Kan uniqueness
  argument from the new one-sided universal properties.

Remaining original hole:
- `WeilConjectures.PurStrictScalar.ordinaryBalancing_existsUnique`
  (`def-pur-strict-scalar-reduction-balancing`), unchanged.

Added holes:
- `WeilConjectures.PurStrictScalar.scalarSourceCounit_universal`
  (`lem-pur-scalar-source-counit-universal`), in
  `Sheaf.Paper.ScalarSourceCounitUniversal`.
- `WeilConjectures.PurStrictScalar.scalarTargetCounit_universal`
  (`lem-pur-scalar-target-counit-universal`), in
  `Sheaf.Paper.ScalarTargetCounitUniversal`.

There are 3 actual holes in the delivered modules, compared with 2 in the original
item. No proof hole is introduced inside a definition. All new remaining proofs
are exactly `:= by sorry`.

Server validation: both new statements and the complete assembly have compiled
through lcompile.py. The final packet is checked again by deliver3.py, including
the declaration/axiom probe. The original compilation exposed missing explicit
local additive/exact instances; those are supplied in the new theorem types.
Edge checks of the new statements include zero complexes, the empty site object,
the identity arithmetic index, and e=0 (restriction to level zero); none requires
ramification or conservative finite evaluation. The two one-sided Kan properties
are justified by the whole ringed-sequence derived calculation, not by equality
of separate derived evaluations.

## No longer needed

None. No original import, declaration, node or module was pruned. The native
support data and the stated ordinary balancing remain necessary. Both new proof
imports are used. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item's DAG node has an empty proof and empty proof_deps, rather than the
numbered plan described in the generic brief. Its two theorem docstrings do
contain the intended argument. The updated node records the actual partial
reduction and preserves its statement and attachment.

No existing declaration in Mathlib, WeilConjectures or Sheaf supplies the two
concrete composite counit properties. Searches located Mathlib's general Kan
uniqueness API and the existing DAG leaf
`lem-sfb-right-kan-extension-unique-iso`; these are reused rather than restated.
The blueprint unit has no realized node attached to this item, and its scalar
compatibility route is retained.

## New nodes

`lem-pur-scalar-source-counit-universal`: the explicit source composite has its
right Kan universal counit. This is one side of the original docstring's
left-derived uniqueness argument; it asserts no balancing isomorphism.

`lem-pur-scalar-target-counit-universal`: the completed-extension/F-reduction/
arithmetic-restriction composite has its explicit universal counit. It is
independent of E reduction and of the ordinary ramification comparison.

Both theorem nodes inherit the original chapter and unit, cite the original
blueprint ancestor, include three kinds of search and a self-contained proof
in words, and attach exactly one new theorem in one new module.

`def-pur-constant-scalar-tensor-data`: reattaches the existing constantMap,
tensor, tensor_exact, T and constants declarations from the larger scalar
adjunction node. No Lean declaration is added or changed.

`def-pur-whole-cochain-derived-unit`: reattaches existing derivedUnit from
the larger geometric mates node. It is the generic right-derived cochain
unit formula and has no geometric scalar-comparison dependency.

`def-pur-native-reduction-counit-data`: reattaches the existing coefficient
restriction, native reduction, ordinary limit/reduction adjunction and
normalized reduction counit declarations from the larger support-model
node. Proper/open/support declarations stay on the original node.

The existing three nodes retain their main declaration and all their text;
their lean.declarations lists lose precisely the declarations now owned by
the new data nodes, and their stmt_deps gain the respective new node. There
are no new Lean modules for these already existing definitions. Every moved
attachment still points to its original module. This is a dependency-precision
repair of the actual preflight rejection, not a removal of dependencies.
Change record: `coord/changes/C3-scalar-balancing-coefficient-data-attachments.md`.

Dependency audit: the first preflight rejected both auxiliary edges because the
coarse native-support node already reaches the item through its geometric
compact-support route. The coefficient-only prerequisites have now been factored
into the three data nodes above; their old attachments are removed from the
coarse nodes and their original declarations are preserved verbatim. The new
auxiliary dependency paths therefore contain no balancing theorem. Existing
unrelated base cycles are not changed. The Lean import graph is acyclic.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
