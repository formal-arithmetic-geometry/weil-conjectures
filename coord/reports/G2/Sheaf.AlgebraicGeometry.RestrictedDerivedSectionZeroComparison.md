## What changed

Reduced `AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedSectionPullback_zero`
to two independent comparisons, in new modules `DerivedSectionPullbackZero` and
`DerivedRestrictionZeroTransport`. The original definitions and theorem signature are unchanged.
The two new imports in the original module are proof-only imports. The combining proof
postcomposes with the target zero comparison, cancels its inverse, expands the natural
transformation, rewrites the restriction tail, and then rewrites the pullback prefix.
All three modules compile locally with no warnings.

The first helper is the derived adjunction/Leray calculation on degree-zero objects,
for an arbitrary morphism into an etale restriction, without a restriction triangle or
coefficient morphism. The second helper is only exact-functor restriction coherence and
coefficient naturality, without the derived adjunction unit or section pullback. These
are separate proper parts of the original argument, rather than a renaming of its conclusion.
The original DAG node now records this reduction. The blueprint unit route is unchanged.

## Proved and sorry left

Decomposition: closed the one original hole in
`AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedSectionPullback_zero`.
The original module now has no sorry. Two holes added, both named public theorems:

- `AlgebraicGeometry.Etale.RawRestrictedComparison.derivedSectionPullback_zero`,
  node `lem-sbc-derived-section-pullback-zero`.
- `AlgebraicGeometry.Etale.RawRestrictedComparison.derivedRestriction_zero_transport`,
  node `lem-sbc-derived-restriction-zero-transport`.

Each has an exact Lean statement, a complete proof in words, and its own module and node.
This is a decomposition of one hole into two, not an independent proof free of sorry.
No definition contains sorry; no arbitrary data is chosen from an unproved existence theorem.
Empty schemes, zero sheaves and zero/noninvertible coefficient morphisms require no extra
hypotheses: all equalities concern functorial comparisons and never invert a section or
coefficient map. Identity triangles specialize to the corresponding single comparisons.

## No longer needed

None. No existing import, node or module is pruned. The original public import is retained.
The original construction dependencies are still used by the unchanged definitions;
the degree-zero comparison dependencies now belong to the two helper nodes.

## Where the brief, the DAG or earlier work was wrong

The original proof step 2 combined the nontrivial derived adjunction/Leray degree-zero
calculation with exact inverse-image composition coherence and coefficient naturality.
Its cited declarations supply constructions, but not that combined comparison identity.
The delivery makes the two missing calculations separate, explicit Lean statements.
The existing `RestrictedDerivedSectionsSingle` lemma cannot be imported here: it depends
on the original module and would introduce an import cycle.

Read the Stacks Project pages for Tags 07A6 (derived adjunction) and 0D6F
(restricted cohomology), and the local derived-adjunction, Leray, single-comparison
and right-derived-zero implementations. The cited tags supply the constructions;
the detailed compatibility arguments in the helper docstrings expand the parent's plan.
LeanSearch was unavailable (Internal Server Error); leanfinder, loogle and grep ran.
No exact existing lemma for either composite identity was found.

## New nodes

`lem-sbc-derived-section-pullback-zero`: the prefix of the original calculation,
using the derived adjunction unit and Leray, ending at ordinary section pullback.
Module `Sheaf.AlgebraicGeometry.DerivedSectionPullbackZero`.

`lem-sbc-derived-restriction-zero-transport`: the tail of the calculation,
using exact inverse-image composition and coefficient naturality, ending at the
underived coefficient section map. Module
`Sheaf.AlgebraicGeometry.DerivedRestrictionZeroTransport`.

No statement, definition, visibility or public import was changed; no change record is needed.

## Second reading by G2

1. Interface preservation: compared the original module against the repository with
   `diff -u`. The only changes are the two plain proof imports and the proof body of
   `restrictedSectionPullback_zero`. All existing signatures, definitions, visibility,
   docstrings and public imports are byte-for-byte unchanged. No forced adaptation or
   change record is needed. Verdict: pass.
2. Proof and trust: compiled all three modules in import order through `lcompile.py`,
   cleanly (13.3 s, 15.7 s and 39.0 s). The main theorem is a genuine cancellation and
   reassociation proof applying both helper identities. The only direct sorries are
   the two named public helper theorems reported above; their entire proofs are
   `by sorry`. No forbidden declaration or hollow definition was introduced.
   The scratch-copy axiom probe covers all three existing definitions, the main
   theorem and both helpers: the definitions use only propext, Classical.choice and
   Quot.sound; the three theorems additionally use sorryAx, as expected from the two
   open helpers. Delivery preflight repeats the full declaration probe.
   Verdict: pass as a decomposition, not a sorry-free proof of the mathematical result.
3. Split statements: read both Lean statements and nodes against Stacks Tags 07A6
   (lemma-adjoint) and 0D6F (lemma-unbounded-cohomology-of-open), and the actual
   zeroIso, inverse-image, derived-unit and Leray constructions. The first helper
   contains only the adjunction/Leray prefix, for any f into an etale restriction;
   it has no coefficient or restriction triangle. The second contains only the
   restriction/coefficient tail and has no derived unit or section pullback. Their
   combination is strictly more than either alone. Empty source or restriction gives
   zero section groups; zero G gives the unique map from zero; psi = 0 makes both
   coefficient tails zero by additivity; identity maps reduce to canonical single
   comparisons. No coefficient or section morphism is inverted. The resolution
   argument cancels augmentations in the derived category, where they are invertible,
   not arbitrary maps of sections. Both are true with exactly the stated hypotheses.
   Their docstrings give the resolution/unit and localization/naturality arguments.
   Repeated searches with different words using leanfinder, loogle and grep, and rg
   over the library, found no usable theorem stating either whole identity. Loogle
   reports newer Mathlib composition-on-single lemmas absent from the pinned local
   Mathlib. Existing local single-square calculations in
   RestrictedDerivedSectionsSingle are private and downstream, so importing that
   module creates a cycle. Neither remaining hole has a short direct closure using
   currently accessible declarations. Verdict: pass.
4. Route and pruning: inspected sk-lem-failure-field.json, including realized
   (statement = [], steps = [[]]), and the parent blueprint chain. The delivery only
   decomposes a lower node's calculation and changes no unit statement or step. Both
   new imports are needed by the proof. Each helper's sole public import provides
   types and constructions occurring in its statement. Every old proof dependency
   remains used in the unchanged explicit constructions; No longer needed is
   complete with none pruned. Verdict: pass.
5. DAG agreement: checked the main reduction against the two rewrites in Lean,
   all three proof_deps against the union of their steps' uses, and every dependency
   against its node's Lean record. The two new nodes have matching source, chapter,
   unit, creation, blueprint, search and Lean records. The parent's unchanged
   statement still matches its declaration. Verdict: pass.

Second-reading changes: corrected the two new file headers from group G3 to G2;
replaced their flattened node lean.statement strings with the verbatim multiline
Lean signatures. Added this independent review. No proof, definition, theorem
statement or import was changed in the second reading. The delivery closes one
upper hole and adds two lower holes, so its raw hole net is -1; it is explicitly
reported as a decomposition.
