## What changed

Proved `AlgebraicGeometry.exists_recordedPerfectHom_normalization` in
`Sheaf.AlgebraicGeometry.RecordedPerfectHomNormalization`, without changing its
signature, visibility, definitions used by its statement, or imports.

The private `oldAdditive`, `oldCounit`, and `oldUniversal` helpers project exactly
the witness already selected by `perfectHomComposition`. They do not select a new
counit. The private `normalization` is Mathlib's `Functor.leftDerivedUnique` between
the recorded and old universal counits; its factorization determines it uniquely.

The proof makes both numbered steps of the existing node into Lean. First,
`composition_change` proves the abstract component calculation, and
`normalization_composition` applies `Functor.leftDerived_ext` and both explicit
composition-lift factorization equations. Second, invert the composition equation,
transport the normalization through `baseChangeMap_fst` by equality induction,
and cancel the base-change automorphism by naturality in `conjugated_transport`.
All helpers are private and fully proved. No public interface or unit route changes.

Searches: Lean Finder for change of left-derived counits returned
`Functor.leftDerivedNatIso` and related derived adjunction primitives, without a
matching direct normalization theorem. Loogle for
`CategoryTheory.Functor.leftDerivedUnique`, the launcher grep search for
`leftDerivedUnique|leftDerived_ext`, and local library searches confirmed the
universal-property primitives and examples of their use. The source statements
were checked in Stacks Tags 06YJ and 0D5S.

Validation: the complete module compiled through `lcompile.py` in 26.1 seconds,
with no warnings or errors, before the final report and formatting cleanup.
The required delivery dry run performs the final compile and axiom probe.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_recordedPerfectHom_normalization`
(node `lem-pc-recorded-perfect-hom-normalization`).

There are no `sorry`s left in the item's module, and no new holes or split-off
modules. The proof uses the existing universal-counit and composition APIs;
this delivery does not assert that all their transitive dependencies are sorry-free.

## No longer needed

None. Both original public imports are needed by the unchanged statement and
its proof: `Sheaf.AlgebraicGeometry.RecordedPerfectHomTransport` and
`Sheaf.AlgebraicGeometry.PerfectHomTransport`. Their recorded and old composition
modules supply the two lift equations. All four original proof-dependency nodes
remain used. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface discrepancy was found. The proof follows the
existing node's two steps, so no DAG route update is needed. The local build cache
initially lacked the recently landed recorded-composition modules; they became
available during the work, and the complete proof then compiled against them.

## Second reading by K3

1. Interface: PASS. Read the full repository/sandbox diff. The existing theorem's
   docstring, signature (including universes and the shared instance family), and
   visibility are byte-identical; checked the docstring/signature equality with a
   script. Both public imports and the module header are unchanged. The only
   additions are private helpers and the replacement proof. No change record or
   adaptation is needed. The quantifiers still cover every scheme arrow, arbitrary
   derived objects P and Q, and every Hom a, without finiteness or perfectness.
2. Proof and data: PASS. Independently compiled the delivered file with lcompile.py
   (26.8 seconds, clean). A scratch copy printed axioms for all twelve declarations,
   including the private abbreviations/definition and the public theorem; every
   result is exactly propext, Classical.choice, Quot.sound, with no sorryAx.
   The file contains no sorry or prohibited declaration mechanism. oldAdditive and
   oldCounit project the identical nested witness used by perfectHomComposition;
   they do not choose a different counit. exists_derivedPullbackComposition is
   itself proved, and the axiom probes confirm its chosen data introduces no
   unproved existence. normalization is Mathlib's constructed leftDerivedUnique,
   uniquely characterized by normalization_fac, not an arbitrary existence witness.
3. Split statements: PASS (none). No new public statements, nodes, modules or holes.
   Read the private component lemmas: composition_change uses exactly the three
   factorization equations, the two lift equations and derived extensionality;
   conjugated_transport is naturality and inverse cancellation for arbitrary a.
   Identity arrows, identity morphisms, and zero derived objects require no extra
   hypothesis: the component equalities and cancellation remain valid in these
   cases. There is no assumption that a is invertible or that a counit is invertible.
4. Route and pruning: PASS. Read Mathlib LeftDerived.lean lines 73-137 and both old
   and recorded composition modules, as well as both Hom-transport definitions.
   The first lift equation comes from the old composition witness's hom equality;
   the second comes from the explicit recordedDerivedPullbackCompositionLift.
   Both use the same underived adjunction-conjugate comparison. Naturality at the
   old g-counit is the precise equality used by composition_change. Inverting that
   equation and equality induction at baseChangeMap_fst yields
   normalization_comparison; conjugated_transport cancels the base-change
   automorphism and leaves exactly the projection conjugations in the statement.
   Independent launcher grep search for leftDerivedNatTrans_comp|leftDerivedNatIso|
   counit_normalization found only the general Mathlib primitives; local searches
   of lean/ and the upstream source found no existing direct normalization theorem.
   The same-underived-functor composition lemma leftDerivedNatTrans_comp does not
   supply the two-arrow composition equation needed here. Both public imports
   provide names in the unchanged signature, so neither is a proof-only import.
   All four old proof-dependency nodes are used; No longer needed is complete.
   Read dag/units/sk-thm-picard-semicon.json: its realized statement and step lists
   are untouched, and this below-unit normalization follows its existing route.
5. DAG/source: PASS. Read lem-pc-recorded-perfect-hom-normalization.json and matched
   its two proof steps, four proof_deps and proof_origin to the above calculation.
   No DAG edit is necessary. The local cited cohomology.tex is absent, so read
   [Stacks Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ) and
   [Stacks Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S) online: they give
   the choice-independent derived pullback and its composition using K-flat
   representatives, without geometric finiteness assumptions. The normalization
   formula is the node's universal-property calculation for those presentations,
   not a claim that Stacks prints this particular counit formula. Also read the
   landed perfectDescentComparison-original-counit change record's account of
   this obligation; the delivery closes it without altering those definitions.

Second reading changed only this report, recording the independent checks and
axiom results. No Lean repair was needed. Holes closed: one, namely
AlgebraicGeometry.exists_recordedPerfectHom_normalization. Holes added: zero.
