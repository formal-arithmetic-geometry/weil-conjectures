## What changed

Reduced `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing`
to restriction of clopen subsets and the existing scheme/idempotent correspondence.
Injectivity follows by equality of loci; surjectivity lifts a clopen locus and realizes
it by an idempotent. Added proof-only imports of `HenselianClopenRestriction` and
`SchemeClopenIdempotent` and updated its DAG proof.

Reduced `AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`
to full faithfulness and the existing essential-surjectivity theorem. The latter uses
the chosen categorical pullback, so the proof transports each cover using `h.isoPullback`
and `pullback.map`. It proves the projection compatibility by cancellation of the fibre
isomorphism, then combines full, faithful, and essentially surjective instances.
Added proof-only imports of `FiniteEtaleRestrictionFullyFaithful` and
`FiniteEtaleLiftingEssentialSurjectivity` and updated its DAG proof.

The local-ring corollary now supplies the ideal with the named argument `I :=`:
new proof dependencies make that argument implicit in the pair theorem. No theorem
signature or definition was changed.

## Proved and sorry left

Proved from named intermediate statements (2 of the original 4 sorries):

- `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing`.
- `AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`.

The existing local-ring corollary also compiles. Original sorries left untouched:

- `AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`
  (lemma-weil-pbc-finite-locally-constant-etale-equivalence).
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing`
  (lemma-weil-pbc-h1-torsor-comparison).

New sorries, each a whole named public theorem in its own module:

- `AlgebraicGeometry.Scheme.henselian_clopen_restriction`
  (lem-weil-pbc-henselian-clopen-restriction), `HenselianClopenRestriction`.
- `AlgebraicGeometry.Scheme.fullyFaithful_pullback_finiteEtale_of_henselianRing`
  (lem-weil-pbc-finite-etale-restriction-fully-faithful),
  `FiniteEtaleRestrictionFullyFaithful`.

Existing imported sorries, unchanged:
`AlgebraicGeometry.scheme_clopen_idempotent`
(lem-weil-pbc-scheme-clopen-idempotent) and
`AlgebraicGeometry.Scheme.essSurj_pullback_finiteEtale_of_henselianRing`
(lem-weil-pbc-finite-etale-lifting-essential-surjectivity).

## No longer needed

No existing imports removed and no nodes globally pruned. The idempotent theorem
now directly imports only the clopen restriction and scheme/idempotent correspondence;
its closed-immersion and Zariski H0 route remains below the clopen node.

The finite étale equivalence now directly needs the full-faithfulness node and the
existing essential-surjectivity node. Its former setup, cartesian-square pasting,
finite-morphism permanence, sections-as-clopen-immersions, composition/cancellation,
closed-immersion finiteness, and finite-flat rank arguments remain below the new
full-faithfulness node. That node uses clopen restriction directly, so does not depend
on the idempotent theorem as an intermediate interface; the idempotent theorem remains
used elsewhere. No unit statement or realized unit step is bypassed.

For completeness, the old direct proof dependencies removed from the two rewritten
nodes are listed explicitly below. They are retained below the new split nodes, except
that the idempotent theorem is no longer an intermediate interface for full faithfulness;
none becomes globally unreachable through this delivery.

From `thm-weil-pbc-henselian-idempotent-lifting`:

- `def-weil-closed-immersion`.
- `lem-weil-pbc-closed-immersion-base-change`.
- `lem-weil-pbc-spec-quotient-closed-immersion`.
- `lem-weil-pbc-zariski-h0-proper-henselian-pair`.

From `thm-weil-pbc-finite-etale-lifting`:

- `def-weil-pbc-finite-etale-category`.
- `lem-weil-pbc-cartesian-square-pasting`.
- `lem-weil-pbc-closed-immersion-finite`.
- `lem-weil-pbc-etale-composition-cancellation`.
- `lem-weil-pbc-etale-section-clopen-immersion`.
- `lem-weil-pbc-finite-composition`.
- `lem-weil-pbc-finite-flat-rank-iso`.
- `lem-weil-pbc-finite-morphism-permanence`.
- `thm-weil-pbc-henselian-idempotent-lifting`.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left an anonymous `sorry` in the essential-surjectivity
transport and supplied no node for full faithfulness. Both are repaired: the transport
is now a complete Lean proof and full faithfulness is a separate part of the argument
with its own node and source. Removed an unnecessary `simpa` reported by the linter.

The existing `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`
cannot be imported here: it already reaches this module through `EtaleTorsorDescent`,
as confirmed by `tools/import_direction.py may`. Thus it is not a shorter route for
the remaining Yoneda theorem. No mathematical statement discrepancy found.
The earlier LeanSearch attempt returned Internal Server Error; LeanFinder, Loogle,
and source grep were available. The original attempted split into injectivity and
surjectivity of the same idempotent map was discarded as too close to a restatement.

## New nodes

`lem-weil-pbc-henselian-clopen-restriction`: the original idempotent proof's first
three steps: closed fibre as a closed subset, Tag 0A0B on locally constant two-valued
functions, and transport to clopens of the fibre. Its statement contains no global
sections or idempotents; the remaining idempotent argument is proved in Lean.
Empty schemes and empty/full clopens are included.

`lem-weil-pbc-finite-etale-restriction-fully-faithful`: finite étale lifting's first
six steps: morphisms as sections, sections as clopen rank-one pieces, clopen restriction,
and descent of the degree-one condition. It proves only full faithfulness, leaving
essential surjectivity to the existing theorem. Empty covers cause no exception.
Neither new node replaces a whole theorem under another name. No change records needed.

The source texts were checked directly at [Stacks 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
and [Stacks 0GS2](https://stacks.math.columbia.edu/tag/0GS2). The clopen argument uses
0A0B, while full faithfulness follows the corrected blueprint rank argument (the
Stacks proof of 0GS2 instead lifts graphs through essential surjectivity).

## Second reading by N1

1. Compared the complete existing module with the repository by `diff -u` and the
   declaration parser. Verdict: every existing declaration signature and definition is
   byte-for-byte unchanged. The only existing proof adaptation outside the two reductions
   supplies the ideal by name in the local-ring corollary. No change record is needed.
2. Compiled all three delivered modules in import order through `lcompile.py`: no errors
   or warnings. Compiled scratch copies with `#print axioms` for every declaration:
   only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` occur.
   The two original remaining sorries and two new whole-theorem sorries are all reported;
   there is no hollow definition or forbidden implementation mechanism. Verdict: pass
   as a reduction to named open statements, not as an axiom-free completed target.
3. Read both new signatures, full natural-language proofs and nodes. Checked empty
   schemes, empty/full clopens, identity fibre (`I = 0`), and empty source/target covers.
   The rank-one complement argument uses clopen injectivity, never surjectivity of the
   closed immersion. The stability parameter only provides the canonical pullback
   instance. Rechecked [Stacks 0A0B](https://stacks.math.columbia.edu/tag/0A0B) and
   [Stacks 0GS2](https://stacks.math.columbia.edu/tag/0GS2). New LeanFinder search used
   connected components/locally constant functions terminology; Loogle searched
   `"Henselian", "idempotent"`; source grep included Mathlib, upstream, and `lean/Sheaf`.
   No replacement was found. Existing HenselianConnectedness gives a still-open
   connectedness input, not either new statement. Verdict: both statements are true
   parts of the original argument and neither merely renames its entire conclusion.
4. Read both reductions from the top: clopen lifting plus the general locus
   correspondence proves idempotent bijectivity; full faithfulness plus existing
   essential surjectivity and pullback transport proves the equivalence. All four added
   imports are proof-only and used. Existing public imports supply the signatures and
   definitions. Compared old/new dependency lists and read `dag/units/sk-thm-p1.json`:
   no realized unit statement or step is bypassed or modified. Verdict: pass; the report
   now enumerates every removed old direct dependency, with none globally pruned.
5. Checked each new node's source, searches, Lean signature, creation record, chapter,
   unit, and blueprint ancestry. Existing nodes change only `proof`, `proof_deps`, and
   `proof_origin`. For all four nodes, `proof_deps` equals the union of step `uses`;
   the rewritten proofs describe the actual Lean reductions. Verdict: pass.

Changes by the second reader: expanded `## No longer needed` to list all removed
old direct dependency IDs, and added this independent review. No Lean or node changes
were necessary. Neither open split statement has a short existing formal proof that
can be completed in a few minutes without expanding the scope.
