## What changed

Replaced the single hole in `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData`
with a complete Lean assembly. The derived object is the actual
`schemeDerivedDirectImage` of the tensor-pulled module in degree zero, and the map is
`canonicalSingleDirectImageMap`; neither is chosen from an existence theorem.
A proved private helper establishes relative flatness from finite local freeness
using projective affine sections and transitivity of module flatness. The existing
perfect direct-image/base-change theorem supplies perfection and invertibility of
the characterised derived comparison. The canonical H0 unit theorem proves H0(a)
invertible by cancellation. The assembly transports negative vanishing from the
nonnegative right-derived image and transports ordinary rank witnesses through the
constructed e1. `Iso.comp_inv_eq` supplies precisely the required canonical-map equality.

Added two smaller modules for the ordinary rank dictionary and tensor-form mate
transport. Updated the original node's proof route and added their nodes. Every
existing signature and public import is preserved. No other existing module is adapted.
The blueprint unit `sk-prop-av-cube` has empty realized lists; its cube-theorem route
is unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.picardRankMatch_derived_truncation_data`
(node `lem-sc-picard-rank-match-derived-truncation-data`), 1 of 1 original holes.
The main module has no remaining sorry. This is a decomposition, not a claim that
the complete target import closure is sorry-free.

Added holes:

- `AlgebraicGeometry.Scheme.picardRankMatch_ordinary_ranks`
  (`lem-sc-picard-rank-match-ordinary-ranks`): ordinary finite local freeness and
  uniform ordinary ranks under further base change, with no derived data or maps.
- `AlgebraicGeometry.Scheme.Modules.tensorDegreeZeroMateSquare`
  (`lem-sc-picard-tensor-degree-zero-mate-square`): a general canonical tensor mate
  square, with no properness, relative-flatness, perfectness, rank matching, or
  base-change invertibility assertion.

The two statements are independent pieces of the argument, rather than renamed
copies of the original existential derived-truncation theorem. One upper hole was
closed and two lower holes added, so the delivery's nominal hole net is -1.

The resumed worker reread the three modules, the original rank predicate, the
perfect direct-image interface, and the canonical H0 definitions. All three sandbox
modules compile again (4.4 s, 3.7 s, and 22.0 s), with unchanged existing signatures.
The ordinary-rank docstring now explicitly says that all fixed-rank conditions are
vacuous on an empty test scheme, rather than suggesting only rank zero is possible.

## No longer needed

None of the original imports can be removed: they are public statement dependencies.
The second reader removed the unused proof import
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`; the affine projectivity
argument uses `Modules.LocallyFreeAffine` directly.
No module or node is claimed pruned from the target closure. The original direct
proof-dependency list is replaced by the actual route. The general flat-complex pullback node
`lem-pc-flat-complex-derived-pullback` is not a direct proof dependency of this
assembly: the remaining tensor comparison uses the smaller
`lem-pc-flat-module-canonical-derived-pullback`. Tensor adjunction and composition
remain needed for finite local freeness and the ordinary rank dictionary.
`CanonicalDegreeZeroMateSquare` remains imported for its canonical H0 definition,
although its abstract mate theorem is not used by the revised comparison plan.
These are route changes, not claims of global pruning.

For completeness, the old direct proof dependencies absent from the new direct
list are `lem-pc-flat-complex-derived-pullback`,
`def-sc-picard-universal-rank-match`,
`lem-weil-pbc-module-base-change-map-open-restriction`, and
`lem-pc-module-pullback-identity-composition`. The first is replaced by the smaller
flat-module comparison in the new mate lemma's plan. The rank predicate and
ordinary-map module remain statement dependencies; identity/composition remains
in the ordinary-rank lemma's plan. Thus none of these nodes is claimed globally
unneeded, and no module is claimed pruned from the target import closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric plan is sound, but its listed declarations do not directly give
the universal fixed ordinary rank assertion for the iterated fibre product.
The rank-matching predicate only gives local tests with potentially differing ranks;
nonempty-fibre rank comparison and the empty-fibre locus must be accounted for.
The canonical degree-zero mate square is stated for abstract `Modules.pullback`,
whereas this item's beta uses the specified `Modules.tensorPullback` adjunction.
The existing tensor-form `derivedBaseChange_unit_compatibility` provides a direct
route: specialize to a single complex, use the termwise exchange identity and
derived-unit naturality, then pass through H0. The remaining comparison lemma
records this route instead of substituting arbitrary pullback isomorphisms.
A scratch attempt checked the single-complex exchange and derived-unit square,
but the final H0 normalization did not compile within the single-file limit.
The delivered comparison is one named whole theorem with its complete proof in
words; it contains no partial proof or anonymous hole.

Checked the new statements on empty source/base/test schemes, zero modules and
rank zero. Empty fibres require choosing rank zero for direct images; local ranks
of E on an empty inverse image alone are vacuous. The generic comparison cancels
only the flat single-source comparison; it assumes neither phi nor beta invertible.
It requires no higher-cohomology vanishing. The standard nonnegative right-derived
image theorem applies to all modules, so the assembly's negative-vanishing argument
uses no extra geometric hypothesis.

LeanFinder, Loogle, and pinned-source searches found the single-homology dictionary,
the canonical direct-image H0 unit, and abstract mate compatibility, not the entire
statement. LeanSearch returned HTTP 500 and is recorded as unavailable. Blueprint
searches for rank/direct image, universal/rank, degree/mate and tensor/mate found no
equivalent blueprint statement. The ancestor helper cannot traverse the original
node's module-valued `created.item`; the new records retain its explicit established
ancestor `thm-sc-theorem-of-cube` and extend its existing via chain.

## New nodes

`lem-sc-picard-rank-match-ordinary-ranks` states the ordinary geometric part of steps
1--2, in `PicardRankMatchOrdinaryRanks`. Its proof describes identity tests, the
clopen empty-fibre split, invariant-basis comparison after residue-field extension,
and locality with pullback associativity. It asserts no derived comparison.

`lem-sc-picard-tensor-degree-zero-mate-square` states the tensor-normalized part of
steps 3--4, in `Picard.TensorDegreeZeroMateSquare`. Its proof constructs the
characterised derived module comparison using the pinned counit, specializes
`derivedBaseChange_unit_compatibility` to a single complex and transports its
identity through the canonical direct-image H0 unit.
The original main theorem supplies its invertibility by the existing perfect
base-change theorem, then performs the H0 composition and cancellation itself.
No change record is required: no existing statement, definition or visible import changes.


## Second reading by B3

1. Compared the complete main-module diff against the repository version. The
   existing theorem signature and docstring are byte-for-byte unchanged. The
   only changes are its proof, one proved private flatness helper, scoped
   elaboration options, and plain proof imports. The new modules add statements
   without modifying any existing definition or public interface. Verdict: pass;
   no change record is needed.
2. Compiled all three modules through lcompile.py in import order, and compiled
   a scratch copy with explicit #print axioms for all three public theorems.
   Each reports only propext, Classical.choice, Quot.sound and sorryAx. There are
   exactly two named public sorry theorems, both listed above; no forbidden
   declaration or hollow definition. K is the actual derived direct image and a
   its canonical unit. The adjunction choice in the proof is used only to obtain
   the unique comparison with the existing pullback, not an arbitrary object.
   Verdict: pass as a decomposition, not a sorry-free proof of the import closure.
3. Read both new statements and their full docstring arguments. For ordinary
   ranks, proper flat finite presentation gives a clopen empty-fibre locus;
   nonempty fibres stay nonempty under residue-field extension and allow rank
   comparison. On the empty-fibre locus use rank zero, and on an empty test
   scheme every rank assertion is vacuous. For the mate statement, finite local
   freeness of M makes its single-source comparison invertible; no flatness of
   G and no invertibility of beta or phi is asserted. Its equation follows from
   the tensor derived-unit compatibility and natural H0 unit. Zero modules and
   identity base changes cause no exception. Repeated LeanFinder, Loogle and
   pinned-source grep searches with different terms; inspected the existing
   stalk-finrank equality and abstract canonical degree-zero mate square.
   These provide ingredients, not either complete new statement. Neither new
   statement is a renamed target: one has no derived data, the other has no
   geometric/rank/perfectness assertions. Neither hole had a few-minute closure.
   Verdict: true, necessary, strictly smaller pieces.
4. Read from the constructed K and a downward, including the affine flatness
   helper, perfect direct-image/base-change interface, canonical H0 unit and
   homology transport. No shorter complete route was found. Removed the unused
   plain FiniteDescent import and recompiled successfully. All original imports
   are statement dependencies. Completed the accounting for every removed old
   direct proof dependency above. The sk-prop-av-cube unit's realized fields are
   empty, and its stated cube-theorem route is untouched. Verdict: pass.
5. Compared node statement records against the Lean signatures, checked the
   main node changes are only proof/proof_deps/proof_origin, and checked the two
   new nodes' source, natural-language proof, searches, creation, ancestry and
   Lean records. Their dependency unions agree with their plans; the main
   record follows the assembly actually written, including canonical H0
   definitions from CanonicalDegreeZeroMateSquare. Verdict: pass.

Second-reading changes: removed the unused FiniteDescent proof import, completed
old-dependency accounting in this report, recorded additional independent
searches in the new nodes, and added this review. No statement or definition
changed. Sources checked: https://stacks.math.columbia.edu/tag/0BDP,
https://stacks.math.columbia.edu/tag/08HY, and
https://stacks.math.columbia.edu/tag/06YJ.
