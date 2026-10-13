## What changed

Proved `AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_single`
in `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsSingle`, with its statement and
visibility unchanged. Added only proved private helpers for localization/single
compatibility, composition, natural isomorphisms, arbitrary coefficient maps, and
naturality of an arbitrary section transformation. The public import is unchanged.
Updated the item's DAG proof and proof origin to describe the actual calculation.

The complex comparison identities are checked componentwise: degree zero is the
identity/natural-transformation calculation; every other target component is zero.
The derived identities follow from existing localization factorization lemmas. The
last step is naturality of `derivedSectionPullback`, specialized to the inverse-image
square. There are no new data constructions and no new statements with holes.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_single`
(node `lem-sbc-restricted-derived-sections-single`).

Proved 1 of 1 original sorries; added 0 holes; split off 0 statements. No `sorry`
remains in the delivered Lean file, including its private helpers. This is a proof,
not a decomposition. No theorem with an existing `sorry` is applied by this proof.

## No longer needed

Imports removed: none. Whole modules/nodes pruned: none. The four original DAG
interface dependencies remain necessary for the definitions in the statement.

`restrictedSectionPullback_zero` is not used. Its module must remain imported because
it defines `derivedSectionPullback` and `derivedRestrictionIso`. Expanding the derived
adjunction unit and Leray comparison, computing zeroth cohomology, injective-resolution
arguments, and shift/homology comparison lemmas are unnecessary for this identity.
The proof uses only naturality of the already constructed section transformation.

## Where the brief, the DAG or earlier work was wrong

The original proof plan unnecessarily proposed expanding the unit and Leray map.
Naturality proves the transport step for any transformation of the same type. The
statement, coefficient construction, and required unit route were correct and are
unchanged (`sk-lem-failure-field` has no realized statement/step nodes bypassed here).

The cited Stacks tags were read online: [07A6](https://stacks.math.columbia.edu/tag/07A6)
is derived adjunction, [0D6F](https://stacks.math.columbia.edu/tag/0D6F) is restriction of
cohomology to the localized site, and [03Q8](https://stacks.math.columbia.edu/tag/03Q8)
is the higher-direct-image presheaf presentation. They justify the constructions,
while the explicit identity here is a categorical calculation from their Lean
implementations. No source statement was changed.

Searches used the prescribed Lean Finder, Loogle and grep wrappers, plus repository
and Mathlib searches. The useful existing results were the single/localization
comparison and the composition/natural-isomorphism factorization lemmas. The online
Loogle index also returned newer composition-on-single lemmas absent from this pinned
Mathlib, so the needed compatibilities were proved privately from the pinned library.

The previous dry run conservatively classified section variables and scoped options
for private helpers as an interface change. The repaired file gives each helper
explicit category parameters and makes its elaboration options local to that
lemma. The interface comparison now reports no changes. The dry-run tool now
allows the missing second-reading section for a first worker; that section remains
reserved for the independent second reader.

All writes are in the item's sandbox. Compilation uses `lcompile.py`; delivery
validation uses only `deliver3.py --no-push`, with no push.

## Second reading by Q2

1. **Interface: PASS.** Compared the entire delivered module with the repository.
   The existing theorem signature is byte-for-byte identical, as is the sole public
   import. Only private proved helpers, declaration-local options, the theorem proof,
   and its proof documentation are added or changed. No definition or target changes.
2. **Proof: PASS.** Independently compiled a scratch copy with `lcompile.py` and
   `#print axioms` for `restrictedDerivedSections_single`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No delivered theorem or
   private helper contains `sorry`; there are no forbidden declarations or new data
   constructions. An initial compile timed out amid concurrent Lean processes; the
   independent scratch compilation subsequently passed in 58.8 seconds without warnings.
3. **Split statements: PASS (none).** No new public statements, nodes, or holes are
   split off. Read all eleven private helper proofs. Their degreewise calculations
   handle degree zero and every nonzero integer separately; arbitrary coefficient
   maps are handled by naturality without an invertibility assumption. Zero sheaves,
   zero coefficient maps, and empty schemes require no extra hypotheses.
4. **Route and pruning: PASS.** Read the definitions of `Evaluation.singleIso`,
   `derivedSectionPullback`, `derivedRestrictionIso`, and `rawAffineRestrictedCoefficient`.
   The last proof is their actual categorical compatibility, using naturality rather
   than a zeroth-cohomology theorem. Independently searched pinned Mathlib and both
   library roots for composition/natural-isomorphism comparisons on singles. Related
   generic helpers in `EtalePullbackSingleComp` and
   `ExtExactFunctorCompositionComparison` are private; their public theorems concern
   module sheaves or Ext, so neither supplies a shorter applicable route here. The
   one import supplies definitions in the public signature and remains public.
   No old proof dependency is removed; the unused `restrictedSectionPullback_zero`
   theorem is explicitly recorded above, and its module cannot be pruned. Read
   `dag/units/sk-lem-failure-field.json`: its realized statement and step lists are
   empty, and this node calculation changes no unit route.
5. **DAG: PASS.** Only `proof` and `proof_origin` differ from the repository node.
   The unchanged `proof_deps` equal the union of the updated proof steps' `uses`;
   these describe the definitions and inverse-image composition used by Lean.
   The Lean statement record is unchanged and matches the delivered declaration.

Second reading changed only the theorem's natural-language proof docstring to match
its actual naturality-based argument, and added this review record. The proof code
was retained. Holes closed: `restrictedDerivedSections_single` (1); holes added: none
(0); split off: none (0); pruned: none.
