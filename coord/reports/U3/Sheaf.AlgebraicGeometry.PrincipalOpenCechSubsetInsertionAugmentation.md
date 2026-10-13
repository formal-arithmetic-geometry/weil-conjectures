## What changed

Proved `AlgebraicGeometry.principalSubsetInsertion_augmentation` from a single new
singleton-component comparison, with its existing signature and visibility unchanged.
Added the proof-only import
`Sheaf.AlgebraicGeometry.PrincipalOpenCechSingletonAugmentationComponent`.
The proved private helper `sum_singleton_subsets` evaluates the finite sum at each
one-tuple, identifies its unique singleton subset, and eliminates every other term.
The main proof evaluates the sum of morphisms, discards the zero coordinates, applies
the singleton comparison termwise, moves the common additive inclusion through the sum,
and cancels the extension component isomorphism. Updated the parent node to this route.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.principalSubsetInsertion_augmentation`
(node `lem-sc-principal-open-cech-subset-insertion-augmentation`).
Added one hole: `AlgebraicGeometry.principalSubsetInsertOne_singleton_augmentation`
(node `lem-sc-principal-open-cech-singleton-augmentation-component`), in its own module.
There are no holes left in the item's module or its private summation helper.
This is a decomposition: one upper hole closed and one strictly smaller singleton
comparison left, so the net hole count is zero. The combination proof is complete.
No definitions or existing statements changed. No data was chosen from an unproved theorem.

## No longer needed

None. The original insertion import remains necessary. The proof uses the original
explicit insertion, section transport and alternating-total construction; no original
DAG dependency or module is bypassed. No extra imports are retained for searches.

## Where the brief, the DAG or earlier work was wrong

The parent DAG's one step combines the singleton geometric transport with the finite
summation and total-inclusion cancellation. The latter parts are now proved in Lean;
the former is isolated with the exact explicit transport statement and a complete
natural-language proof. This is below the unit level and keeps the original route.
`dag/units/sk-thm-picard-duality.json` has empty realized entries, and no unit statement
or step is bypassed.

The installed shared build initially lacked `PrincipalOpenCechSubsetInsertion.olean`.
An unchanged sandbox source copy was compiled through lcompile.py to populate the local
overlay, then removed from the delivery sources. No dependency was edited.
The LeanSearch service returned Internal Server Error; LeanFinder, Loogle and source
searches were performed. No exact singleton comparison was found.
The blueprint ancestor tool reports None for this parent, which was already created
below another generated node. The new node therefore records the explicit parent and
its exact singleton-comparison clause, following the existing generated-node convention.

## New nodes

`lem-sc-principal-open-cech-singleton-augmentation-component` states only the image of
one singleton restriction under `principalSubsetInsertOne`. It does not assert the
sum or the augmentation equality. Its source is the parent's singleton verification,
Stacks Tags 08C1/08C0 and 01FM, and Mathlib restriction-equivalence naturality.
The node introduces all data and has a complete proof in words; the Lean statement
uses only explicit definitions. The edge cases checked are the zero section, a zero
coefficient module, arbitrary coefficient degrees, a singleton cover and vanishing
principal opens. For r=0 there is no nonempty singleton S, so this lemma is vacuous;
the main proved sum handles the empty cover without a nonempty-cover hypothesis.
No change records are needed.

## Second reading by U3

1. **Unchanged interface — pass.** Read the full diff against the repository.
   The existing `principalSubsetInsertion_augmentation` signature is byte-for-byte
   identical, including its hypotheses, conclusion and visibility. Its docstring
   and all existing definitions are unchanged. The only additions to that module
   are a private proved summation helper, a proof-only import, a scoped heartbeat
   option and the proof. No change record or forced adaptation is necessary.
2. **Proof and trust — pass.** Compiled both delivered modules with `lcompile.py
   --all`: no errors or warnings. Source scan finds exactly the reported named
   singleton theorem's `:= by sorry`, no forbidden declarations or options, and
   no definition containing a hole. Read the sum evaluation, zero terms, singleton
   substitution, additivity and extension-isomorphism cancellation line by line.
   Scratch-copy `#print axioms` checks cover the private helper and both public
   theorems; the public reduction depends on the reported singleton hole.
3. **Split statement — pass.** Unfolded the source insertion, both explicit section
   transports and `alternatingCechZero`. For a singleton, the subset and tuple
   opens coincide, the coefficient degree is n, and the total summand is (0,n).
   The inverse `overFunctorEquiv` component is a morphism of sheaves of modules,
   so its naturality in the open, together with `restrictAppIso_inv_map`, gives
   exactly the claimed restriction comparison. The scalar-identity comparison
   acts identically on underlying groups. These observations verify the docstring
   argument without a nonempty-open or distinct-open hypothesis. Checked r=0
   (no singleton or tuple), r=1, repeated opens, an empty principal open, zero
   sections/modules and arbitrary integer n. The new node's Lean signature is
   verbatim and its source/proof/dependency/search/creation fields are present.
   This compares one summand only: the finite reconstruction and cancellation
   remain proved in the parent, so it is a genuine decomposition, not a restatement.
   Independent LeanFinder search for open-restriction evaluation, Loogle search
   for `AlgebraicGeometry.Scheme.Modules.restrictAppIso_inv_map`, and grep for
   both directions of restriction comparison found the expected general tools,
   not an existing singleton insertion theorem. Also read the existing
   `principalOpenCech_singleton_augmentation_exists`: it constructs a different
   coordinate augmentation and does not prove this explicit insertion comparison.
   The remaining dependent transport calculation is not a short direct application.
4. **Route and pruning — pass.** The coordinatewise summation proof is elementary
   and handles the empty cover. The original public import supplies the signature;
   the sole new import is used only in the proof and is correctly plain `import`.
   All original proof dependencies remain used through the explicit constructions.
   There are no unused delivered imports, bypassed original dependencies or modules
   to prune. Read `dag/units/sk-thm-picard-duality.json`; its realized entries are
   empty and the delivery preserves the existing below-unit augmentation route.
5. **DAG agreement — pass.** Compared the parent JSON structurally: only `proof`,
   `proof_deps` and `proof_origin` changed. Both nodes' dependency lists equal the
   unions of their proof-step uses. The parent describes the Lean finite sum and
   cancellation; the child describes precisely the remaining singleton naturality.
   The reported holes closed/added are accurate: one closed, one added, net zero.

Second reading changed only this report by adding the independent review and
verification evidence. No Lean or DAG repair was needed.

Axiom results: `sum_singleton_subsets` uses exactly `propext`, `Classical.choice`
and `Quot.sound`; `principalSubsetInsertion_augmentation` and
`principalSubsetInsertOne_singleton_augmentation` use those three plus `sorryAx`.
No other axiom occurs.
