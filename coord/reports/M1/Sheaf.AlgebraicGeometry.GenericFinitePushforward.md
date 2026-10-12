## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.GenericFinitePushforward`,
`AlgebraicGeometry.Scheme.exists_dense_open_lisse_finite_directImage`, by a complete Lean
proof from two new intermediate theorems and the existing
`AlgebraicGeometry.Scheme.pullback_finite_locally_constant` theorem.
The declaration's signature and all its public imports are unchanged.

The two new modules are `Sheaf.AlgebraicGeometry.GenericFiniteSourceLisse` and
`Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation`. Their statements isolate different
parts of the original blueprint proof. The first provides lissity of the **source** on the
inverse image of a dense base open and has no direct-image conclusion. The second provides a
dense open depending **only on the finite map**, on every smaller open of which direct image
preserves lissity of the source restriction; it assumes no constructibility of the sheaf.
Neither is the original constructible-direct-image theorem under another name.

The Lean proof obtains the two dense opens independently and takes their intersection.
`Dense.inter_of_isOpen_left` proves that intersection dense. The source inverse images have
an inclusion, expressed as `Z.homOfLE hWU`. The existing pullback theorem carries lissity to
this smaller source open; rewriting with `Scheme.homOfLE_ι` identifies the composite with
its canonical inclusion. The second helper then applies on precisely that intersection.
The item's copied DAG node records these steps and the three declarations actually used.

Read the original blueprint file
`sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-finite-pushforward-generic-constructible.md`,
including its finite-algebra calculation and final paragraph, from the project's literature
copy. A read-only copy is in the sandbox scratchpad. Both intermediate theorems have that
source, complete natural-language proofs, public theorem declarations with exactly
`:= by sorry`, matching nodes, and explicit blueprint ancestry. The unit record
`sk-prop-sf-cbc` has no realized steps requiring another route; the reduction keeps the
original source-lissity and algebra-splitting route.

Local compilation of all three modules in import order succeeds without errors or warnings.
The new-node dependency closure, overlaid on the repository's DAG, has no cycles or missing
pointers. The import of `PullbackFiniteLocallyConstant` is permitted by `import_direction.py`.
The delivery-tool dry run printed OK: local and server compilation and preflight pass,
except for the second reading reserved for the next worker. Nothing was pushed.

## Proved and sorry left

Proved from named intermediate declarations:
`AlgebraicGeometry.Scheme.exists_dense_open_lisse_finite_directImage`
(node `lem-weil-pbc-finite-pushforward-generic-constructible`). There is no `sorry` in the
item's module. This is a reduction, not a claim that its entire dependency closure is
axiom-free.

Two new named sorries remain in the delivery:

- `AlgebraicGeometry.Scheme.exists_dense_open_lisse_finite_source`, in
  `Sheaf.AlgebraicGeometry.GenericFiniteSourceLisse`, node
  `lem-weil-pbc-finite-source-generic-lisse`.
- `AlgebraicGeometry.Scheme.exists_dense_open_finite_lisse_preservation`, in
  `Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation`, node
  `lem-weil-pbc-finite-map-generic-lisse-preservation`.

The existing imported `AlgebraicGeometry.Scheme.pullback_finite_locally_constant`
(node `lem-weil-pbc-pullback-finite-locally-constant`) is still sorry in the repository;
it is used as the stage-3 brief intends and is not changed by this delivery.
No new definitions or axioms were introduced.

## No longer needed

Removed these proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting`
- `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `WeilConjectures.SixFunctors.Finite.BaseChange`

They are no longer direct dependencies of the combining Lean proof. They remain needed
in the planned proofs of the two new nodes: the strata and reduction argument under the
source node, and algebra splitting, universal-homeomorphism invariance, and finite exchange
under the preservation node. Their old DAG nodes are therefore **not globally pruned**.
The finite-integrality and finite-components nodes likewise remain needed below the source
node. No original node or module is asserted to be unnecessary to the mathematical route.

## Where the brief, the DAG or earlier work was wrong

The recorded input lemmas are useful but do not directly expose the source shrinking and
the sheaf calculation following the algebra-level splitting. In particular, generic finite
algebra splitting returns rings and an algebra isomorphism, not lissity of a direct image;
the irreducible-strata theorem returns set pullbacks, whereas the existing lissity pullback
lemma takes underlying abelian pullbacks. The helper proofs explicitly account for this
comparison through `lem-weil-pbc-etale-inverse-image-algebraic-structures`.
No existing statement or definition was changed or disputed.

The available upstream generic-constancy theorem uses `IsConstructibleSheaf` and
`IsFiniteLocallyConstantSheaf`, with finitely generated abelian stalks. That theorem is not
a direct substitute for the item's predicates, which require finite underlying sets.
The finite-pushforward-constructibility theorem of `Sheaf` depends on this very item, so it
cannot be used to obtain a shorter proof without an import cycle.

Edge cases checked before finalizing the helper statements:

- Empty source, or a source with no dominating component: remove its closed image;
  the inverse-image source is empty and direct image is zero, with underlying singleton
  sheaf. The preservation helper allows zero factors in the split source.
- A zero sheaf, and an empty smaller open V: singleton stalks or vacuous stalk conditions
  satisfy the same finite-lissity assertions. No nonempty-source hypothesis was added.
- Nilpotent sources and finite purely inseparable maps: reduction and the universal
  homeomorphism equivalence apply; the helpers assume neither reducedness nor separability.
- Ramified finite covers: the preservation assertion is made only after dense shrinking,
  not on all of S. A cover such as x^2=t has changing geometric fibres at the branch point,
  which explains why the generic locus is necessary.
- Arbitrary, possibly nonaffine, smaller opens V: restrict the fixed etale splitting cover
  to V. This gives the same splitting locally on V, so the uniform conclusion needs no
  additional affine hypothesis on V.

## New nodes

`lem-weil-pbc-finite-source-generic-lisse` states the source-lissity conclusion of the first
three paragraphs of the original proof. Its proof records finite closedness, finite type
Noetherianity, reduction, irreducible lisse strata, removal of the closed bad image, and the
set/abelian inverse-image comparison. It becomes the independent source-shrinking item.

`lem-weil-pbc-finite-map-generic-lisse-preservation` states the sheaf-independent generic
preservation conclusion of the finite-algebra calculation and final paragraph. Its proof
records the fixed splitting cover, restriction of that splitting to all smaller opens,
transport through universal-homeomorphism equivalences, the finite product calculation,
finite exchange, and etale descent of local constancy and finite stalks.

Both nodes record real LeanFinder and Mathlib grep searches with no exact match. LeanSearch
returned an Internal Server Error for both queries and is recorded as unavailable, not as
an unsuccessful match. Searches of the full imported blueprint index for generic lissity,
lisse source, preservation of lissity, and finite pushforward produced no existing statement
of either helper. Search evidence is recorded in the sandbox `searches.jsonl`.
There are no change records because no existing statement or definition changed.

## Second reading by M1

1. Compared the delivered item module with the repository version. The target declaration signature is byte-for-byte unchanged; only proof imports and the proof body changed. The two helper modules and their node records are new, as declared in this report. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`; all compile without errors or warnings. The item has no `sorry`; the only new sorries are the two named helper theorems listed above. No forbidden declarations or hollow definitions occur. Verdict: pass.

3. Checked both split-off statements against the blueprint, edge cases, and searches recorded in `searches.jsonl`. Each is a strict intermediate result (source lissity and map-only preservation respectively), has a complete docstring proof and matching DAG node, and does not duplicate an existing library or Mathlib theorem. Verdict: pass.

4. Read the proofs and imports top-down. The item combines the two independent dense opens, uses the existing finite-locally-constant pullback theorem, and removes four proof-only imports that are no longer used. The helper imports are needed for their public statements and their planned proofs. Verdict: pass.

5. Compared each node's Lean declaration, proof steps, dependencies, origin, chapter, and unit with the delivered code. The target node depends exactly on the two helpers and pullback theorem; the unit `sk-prop-sf-cbc` has no realized route to preserve. Verdict: pass.

Changed during second reading: appended this review only; no Lean, DAG, or statement repairs were necessary.
