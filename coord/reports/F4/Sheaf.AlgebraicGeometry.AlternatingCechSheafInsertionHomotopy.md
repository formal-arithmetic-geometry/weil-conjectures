## What changed

Reduced `AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_homotopyEquivalence`
to two smaller public statements in separate modules. Its original signature and public
imports are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.AlternatingCechSheafSingletonRetraction` and
`Sheaf.AlgebraicGeometry.AlternatingCechSheafInsertionIdentities`.

The item's module proves that its source vanishes outside degree zero and its target
vanishes in negative degrees. It constructs the chain retraction from a degree-zero
projection, checks its composite with the augmentation, converts the insertion equations
into an actual `Homotopy`, and packages both homotopies into a `HomotopyEquiv` with the
required forward map. All five private helpers are proved. No definitions contain holes,
and no object is defined by choosing an arbitrary witness of an unproved existence result.
The two existential witnesses are eliminated only inside the proof of the public proposition.

All three modules compile together with `lcompile.py --all` without errors or warnings.
The ordered insertion signs were additionally checked on every coordinate basis for
constant integer coefficients with r=1 through r=5, every insertion index and every
nonempty tuple degree, including the degree-zero projection term. This finite check
supports the statement design; it is not a substitute for either remaining Lean proof.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_homotopyEquivalence`
(node `lem-pc-s3-alternating-cech-sheaf-insertion-homotopy`).
The item's module has no remaining `sorry`.

Added two holes, each exactly `:= by sorry`:

- `AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_degreeZero_retraction`
  (node `lem-pc-s3-alternating-cech-sheaf-singleton-retraction`): only the degree-zero
  module morphism and its retraction identity, not a chain map or homotopy.
- `AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_insertion_identities`
  (node `lem-pc-s3-alternating-cech-sheaf-insertion-identities`): degree-lowering maps and
  their cancellation identities, assuming a chain retraction already supplied.

This is a decomposition: one hole closed and two holes added (net -1), not a complete
proof from sorry-free dependencies. The second statement is for any chain retraction:
its docstring explains how to adjust the canonical singleton contraction to that retraction.
The r=0 case has no index i; empty opens and intersections give zero modules, and degrees
above the tuple bound give empty products. No cover, affineness, or quasi-coherence
hypothesis was added. The proof retains the same ordered insertion route as the parent.

## No longer needed

None. The existing public construction import and its definition node remain needed.
The proof already works directly on the restricted integer extension, so no new
extension/restriction comparison, all-tuple normalization, simplicial extra-degeneracy,
monomial Čech complex, or stalk-exactness module is imported or made into a dependency.
No existing planned dependency was removed. The unit record has empty realized lists;
its statement and proof route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect found. The parent's proof steps cite only the
construction node, which constructs the complex and augmentation but supplies no local
singleton retraction or insertion identities. Those parts of its existing argument are
now explicit separate obligations, rather than presumed available lemmas.

The source library's Čech exactness results use all tuples of indices and prove exactness,
not a homotopy inverse for this explicit increasing-tuple module-sheaf augmentation.
Its monomial contraction is also on all tuples and on different coefficient objects.
Mathlib's extra-degeneracy and Dold-Kan equivalences concern different complexes.
The two cited Stacks source pages were read; LeanSearch was unavailable, and semantic,
type-pattern and source searches found no exact replacement. No tool workaround or
forced adaptation was needed.

## New nodes

`lem-pc-s3-alternating-cech-sheaf-singleton-retraction`, in
`Sheaf.AlgebraicGeometry.AlternatingCechSheafSingletonRetraction`, states only the local
degree-zero retraction. Its proof is the singleton projection on a subordinate test open,
transported through sheafification, restriction, and degree-zero extension isomorphisms.

`lem-pc-s3-alternating-cech-sheaf-insertion-identities`, in
`Sheaf.AlgebraicGeometry.AlternatingCechSheafInsertionIdentities`, states the signed
insertion cancellation equations conditional on a chain retraction. Its proof pairs
faces, handles tuples already containing i, then adjusts the degree-one-to-zero operator
to an arbitrary chain retraction. Both nodes inherit the parent's chapter, unit and
blueprint ancestor. Their full Lean signatures, source, complete proofs in words and
three kinds of search are recorded. The parent proof and proof dependencies were updated
to match the Lean assembly. No change records were needed.


## Second reading by F4

1. **Interfaces unchanged — pass.** Read the repository/sandbox diff of the item.
   The existing public theorem signature and docstring are byte-for-byte unchanged,
   as is the construction's public import. The additions are five private helpers,
   two proof-only imports and the proof body. Both new public statements live in
   their own modules. No existing definition or target statement changed; no change
   record or forced adaptation is needed.
2. **Lean proof and axioms — pass as a decomposition.** Independently compiled all
   three modules with `lcompile.py --all`, without errors or warnings. A scratch
   copy with `#print axioms` checked both new statements, the item and all five
   private helpers. The helpers depend only on `propext`, `Classical.choice` and
   `Quot.sound`; the three public theorems also depend on `sorryAx`, precisely as
   expected from the two named obligations. Only those two public theorems have
   `sorry`; neither definition has a hole or chooses data from an unproved
   existence theorem. The existential projection and insertion operators are
   eliminated inside a proof of a proposition. No forbidden declaration or
   attribute appears. Checked the supported-source chain equation at degree -1
   and the direction of both homotopies in the final `HomotopyEquiv`.
3. **Split statements — pass.** Read both full signatures, docstrings and node
   records against the explicit product, face differential, sheafification and
   augmentation in `AlternatingCechSheafConstruction`. Read Stacks Tags
   [02FU](https://stacks.math.columbia.edu/tag/02FU) and
   [01FM](https://stacks.math.columbia.edu/tag/01FM): these supply the local
   insertion argument and ordered convention; the adaptation does not use a
   covering hypothesis. The singleton statement supplies only one degree map,
   not a homotopy inverse. The insertion statement supplies the remaining
   cancellation equations conditional on a retraction; the proved chain-map
   and homotopy assembly is a genuine reduction rather than a renamed target.
   Checked r=0 (no i), r=1 (augmentation is identity locally and all positive
   terms vanish), empty U i, tuples containing i, tuples without i, and negative
   and above-bound degrees. In Lean composition order, δ=p-p₀ satisfies
   a₀≫δ=0 and δ=d₀≫h₀≫δ; replacing h₀ by h₀-h₀≫δ≫a₀ changes d₀≫h₀ by
   -δ≫a₀ and leaves h₀≫d₀ unchanged because a₀≫d₀=0. Thus the claim for an
   arbitrary chain retraction is sound. Independently searched with LeanFinder
   for singleton projection on increasing tuples, Loogle for Homotopy/retraction,
   and the logged grep for Cech homotopy/retraction and insertion identities.
   Also searched repository Lean and DAG sources. Inspected the existing
   all-tuple local quasi-isomorphism, additive sorting homotopies, and ordered
   module projection/retraction statements: none supplies these maps for this
   explicit local increasing-tuple sheaf augmentation. Closing either obligation
   requires the actual presheaf/sheafification construction, beyond a short repair.
4. **Route and pruning — pass.** The construction public import is needed by the
   signatures, and each new plain import is used by the proof. There are no
   unused imports. The old proof_deps contains only the construction node, which
   remains used, so `No longer needed: None` is complete. Read the unit record
   `sk-thm-picard-f-representable`: its realized statement and sole step lists
   are empty. The ordered local insertion route is retained and no unit is
   bypassed. This delivery closes one hole and adds two, net -1; it is explicitly
   reported as a decomposition, not sorry-free progress.
5. **DAG agreement — pass.** Parsed and compared the parent's JSON: only `proof`,
   `proof_deps` and `proof_origin` changed. Its two steps match the supported
   chain-retraction construction and the conversion of cancellation identities
   into an actual homotopy. Every cited dependency is used. Each new node has
   its self-contained statement, exact Lean signature, source, complete proof,
   search records, status, creator, blueprint ancestry, chapter, unit and Lean
   record, and corresponds to the named public theorem with the same docstring.

Second reading changed only the incorrect report count from four to five private
helpers, removed excess blank lines before the existing theorem docstring, and
added this review. No mathematical or interface repair was necessary.
