## What changed

Repaired return X-85771. Moved `AlgebraicGeometry.exists_chow_modification_data` to
`Sheaf.AlgebraicGeometry.ChowModificationData` and
`AlgebraicGeometry.exists_chow_algebraization_data` to
`Sheaf.AlgebraicGeometry.ChowAlgebraizationData`, one new statement per module.
The geometric witness now includes finite projective coordinates, an immersion `e`,
and its equation over Spec A. The algebraization helper requires that same data.
The assembly installs `IsProper q` and `IsImmersion e`, passes `n`, `e`, and `he`, and
assembles the original conclusion without changing its signature. Restored the original
target docstring immediately before the target theorem and gave each helper a complete
source-and-proof docstring for its corrected signature.

Updated both new nodes' statements, exact Lean signatures, module/file paths, and proof
routes, and the target node's assembly route. Deleted the copied `reviewed` and
`reviewed_proof` keys from both new nodes. Updated both change records.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_chowPullbackAlgebraization`
(node `lem-weil-pbc-chow-pullback-algebraization`) by a complete Lean existential assembly.
Added two holes, which remain the whole proofs of named public theorems:

- `AlgebraicGeometry.exists_chow_modification_data` (`new-chow-modification-data`).
- `AlgebraicGeometry.exists_chow_algebraization_data` (`new-chow-algebraization-data`).

This is a decomposition: one upper hole closed and two lower holes added, net minus one.
The target still depends on these unproved helpers; no claim of axiom-free completion is made.
All three delivered modules compile with `lcompile.py --all`; the only two direct
sorry declarations are the helpers.

## No longer needed

Removed all seven old plain imports from the item module:

- `Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective`.
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`.
- `Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`.
- `WeilConjectures.AlgebraicGeometry.ChowLemma`.

The assembly now uses only the two new plain helper imports. In `ChowModificationData`,
ChowLemma supplies the proper map, immersion, and dense restriction isomorphism;
ReducedInducedClosedSubscheme supplies the reduced complement ideal. In
`ChowAlgebraizationData`, projective existence supplies algebraization of the extension,
finite-type support pullback identifies the pulled supports, pushforward coherence on an
open handles extension by zero, and the two closed-subset properness modules handle
proper preimages, closed images and closed subsets. These are retained as proof-route
imports of the relevant remaining helper, rather than unused imports of the assembly.
Its other retained dependencies are FormalSystemsPullback (public, also needed by its
statement), AdicCompletion.Basic (public, Jacobson-radical argument),
ModuleSupportProperOverBase (scheme-theoretic support), and
Cohomology.DirectImage.FiniteFreeComplex (proper coherent pushforward).
The helpers' proof-dependency nodes remain needed for their documented arguments;
no global pruning of those nodes or modules is claimed. The assembly node no longer has
any direct dependency on the seven old route imports.

Every old direct `proof_deps` entry removed from the assembly node is listed here:
`def-nagata-scheme-theoretic-image`, `def-weil-pbc-coherent-formal-module`,
`lem-pc-coherent-hi`, `lem-weil-pbc-adic-complete-jacobson-radical`,
`lem-weil-pbc-chow-noetherian`, `lem-weil-pbc-closed-subset-proper-over-base-properties`,
`lem-weil-pbc-closed-subset-proper-over-base-union-preimage`,
`lem-weil-pbc-formal-systems-pullback`, `lem-weil-pbc-grothendieck-existence-projective`,
`lem-weil-pbc-module-support-proper-over-base`, `lem-weil-pbc-pushforward-coherent-on-open`,
`lem-weil-pbc-reduced-induced-closed-subscheme`, `lem-weil-pbc-support-pullback-finite-type`,
`lemma-nagata-immersion-open-in-scheme-image`, and `pqf-lem-locnoeth-lft`.
These are removed as direct assembly proof dependencies, not globally pruned: the
coherent-formal-module definition remains a statement dependency, and all other entries
are assigned to the corresponding helper's documented proof route. In particular,
the algebraization helper records scheme-theoretic image, immersion-open-in-image,
and finite-type Noetherianity explicitly. No module is pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

E1/D1: The returned geometric conclusion admitted `Y = Z`, `q = 𝟙 Z`, `L = ⊤` without
retaining any quasi-projective data. Its algebraization helper thereby hid the general
algebraization problem. The corrected geometric conclusion also requires an immersion
into a finite projective space over A. The corrected algebraization proof constructs the
scheme image from that supplied immersion and uses its equation over the base.
H8: The returned helper comments were ordinary comments, and the original target docstring
was attached to a helper. Both defects are repaired.
H1/H9: The helpers are now separate modules; the assembly's seven unused imports are removed.
B/F: Both new nodes had copied historical U2/COMPILER reviews and landing metadata; removed.

## Earlier second reading (a previous round; superseded)

Repair assessment replacing the returned draft's assessment; an independent second reader
still performs the delivery review. The original target statement and public imports are
unchanged. The new geometric conclusion retains the immersion and equation that Stacks 088E
uses before constructing a projective compactification. An identity modification is still
allowed when Z has such an immersion, which is legitimate: in that case the supplied
immersion itself constructs the projective closure. Choosing only `q = 𝟙 Z` and `L = ⊤`
no longer discharges the geometric conclusion and no longer lets the algebraization helper
apply to an arbitrary Z.

The algebraization helper's docstring explicitly uses `e` and `he` to form Y', extends the
pulled formal system using its closed proper support, checks coherence and quotients locally,
applies projective existence, excludes boundary support by Jacobson radical and Nakayama,
and restricts before taking proper coherent pushforward. For an empty Y the zero coherent
module supplies the conclusion; for I = 0 the completion is constant and the same route
applies. The geometric helper uses nonemptiness of Z to ensure the dense open and projective
coordinate type are nonempty. These checks address the identity-modification failure without
claiming that the former unrestricted fixed-modification assertion was a smaller problem.

The final Lean proof combines the geometric existence statement with algebraization under
its supplied quasi-projective data. The DAG matches this passage of data. The item is not
one of the `realized` statements or steps of `sk-thm-p1`, whose route remains unchanged.
The corrected three-module set compiles; both new nodes have no purported past review.

## New nodes

`new-chow-modification-data`: geometric Chow data including the finite projective immersion,
stated in `lean/Sheaf/AlgebraicGeometry/ChowModificationData.lean`.
Change record: `coord/changes/exists_chow_modification_data.md`.

`new-chow-algebraization-data`: algebraization from the supplied quasi-projective immersion,
stated in `lean/Sheaf/AlgebraicGeometry/ChowAlgebraizationData.lean`.
Change record: `coord/changes/exists_chow_algebraization_data.md`.

## Second reading by W3

1. **Visible declarations: PASS.** Compared the delivered item against the repository with
   `diff -u`. The sole existing theorem's signature and original docstring are byte for byte
   unchanged; its public imports are unchanged. The two other modules and declarations
   are new, and both have change records. There are no definitions or forced adaptations.
2. **Lean proof and axioms: PASS as a decomposition.** Compiled all three modules locally
   in import order, with no diagnostics. Compiled scratch copies with `#print axioms` for
   all three declarations: only `sorryAx`, `propext`, `Classical.choice`, and `Quot.sound`
   occur. The two helper theorems are the only direct holes, each a whole named public
   theorem proof with its matching node and source-and-proof docstring. No forbidden
   declarations, hollow definitions, or arbitrary data chosen from unproved existence
   occur in this delivery. The assembly extracts witnesses inside a proposition proof.
3. **Split statements: PASS.** Read both helpers and the declarations of their route
   dependencies, and compared the argument with Stacks Project Theorem 088E
   (https://stacks.math.columbia.edu/tag/088E). The geometric helper is purely geometric;
   the other handles a fixed supplied projective immersion. Neither restates the target.
   Tested empty Y (zero module), zero G (zero algebraization), I = 0 (constant system),
   and identity q (requires the supplied immersion). For the zero ring the geometric
   nonempty-source hypothesis is impossible. Finite coordinates cannot be empty when
   the proper surjective modification has nonempty target. The compactification,
   closed proper support, extension, projective existence, and boundary exclusion give
   the algebraization conclusion without assuming it. An alternate LeanFinder query for
   quasi-projective coherent formal algebraization with proper support returned Proj
   properness and unrelated section lemmas; Loogle `ProjectiveSpace, Equiv` could not
   resolve the project's identifier and establishes no absence result. A local grep
   for reindex/congr/rename of ProjectiveSpace and quasi-projective completion found
   no replacement. Read ProjectiveSpace and ChowLemma: coordinate reindexing is not
   already provided there. No helper can be closed in a few minutes from these APIs.
4. **Top-down route and pruning: PASS after report repair.** The target assembles two
   strictly smaller stages. Its seven old plain imports move to the relevant helper;
   the report now enumerates every old direct proof dependency, including those that
   remain as statement dependencies or transitive proof dependencies. Public imports
   supply signature types or instances; helper route imports are plain. No global
   module pruning is claimed. Checked `dag/units/sk-thm-p1.json` `realized`: neither
   the item nor the two new nodes realize one of its prescribed statements or steps,
   and its route is unchanged. This remains one closed upper hole and two added lower
   holes (net minus one), not an axiom-free proof of the original result.
5. **Nodes versus Lean: PASS after metadata repair.** Existing node differs only in
   `proof`, `proof_deps`, and `proof_origin`; its route matches the existential assembly.
   New nodes have signatures matching their own modules, sources, docstring arguments,
   creation records, searches, chapter/unit, and no copied review claims. Added the three
   compactification/Noetherianity dependencies actually mentioned in the algebraization
   argument, and prepended the item to both new nodes' blueprint ancestry paths.

Second reading changed only the assembly's local instance syntax (`letI` to `have`),
removed its unnecessary `linter.style.haveILetI` suppression and one extra blank line,
completed the removed-dependency inventory, corrected the new nodes' dependency/ancestry
metadata, and added this independent review. No theorem signature or definition changed.
