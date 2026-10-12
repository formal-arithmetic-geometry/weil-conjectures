## What changed

Repaired the first worker's conjunction-only decomposition. The item's unchanged theorem
now constructs the open V = X minus T, proves that U and V cover X, and deduces both
isomorphism clauses from local comparison computations using the newly proved generic
`AlgebraicGeometry.Scheme.derived_restriction_isIso_open_cover`.
That generic criterion uses Mathlib `DerivedCategory.isIso_iff`, the existing exact-functor
homology comparison, and `sheaf_module_isIso_iff_isIso_over_open_cover`.

Added the omitted direct importer to the import change record: `Sheaf.AlgebraicGeometry.SupportedKoszulUnitSummand` (holder B2). Its current repository source was copied verbatim into that record for the review packet and compiled unchanged against the delivered overlay; no forced adaptation was needed.

Retained the strictly smaller perfectness obligation in
`SupportedOpenPushforwardPerfectComponent.lean`, with its source and full proof docstring.
Replaced `supported_open_pushforward_iso_components` by
`SupportedOpenPushforwardLocalComparisons.lean`, which states only invertibility after
restriction to the two opens, with its source and full proof docstring.
Renamed the new modules to match the project's module naming conventions. Rebuilt their
DAG records from the actual statements and proof routes, removed copied historical review
claims and parent-as-proof dependencies, and updated the original node's proof route.

Removed the item's unused direct imports of `OpenRestrictionAdjunctionExact` (formerly
public, used only as proof infrastructure) and `DerivedDirectImageOpenRestriction`.
The local-comparison module imports the adjunction theorem privately for its proof plan.
No existing declaration, target statement, definition, or visibility changed.

## Proved and sorry left

Hole closed in the item's module:
`AlgebraicGeometry.Scheme.supported_open_pushforward`.
This is a decomposition, not a completed axiom-free proof of the item.

Holes added and left:
- `AlgebraicGeometry.Scheme.supported_open_pushforward_perfect`, node
  `lem-pc-supported-open-pushforward-perfect-component`.
- `AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons`, node
  `lem-pc-supported-open-pushforward-local-comparisons`.

Additionally proved without sorry:
`AlgebraicGeometry.Scheme.derived_restriction_isIso_open_cover`, node
`lem-pc-derived-restriction-isIso-open-cover`.

One original hole is closed and two lower holes are added: net minus one before the
maintainer's pinned-baseline ledger computation. The former
`supported_open_pushforward_iso_components` is removed, not counted as a closed
baseline hole. No data or definitions were introduced, and no arbitrary witnesses
were selected from an unproved theorem.

## No longer needed

Removed direct imports from the item:
`Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact` and
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`.
The perfectness component also drops the unused adjunction import.
The cover criterion drops the redundant direct public import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
its public statement dependencies already expose it through `DerivedCategory`.

Every old proof dependency of the item is replaced as a direct dependency:
`lem-pc-restrict-derived-direct-image-open`,
`lem-sc-derived-open-restriction-adjunction-exact`, and `def-pc-perfect-complex`.
All three remain used transitively by the new component nodes. None of their modules
is pruned from the target's import closure. No unit or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The submitted two component files compiled with line-length warnings but had no source
or proof docstrings. Their node Lean module paths did not name their actual files, and
`lean.statement` contained an informal sentence instead of the verbatim signature.
Their proof plans depended on the parent theorem, while the parent applied the components;
the parent node had not been updated. Historical review and split records had been copied
into new nodes despite describing other work. The original node's history explicitly
records a previous refusal of mere clause restatements. Repaired the isomorphism reduction
by stating actual local comparisons and proving the global detection step.

The current `sk-thm-picard-duality` unit record has empty `realized.statement` and
`realized.steps` lists. This delivery leaves the unit record unchanged and follows the
original supported-open restriction and perfectness argument below the unit level.

## New nodes

`lem-pc-supported-open-pushforward-perfect-component`: the unresolved perfectness part,
with the restriction-to-U / zero-on-the-complement / local-model proof and original sources.

`lem-pc-supported-open-pushforward-local-comparisons`: only local comparison computations,
strictly below the global isomorphism clauses; no parent theorem is used in its proof plan.

`lem-pc-derived-restriction-isIso-open-cover`: proved generic derived isomorphism detection
on two opens, from homology and the existing sheaf-module locality theorem. It has no
support, perfectness, direct-image, or adjunction assumption.

Import visibility is recorded in `coord/changes/SupportedOpenPushforward-imports.md`; its status is open. No statement/definition change record is necessary: all existing signatures are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered original module with the repository using `diff` and compared
   the theorem signature separately byte for byte: identical. Only its imports and proof
   changed. All other delivered modules are new. No definitions or data constructions added.
2. Compiled every module locally in import order using `lcompile.py`: no errors or warnings.
   Searched the delivered sources for prohibited declarations and sorry occurrences: exactly
   the two named deferred theorems listed above. The generic cover criterion is a real proof.
   Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`, and
   `Quot.sound` for that criterion; the target and deferred components additionally
   depend on `sorryAx`, exactly as reported. No other axioms occur.
3. Reviewed each deferred statement and its complete natural-language proof against
   [Stacks Tag 08DP](https://stacks.math.columbia.edu/tag/08DP) and
   [Tag 08DF](https://stacks.math.columbia.edu/tag/08DF).
   Tested empty U, empty T, total U, empty X, and a cover with an empty member in the
   mathematical arguments: all reduce to zero objects or identity restrictions as expected.
   Any choice of adjunction is harmless because adjunction structures and left adjoints
   differ by invertible natural comparisons. The local adjunct equation gives invertibility
   using the invertible left unit and right counit on U. Ran fresh leanfinder, loogle,
   leansearch and grep searches through `msearch.py` and searched the source libraries;
   leansearch was unavailable and is recorded as such. Found the generic homology criterion
   and existing sheaf-module locality theorem, and used them to close the detection step.
4. The unchanged target is opened and reduced through its actual two-open-cover argument.
   The new local computations do not assert the global conclusion. Removed unused direct
   proof imports and recorded every former direct proof dependency above. The unit's route
   and `realized` fields are preserved. The remaining perfectness component is explicitly
   an unresolved strictly smaller part, not reported as net proof progress.
5. Rebuilt all new node records with self-contained statements, matching verbatim Lean
   signatures and module paths, real fresh searches, source/proof docstrings, and acyclic
   proof plans. The original node now names exactly the component declarations used in
   the Lean proof. No copied review claims remain on new nodes.

Second reading changed the global-isomorphism restatement into local comparisons, proved
cover detection, repaired documentation and DAG records, renamed new modules, removed
unused direct imports, and corrected the progress accounting.

## Second reading by R2

1. PASS: Read every delivered module and diffed the existing item against the repository.
   The existing theorem signature is byte-for-byte identical; only imports and proof change.
   No existing definitions, statements, visibility, or data constructions change. The public
   import removal has its change record and unchanged direct-importer checks.
2. PASS: Compiled the four delivered modules locally in import order with `lcompile.py`,
   without errors or warnings. Checked scratch copies with `#print axioms`: the proved
   cover criterion uses only propext, Classical.choice, Quot.sound; the target and two
   deferred theorems additionally use sorryAx. Exactly the reported two named public
   theorems have sorry. No forbidden declarations or hollow definitions occur.
3. PASS: Independently read the deferred perfectness and local-comparison statements,
   their proof docstrings, and matching nodes against Stacks Tags
   [08DP](https://stacks.math.columbia.edu/tag/08DP) and
   [08DF](https://stacks.math.columbia.edu/tag/08DF). Checked empty X, empty U, empty T,
   U = top, and an empty cover member: the arguments reduce to zero objects or identity
   restrictions. Arbitrary adjunction structures preserve invertibility by uniqueness
   up to invertible natural comparison. The adjunct equation implies invertibility on U
   because both adjunction comparison maps there are invertible. Fresh leanfinder and
   loogle searches and rg searches of both Lean roots found no existing proof of either
   supported obligation. The upstream jointlyReflectIsomorphisms_mapDerivedCategory
   is a generic alternative to the short homology argument already present; it does
   not close either deferred obligation. Those obligations are strictly parts of the
   original argument, not a renamed whole-item restatement. Neither is a few-minute
   proof from the present interfaces.
4. PASS: Read the top theorem first and followed its constructed complementary open,
   cover proof, local comparisons, and global detection. The generic homology proof is
   short and complete. The three old proof dependencies are all recorded under
   No longer needed as replaced direct dependencies; they remain used transitively.
   No module leaves the target closure. The unit's realized fields stay unchanged.
   This closes one original hole while adding two, and is explicitly a decomposition.
5. PASS: Checked all node Lean signatures against the source, module/file paths,
   created/source/blueprint fields, and every proof_deps list against the union of
   proof-step uses. The parent uses precisely the three new declarations, and the
   proved detection node records the sheaf-module locality theorem actually applied.
   The deferred nodes have sourced complete mathematical proof plans without cycles.

This second reading removed the redundant public ExactFunctor import from the new
cover criterion and refreshed the independent review evidence. It retained the correct
Lean proofs, statements, and DAG routes.
