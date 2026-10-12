## What changed

Replaced the original equivalent reformulation of short exactness by a genuine two-step
reduction. `ArtinSchreierSchemeSectionData` states construction of the fixed lifted structure
sheaf's section equivalences, maps, zero composite and three section formulas, without
exactness. `ArtinSchreierSchemeSectionExact` states exactness for an arbitrary supplied
abelian sheaf and supplied maps satisfying those formulas; it constructs no maps.
`exists_artinSchreier_shortExact` combines these results. Its existing signature is unchanged.
The unused direct proof imports in the target module were removed; all new imports used
only by the target proof are plain imports. The new helpers have no definitions.

## Proved and sorry left

The original `AlgebraicGeometry.Scheme.exists_artinSchreier_shortExact` now has a complete
Lean reduction with no direct sorry. It is not axiom-free yet: it depends on these two
named open theorems, each with its full source argument in its docstring and node:

- `AlgebraicGeometry.Scheme.exists_artinSchreier_section_data`, node
  `lem-sc-artin-schreier-scheme-section-data`.
- `AlgebraicGeometry.Scheme.artinSchreier_section_data_shortExact`, node
  `lem-sc-artin-schreier-scheme-section-exact`.

Local compilation of all three modules passes. Scratch `#print axioms` checks for all
three declarations list only propext, Classical.choice, Quot.sound and sorryAx. There are
no axioms, unsafe/opaque declarations, implementation bypasses, or hollow definitions.

## No longer needed

Removed the target's direct imports of `ConstantSheafGeometricStalk`, `EtaleTensorSections`,
`TensorPullbackStructureSheaf`, `ArtinSchreierKernel`, `PullbackCarrier`, and `EtalePoint`.
The original DAG proof dependencies are retained in the two new helpers' proof plans:
none is globally pruned by this reduction. The target's direct proof_deps are now the two
new nodes. The rejected, never-landed `ArtinSchreierMapsProperties` module and
`lem-sc-artin-schreier-sequence-scheme-properties` node were removed from the sandbox.

## Where the brief, the DAG or earlier work was wrong

The first worker's component-properties theorem was equivalent to the whole original
statement: existence of maps plus mono, epi and exactness is precisely existence of a
short exact sequence. Applying ShortExact.mk' did not make that new sorry strictly smaller.
The earlier second reading's assertion that it was strictly weaker was incorrect.
The repair separates construction from exactness of already supplied maps and explicitly
carries the section formulas between those parts. The library's curve-only
`artinSchreier_data` and `artinSchreier_data_shortExact` require a curve over an algebraically
closed field and cannot discharge this arbitrary-scheme theorem. Upstream relative
affine-space Artin-Schreier geometry supplies cover prerequisites, but no exact match
for either new statement. No target statement or definition was changed.

## New nodes

`lem-sc-artin-schreier-scheme-section-data` records only section identifications and map
construction, with naturality and the formulas required by the second step. Its statement
has no exactness conclusion. `lem-sc-artin-schreier-scheme-section-exact` records local
surjectivity and kernel identification for given maps with those formulas, not their
existence. Both have Lean signatures, source arguments, dependency records, and actual
leanfinder, loogle and grep searches; LeanSearch was attempted and returned an internal
server error, recorded as unavailable. There are no change records because no existing
signature or definition changes.

## Second reading by C1

1. Compared the original module and its sandbox version by diff and declaration-table
   inspection. The existing theorem signature and all public imports remain unchanged;
   only its proof and proof-only imports change. No existing definition changes. The
   additional declarations are in new modules with new matching nodes. Verdict: pass.
2. Compiled every delivered module through lcompile.py and compiled scratch copies with
   #print axioms on all three declarations. No errors; only the three permitted axioms
   and sorryAx from the two documented helpers. Neither helper has a partial anonymous
   sorry; there are no forbidden declarations or hollow definitions. Verdict: pass as
   a partial proof, not a completed axiom-free Artin-Schreier theorem.
3. Rejected the first split as an equivalent restatement and replaced it. The revised
   construction has no exactness and the revised exactness assumes specified maps and
   section formulas, so neither simply restates the original existential conclusion.
   Checked p=2, empty schemes, disconnected schemes, and nonreduced characteristic-p
   schemes: Frobenius additivity holds; local polynomial covers do not require fields;
   stalk kernels are computed in nonzero local rings, not arbitrary global section
   rings. On the empty site the sheaves are zero. Searched with different terminology
   through leanfinder, loogle, grep, the local library and upstream sources. The curve
   statements and geometric-cover prerequisites are not duplicates. Verdict: pass;
   neither remaining sheaf construction nor stalkwise exactness closes in a short repair.
4. Read the original dependencies and sk-prop-cd unit record. Its Artin-Schreier route is
   retained; the unit and realized fields are unchanged. Removed unused target proof
   imports. No old proof dependency is discarded from the transitive helper plans.
   The target uses the construction data in the exactness step. Verdict: pass.
5. Checked the existing node's proof/proof_deps/proof_origin against the new reduction,
   and the two new nodes' declarations, verbatim signatures, source, complete proof
   descriptions, dependency unions, searches (including the unavailable LeanSearch attempt), creation and blueprint fields. No node
   refers to the rejected equivalent reformulation. Verdict: pass.

Second reading changed the invalid restatement into two genuine intermediate theorems,
rewrote the target reduction and node plans, removed unused direct proof imports,
and corrected the report's progress and axiom claims.
