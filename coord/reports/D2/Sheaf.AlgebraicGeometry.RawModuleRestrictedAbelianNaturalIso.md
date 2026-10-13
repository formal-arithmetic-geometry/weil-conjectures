## What changed
The original theorem `AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_natural_iso`
keeps its exact signature. Its proof splits at degree zero. The nonnegative case remains
an open theorem in `RawModuleRestrictedAbelianNonnegative`; the negative case is now
proved in `RawModuleRestrictedAbelianNegative` using standard t-structure orthogonality
and nonnegative concentration of right derived global sections.
The two comparison modules are proof-only imports. Two unchanged upstream source copies
(`EtaleComplexCohomologyPresentationData` and `RestrictedOverAbelianComplexData`) remain
in the sandbox to supply locally compiled dependencies; they have no delivered changes.
No definition, public import, or existing statement changes. No change record is needed.

## Proved and sorry left
Original hole closed: `AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_natural_iso`.
New hole added: `AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_nonnegative`
(node `lem-sbc-raw-module-restricted-abelian-nonnegative`).
The first worker's proposed hole `AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_negative`
(node `lem-sbc-raw-module-restricted-abelian-negative`) is closed by a foundational proof.
There are no other new holes. The original theorem still depends on the open nonnegative
comparison: this is a partial decomposition, not an axiom-free proof of the entire item.
One original hole is closed and one lower hole added; the local hole net is zero.
Unchanged upstream copies retain their baseline holes and add none.

## No longer needed
Removed the item's proof-only import `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`.
All three original direct proof dependencies are no longer directly used by the top proof:
`lem-weil-pbc-injective-module-abelian-acyclic`, `lem-weil-pbc-inverse-image-composition`,
`sbc-lem-higher-image-raw-over-naturality`. They remain in the nonnegative argument's plan
and/or in the statement import closure; no library module is claimed globally pruned.
The top node's proof dependencies now name its two degree cases.

## Where the brief, the DAG or earlier work was wrong
The earlier report incorrectly said local compilation was blocked. The unchanged upstream
copies compile locally and supply the missing objects. The first worker's split-node
statements and Lean records repeated the original unrestricted theorem rather than their
actual degree restrictions. Their proof docstrings were incomplete, and they had style
warnings. The original node still recorded its old proof route. These are repaired.
The stray change record had only a Users section and was unnecessary for proof-only edits;
it is removed. The negative case needs no unresolved scalar comparison.

## New nodes
`lem-sbc-raw-module-restricted-abelian-nonnegative`: the remaining nonnegative comparison,
with the exact natural-number degree signature, source, and complete proof plan.
`lem-sbc-raw-module-restricted-abelian-negative`: the proved negative-degree comparison,
with exact signature and the zero-object proof recorded. No change records.

## Second reading by D2
1. Compared every sandbox Lean module with the repository using diff. The two upstream
copies are identical. The original declaration signature is byte-for-byte unchanged;
only its proof and private proof imports change. No definitions are added or changed.
2. Compiled all modules using lcompile.py. The negative case is proved without sorry;
the only newly delivered sorry is the named nonnegative theorem. No axiom, unsafe,
opaque, extern, implemented_by, or hollow definition appears. Explicit scratch `#print axioms` checks on all three comparison theorems returned
only propext, Classical.choice, Quot.sound and sorryAx. The negative theorem has no
local hole but still inherits sorryAx from open upstream dependencies. The required
dry run also probes every delivered declaration.
3. The degree-zero and positive-degree cases use the injective-resolution sections
comparison of Tags 03FD and 03Q8; the naturality formula uses the fixed five factors,
without limit or qcqs hypotheses. Zero coefficients and empty test objects give zero
section complexes. The negative case, including q=-1, is proved by orthogonality and
negative derived-section vanishing. Independent leanfinder, loogle and grep searches,
plus local reads of ModuleAbelianDerivedDirectImageComparison and
RawRestrictedCohomologyNaturalIso, found building blocks but no complete module-raw
comparison. The remaining open theorem covers only nonnegative degrees; the negative
part of the original argument is now fully proved rather than renamed as another hole.
4. Used the shorter standard t-structure route for negative degrees and removed the
unused proof import. The unit `sk-lem-failure-field` has no realization pointing at
this node; no unit statement, step, or route is changed. Every removed direct DAG
dependency is listed above; no global module pruning is claimed.
5. Corrected the new nodes' degree restrictions and verbatim Lean signatures, and
updated the original node to the actual degree-split route. Sources, chapter and unit
agree with the original item. New statements have source/proof docstrings and nodes.
Second reading changed: proved the negative case; completed docstrings; fixed split
node records and top proof dependencies; removed unused import, style warnings,
and unnecessary malformed change record; replaced the stale report.
