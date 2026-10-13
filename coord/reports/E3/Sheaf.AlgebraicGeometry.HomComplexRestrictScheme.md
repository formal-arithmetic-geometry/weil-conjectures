## What changed
Added `InternalHomOverEquiv.lean` and `HomComplexRestrictSchemeTransport.lean`.
The unchanged theorem `AlgebraicGeometry.homComplex_restrict_scheme` obtains the natural
internal-Hom comparisons and applies the product/differential transport theorem.
The second reader proved the transport theorem, keeping the existing open-site restriction
route. Only the two new theorem modules are imported for the target proof.
Public imports of the new transport module provide only its signature's definitions;
open restriction, projections, product preservation and adjunction additivity are private imports.
No existing statement, definition or visibility changed. No change record is required.

## Proved and sorry left
Original hole closed: `AlgebraicGeometry.homComplex_restrict_scheme`
(node `lem-sc-hom-complex-restrict-scheme`). Its proof still depends on the one hole below.
New theorem proved during second reading:
`AlgebraicGeometry.homComplex_restrict_scheme_of_homIso`
(node `lem-sc-hom-complex-restrict-scheme-transport`), from the supplied internal-Hom
naturality, actual product limits, the signed differential formula and the existing
`CategoryTheory.homComplex_restrict_open`.
Hole added and remaining: `AlgebraicGeometry.internalHom_overEquiv`
(node `lem-sc-internal-hom-over-equiv`). This is the only `sorry` in the delivery.
There are no holes in definitions, private helpers or partial proofs.
Relative to the repository this closes one hole and adds one: a decomposition, with
net zero holes eliminated, not an unconditional proof of scheme restriction.
Relative to the first worker's submission, the second reading closes the transport hole.

## No longer needed
Removed from the first worker's target: the proof-only imports
`Sheaf.Algebra.Homology.HomComplexProjections`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`, and the unused `Limits Opposite` open.
The original target's direct import `Sheaf.Algebra.Homology.HomComplexRestrictOpen` is
now imported privately by the proved transport module, where its theorem is used.
The old direct proof dependencies `def-pur-hom-complex`, `def-pur-sheaf-hom`, and
`lem-sc-hom-complex-restrict-open` remain needed transitively through the new nodes;
none is mathematically pruned, and no old module leaves the target's import closure.
No modules pruned.
The new transport module also omits the unused explicit
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` import.
It does not need to import `InternalHomOverEquiv`: it assumes
an arbitrary natural family of comparisons. Its proof does not use that unproved theorem.

## Where the brief, the DAG or earlier work was wrong
The original DAG recorded scheme-site transport as elementary without a Lean interface.
The first submission moved both internal-Hom transport and the entire product/differential
transport into unproved statements, but omitted the original node's revised proof route.
The second reading completed product/differential transport and updated all proof records.
The first report called the upper statement proved without distinguishing the resulting
one-closed/two-added decomposition; the final counts above correct that.
The unit `dag/units/sk-thm-picard-duality.json` already has empty `realized.statement` and
`realized.steps` entries. This delivery does not modify that unit or bypass its route;
its recorded open-restriction, internal-Hom, product and differential steps are retained.
The first worker's import-only change record was unnecessary: the existing module's
public imports and public signatures are unchanged. It has been removed.
The cited Stacks text was read online at [08DL](https://stacks.math.columbia.edu/tag/08DL)
and [0A8X](https://stacks.math.columbia.edu/tag/0A8X). The former states derived restriction
compatibility; the ordinary comparison here follows from its construction, not a direct
application of that derived theorem. The latter specifies the arbitrary integer-indexed
product and differential with the same sign used in Lean.

## New nodes
`lem-sc-internal-hom-over-equiv`: `lean/Sheaf/AlgebraicGeometry/InternalHomOverEquiv.lean`.
The one remaining statement concerns only module sheaves and their pre/postcomposition
naturality, strictly below the complex comparison. Its docstring describes transporting
local linear maps and the inverse along the slice equivalence and scalar isomorphisms.
`lem-sc-hom-complex-restrict-scheme-transport`:
`lean/Sheaf/AlgebraicGeometry/HomComplexRestrictSchemeTransport.lean`.
It is now proved, has no internal-Hom existence premise hidden in its proof, and records
the open restriction, projection specification, product and differential construction.
No change records.

## Second reading by E3
1. Compared the delivered target with the repository using `diff`. The original theorem
   signature and docstring are byte-for-byte unchanged, as are all original public imports.
   The two new statements agree verbatim with their new nodes. Verdict: pass.
2. Compiled every delivered module locally using only `lcompile.py`; final compilation
   and axiom verification are recorded below. Scanned for `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern` and holes in definitions: none. The only remaining `sorry`
   is the named public theorem listed above. Existential elimination from it occurs in
   a theorem proving a proposition, never in a data definition. Verdict: pass.
3. Read both split statements and tested the argument on U empty or all of Y, zero
   modules, zero complexes and unbounded complexes. The slice/scalar transport is still
   an equivalence in those cases; product transport uses every integer factor and no
   boundedness assumption. Naturalities cover pre- and postcomposition separately and
   retain the differential sign. Repeated LeanSearch, LeanFinder, Loogle and grep searches with new
   queries (logged in searches.jsonl), and searched the upstream InternalHom and
   InternalHomOver files. No exact internal-Hom comparison for overEquiv is available.
   Loogle does not index the upstream `SheafOfModules.homObj`; this search limitation is
   recorded, not counted as a successful no-match. LeanSearch returned an Internal Server
   Error for both statements, also recorded without a no-match verdict. Cartesian closed exponential comparisons
   are not the module-sheaf internal Hom here. Verdict: pass.
4. Checked the proof top downward against the original plan. The proved transport uses
   `homComplex_restrict_open`, the actual degreewise product universal properties and
   projection differential formula, followed by `overFunctorEquiv` on all three complexes.
   Removed unnecessary imports and report claims. No old dependency is bypassed or pruned;
   the unit's existing realization gap is reported above. Verdict: pass.
5. Updated the original node's proof and proof_deps to the two new declarations.
   The transport node now cites the projection node and no longer cites internal-Hom
   existence as a proof dependency: its comparisons are hypotheses. Checked new nodes'
   source, searches, created, blueprint, chapter/unit and verbatim Lean records.
   Verdict: pass.

Changed during this reading: proved the transport theorem; removed unnecessary target
imports and the transport's import of internal-Hom existence; made proof-only imports
private; updated the original and transport DAG proof routes and actual search evidence;
removed the unnecessary change record; corrected the hole counts and pruning report.

Final verification: `lcompile.py --all` compiled all three final modules without errors
or warnings. The recorded wall times include waiting for shared compiler slots; no
file exceeded the compiler's 60-second execution timeout. Log: `scratchpad/final-compile.log`.
The scratch target copy with `#print axioms` for all three declarations also compiles.
The transport theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
The internal-Hom theorem and target additionally use `sorryAx`, exactly as accounted
for by the one remaining internal-Hom hole. No other axiom occurs.
Log: `scratchpad/axioms.log`; the scratch copy is outside the delivered source set.

The first dry run rejected only missing LeanSearch-category records for the two new
nodes. Real LeanSearch requests returned Internal Server Error; their unavailable
responses are now recorded alongside the completed LeanFinder/Loogle and grep searches.
