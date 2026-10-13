## What changed

Replaced `picardExternalCechCupComponent_exists` with a complete Lean assembly proof,
without changing either original public signature. Added a proof-only import of
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential`.

The new module `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree` constructs the
k-linear map on every tensor summand. It uses the existing
`exists_scalarPullbackCoefficient` to obtain normalized k-linear unit section maps,
composes Cech coordinate projections with restrictions, tensors these maps, and uses
`scalarTensorCoefficientApp` and the categorical product universal property. Its
coordinate proof also accounts for the chosen product opens versus infimum opens.
No data is defined by an arbitrary existence witness: private scalarUnitSection uses
the existing coefficient theorem whose section formula uniquely determines its map.

The new module `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential` explicitly
constructs total-degree maps using `mapBifunctorDesc` and proves their summand inclusion
equation. Its adjacent-degree differential identity is left as one named theorem.
The original theorem chooses the proved summand maps inside its proof, combines the
differential identity with `CochainComplex.ofHom`, and proves its unchanged coordinate
predicate from the inclusion equation. The original node records this route.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupComponent_exists`
(node `lem-sc-picard-external-cech-cup-component`). Its module contains no sorry.

Also proved:
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_exists`
(node `lem-sc-picard-external-cech-cup-bidegree`) and
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_ι`
(node `lem-sc-picard-external-cech-cup-differential`), together with the private section
and product-coordinate helpers used by these proofs.

Added exactly one hole, the only sorry in the delivery:
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm`
(node `lem-sc-picard-external-cech-cup-differential`). It states only the adjacent
differential equation for given degree maps with the specified summand coordinates.
It does not assert existence of a cochain morphism or repeat the original conclusion.
The remaining work is the signed alternating-face differential calculation.

This delivery closes one upper hole and adds one lower hole: it is a decomposition
with net hole change zero, plus a proved bilinear construction. It does not claim that
the original theorem is independent of sorry.

## No longer needed

No imports, nodes, or modules were pruned. The original three public imports remain
necessary for the existing statements and definitions. The old dependencies are used
by the bilinear construction and the remaining differential step. Neither the unit's
statement nor its route is bypassed; its `realized` fields are empty in this checkout.

## Where the brief, the DAG or earlier work was wrong

No statement error or interface correction was necessary. The prior node grouped the
bilinear construction, total-degree assembly, and differential calculation in one
proof step; this delivery separates those parts and makes the first two explicit.

The brief's local `literature/stacks-project/` TeX paths are absent on this machine.
The official Stacks pages https://stacks.math.columbia.edu/tag/0BED and
https://stacks.math.columbia.edu/tag/07MB were read instead. LeanFinder found only
category-theoretic tensor and alternating-face constructions. Loogle identified
`mapBifunctorDesc` and `ι_mapBifunctorDesc`. Mathlib and project rg searches found the
scalar coefficient maps used above, but no existing external differential identity.
LeanSearch returned an Internal Server Error; no mathematical conclusion is drawn
from that unavailable service. Blueprint searches for external Cech cup and 07MB
found no matching imported node.

Edge cases checked in stating the differential lemma: there is no cover, finiteness,
quasi-coherence, or positive-degree hypothesis. Empty families give empty coordinate
products, zero coefficients give zero tensor pairings, and p=q=0 uses the shared
vertex with sign +1. Degree maps are explicit coproduct descents, and the adjacent
commutation equation is the signed tensor differential with the same convention as
`CechCupProduct`. These checks do not substitute for the remaining Lean proof.

## New nodes

`lem-sc-picard-external-cech-cup-bidegree` records the proved k-linear construction on
one tensor summand, in `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree`. It
contains the summand-coordinate predicate and the existence theorem; it asserts no
differential compatibility.

`lem-sc-picard-external-cech-cup-differential` records the adjacent signed differential
calculation for a given family of summand maps, in
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential`. The module's degree-map
construction and inclusion theorem are proved, while its commutation theorem is the
one remaining sorry. Both nodes inherit the item's chapter and unit and carry source,
search, and complete natural-language proof records. No change record is needed:
all existing public signatures and visibility are unchanged.

## Second reading by R4

1. Compared the existing component module with the repository using diff: only a
   plain proof import and the body of picardExternalCechCupComponent_exists changed.
   Both existing declaration signatures and the coordinate definition are byte for
   byte unchanged. The existing node differs only in proof, proof_deps and
   proof_origin. No interface correction or change record is required. Verdict: pass.
2. Read all three delivered modules and compiled them in import order. The only
   textual hole is picardExternalCechCupDegreeMaps_comm, exactly the named theorem
   reported above. No forbidden declaration or hollow definition occurs. The chosen
   scalar coefficient is determined pointwise by exists_scalarPullbackCoefficient
   and by the adjunction homEquiv, hence is not an arbitrary existence witness.
   Scratch #print axioms checks and the delivery probe verify the allowed axiom set,
   permitting sorryAx only through the reported differential hole. Verdict: pass.
3. Read the two new nodes and the differential theorem's source and docstring.
   The remaining identity assumes specified bilinear maps, so it is strictly the
   differential step, not a restatement of cochain-map existence. Pure tensors
   determine each map and categorical Cech products detect equality. In degree
   p=q=0 the extra front term and first back term cancel, leaving the two expected
   restrictions; empty families and zero coefficients give zero maps. Repeated
   indices and characteristic two do not change the alternating-sum argument.
   Independent LeanFinder search for the Leibniz rule of an Alexander--Whitney
   alternating coface product found alternating differential formulas only; Loogle
   found mapBifunctor.d₁_eq and d₂_eq, not this identity. A separate Mathlib grep
   search confirmed the tensor-total inclusion formulas. Project rg found the proved
   cechCupCochain_leibniz: it uses one scheme, one cover and global-section scalars,
   so external pullback/refinement and scalar transport remain necessary. There is
   no direct replacement that closes this hole in a few minutes. Verdict: pass.
4. The proof first constructs bilinear summands from existing proved scalar maps
   and universal properties, then uses the one remaining signed differential
   identity. Every import is needed by signatures or that proof. All three old
   proof dependencies remain used transitively in the new bidegree and differential
   nodes: def-sc-picard-external-right-cech-models, def-sc-cech-cup-product, and
   lem-pc-module-pullback-adjunction. None is no longer needed. The unit
   sk-prop-av-cube has empty realized statement and step lists in this checkout;
   its statement and route are unchanged. Verdict: pass.
5. Checked each node against its module, declaration and verbatim theorem
   signature. Each proof_deps equals the union of proof-step uses; the new nodes
   contain source, search, creation, blueprint, chapter, unit and Lean records.
   The existing node records precisely bidegree construction followed by total
   assembly and the differential step. Verdict: pass.

Second reading changed only this report, adding the independent review and
clarifying that the old dependencies remain necessary transitively. No Lean or
node repair was needed. This is one original hole closed and one strictly smaller
hole added, a decomposition with net zero, not an axiom-free completion.
