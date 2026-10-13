## What changed

Replaced the sorry in
`AlgebraicGeometry.canonicalDerivedTensorHomMap_bijective` without changing its
signature or its definitions. The proof constructs localization equivalences using
K-injective targets, proves the localized tensor comparison invertible on K-flat
inputs using the upstream derived-monoidal criterion, and compares the normalized
maps on chain representatives by total-tensor summand extensionality. It then
chooses K-flat representatives for both inputs and transports bijectivity using the
assumed naturality and isomorphisms of Hom sets.

Added `Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom`, containing the strictly
chain-level missing step: a component-normalized equivalence on homotopy classes.
It concerns arbitrary complexes, assumes neither flatness nor injectivity, and
mentions neither a derived category nor a natural family t. The main proof imports
it privately. Updated the item's proof plan and dependencies to follow this proof.

The first worker recorded a 55.3-second item compile. The second reader
repaired a later local timeout: a private definitional component comparison and
a short localization calculation keep the same proof, and the repaired full
module compiled in 54.4 seconds with no warnings. The delivered set is checked
again by `lcompile.py --all` and the delivery gate below. The missing model artifact initially
blocked compilation, then became available in the shared build refresh. Separate
scratch checks compiled the localization and tensor-model helpers before the refresh.
No source-library module or existing interface was changed.

## Proved and sorry left

Closed the item hole in
`AlgebraicGeometry.canonicalDerivedTensorHomMap_bijective`
(node `lem-pc-canonical-derived-tensor-hom-map-bijective`) by a complete Lean
reduction to the existing localization/K-flat lemmas and the new chain-level lemma.

Added one hole:
`AlgebraicGeometry.exists_normalizedHomotopyTensorHom`
(node `lem-pc-normalized-homotopy-tensor-hom`). Its entire proof is `by sorry`,
with a source and a complete natural-language proof in its docstring and node.
This is a decomposition: one upper hole closed, one strictly lower hole added,
not a claim of an axiom-clean completed proof of the derived tensor-Hom theorem.
There are no other sorries in either delivered module and no new data is chosen
from a mere-existence theorem. The equivalence chosen in the main proof is only
used within a theorem proof, to establish bijectivity of the already given map.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.Algebra.Homology.HomTensorDifferential`.
- `Sheaf.Algebra.Homology.HomTensorNaturality`.
- `Sheaf.Algebra.Homology.HomComplexGlobalCochains`.

The differential and global-cochain comparisons are needed only by the new
chain-level node, whose module imports them. Their nodes
`lem-sc-hom-tensor-differential` and `lem-pur-hom-complex-global-cochains`, together
with `lem-sc-hom-tensor-degreewise`, are now dependencies of that node rather
than direct proof dependencies of the item.

The chain-level naturality lemma `lem-sc-hom-tensor-naturality` and its module
`Sheaf.Algebra.Homology.HomTensorNaturality` are not used by this argument:
transport uses the naturality already assumed in `IsCanonicalDerivedTensorHomMap`.
This is removal of a direct proof import, not global pruning:
`KInjectiveHomComplex` still privately imports `HomTensorTotal`, which uses
`HomTensorNaturality`. No module is claimed removed from the targets' import
closure. No blueprint unit statement or realized proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's localization and naturality argument works as stated. The library had
no theorem supplying the normalized equivalence on homotopy classes, despite
having degreewise tensor-Hom isomorphisms and the global-cochain comparison.
The new node isolates exactly that glue; it does not restate the derived theorem.
Its edge cases are sound: zero inputs give singleton Hom sets, and unbounded
complexes use products in Hom and coproducts in total tensor.

Stacks Tag 0A90 is `sites-cohomology.tex`, `lemma-compose`; its proof is omitted
with a reference to the module calculation. The explicit quotient and component
argument in the new docstring elaborates that source. The second reader corrected
it to retain the component formula of the global-cochain construction: the bare
existential global-cochain theorem does not specify that formula.
LeanSearch was unavailable; LeanFinder, Loogle, Mathlib source grep, and searches
in both library roots found no matching normalized homotopy-class theorem.

## New nodes

`lem-pc-normalized-homotopy-tensor-hom`, in
`dag/nodes/sec-picard-framework/lem-pc-normalized-homotopy-tensor-hom.json`, records
`AlgebraicGeometry.exists_normalizedHomotopyTensorHom` in the new module
`Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom`. It states the normalized
chain-level tensor-Hom equivalence and its equation for every chain representative.
Its proof uses the existing degreewise comparison, differential compatibility,
global-cochain construction, chosen product-projection specification
(`lem-sc-hom-complex-projections`) and sheaf tensor-Hom adjunction. There are no change
records because existing signatures and definitions are unchanged.

## Second reading by H1

1. **Interfaces:** compared the complete item module and its node with the
   repository versions. The existing theorem signature is byte-for-byte identical;
   no existing definition, visibility, target or other module was changed. Only
   proof imports, private proof helpers and the theorem body differ. There are no
   interface change records because no existing interface changed.
2. **Proof and trust:** read all private helpers and both delivered theorem bodies.
   The sole new hole is `AlgebraicGeometry.exists_normalizedHomotopyTensorHom`,
   whose entire proof is `by sorry`; there is no sorry in data, no new axiom,
   unsafe declaration, opaque declaration, external implementation or kernel bypass.
   `localizedHomEquiv` chooses an inverse to a specified bijection, so its data
   are determined; the chain-level equivalence is only eliminated inside a
   proposition proof. Compilation and axiom-check results are recorded below.
3. **New statement:** read Stacks `sites-cohomology.tex`, `lemma-compose` (0A90)
   and `equation-global-cohomology-hom-complex` (0A8Z), together with
   `HomTensorDegreewise`, `HomTensorDifferential`, `HomComplexGlobalCochains` and
   the source sheaf `tensorHomEquiv`. The arbitrary complexes P,L,I, the quotient
   q, tensor order P then L, indices p+r=n and r+p=n, symmetry before inverse
   adjunction, and equation on every chain representative match the node and
   source construction. For complexes concentrated in p and r the equation is
   ordinary sheaf tensor-Hom uncurrying, with no degree-zero sign; zero inputs
   give singleton Hom sets. For general complexes the differential calculation
   has signs -(-1)^n on the P term and -(-1)^(p+n) on the L term; these agree with
   the total-tensor differential. Products and coproducts handle unbounded inputs.
   Passing degree-zero cocycles modulo degree-minus-one boundaries is strictly
   below the derived theorem: this statement has no derived category, K-flat
   hypothesis, K-injective hypothesis or natural family t. Independent Loogle
   search `HomotopyCategory, _ ≃ _` found no match. LeanFinder's alternative
   cocycle/boundary query found Mathlib `CohomologyClass.homAddEquiv`, which
   supplies the generic quotient identification but no normalized sheaf comparison.
   Source grep found the upstream homotopy tensor-Hom adjunction; its internal-Hom
   differential is (-1)^p times a different formula, so it needs a component and
   sign comparison to the present `homComplex`. No direct replacement was found.
4. **Reduction and pruning:** localization is used only into the two K-injective
   targets. The K-flat tensor criterion is established from the upstream
   derived-monoidal lemma. The normalizations of ht and e imply equality of the
   two chain maps by total-tensor summand extensionality. The src/dst Hom
   equivalences then give representative bijectivity, and ht's assumed naturality
   transports it along the displayed K-flat resolution isomorphisms. Reviewed
   every old proof dependency: degreewise, differential and global-cochain work
   move to the new node; chain naturality is not needed directly by this argument.
   Its module remains reached through `KInjectiveHomComplex`/`HomTensorTotal`,
   so there is no claim of global module pruning. Read
   `dag/units/sk-thm-picard-duality.json`: its existing realized statement and step
   arrays are empty, and neither delivery node occurs there. This local reduction
   changes no recorded unit realization or unit/chapter route.
5. **DAG:** the item's proof and dependency list describe the actual localization,
   summand-extensionality and naturality argument. The new node has the same
   chapter/unit, source, self-contained statement, declaration record, provenance,
   searches and blueprint ancestry required by the brief. Its proof dependencies
   are exactly its recorded uses. Repaired its proof plan to specify the normalized
   global-cochain construction, with the chosen product-projection node added.

Changes by this reader: repaired the new theorem's written proof and DAG plan,
which previously treated an arbitrary existential global-cochain equivalence as
if it supplied a component formula. The corrected argument constructs that
comparison from the specified projections, as the existing global-cochain proof
does. Added the private proof import `HomComplexProjections` and the new module's
missing blueprint tag. Corrected the pruning report to distinguish direct-import
removal from global pruning. Existing Lean statements are unchanged. Added the private `uncurryComponent_eq`
theorem (proved by `rfl`) to make the existing component/projection conversion
explicit, and replaced the broad normalization rewrite with src/dst equations
and a short `calc`. This repairs the expensive unfolding without moving work
out of the module or adding holes; the entire module is checked within the same
60-second file limit.

Validation: the delivered modules compiled together with `lcompile.py --all`:
5.4 seconds for the chain-level module and 54.6 seconds for the item, with no
warnings. An import-only scratch module printed the axioms of both public
declarations from these compiled artifacts: exactly `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx`. This confirms the stated decomposition; it does not
claim an axiom-clean completed theorem. The delivery gate attempts an additional probe of every private and public
declaration. The dry run printed OK (commit c689e7486a), with review class CODEX.
Its full item probe hit the 60-second limit; the tool explicitly deferred that
probe to the merge. The independent `#print axioms` check above reads the compiled
item declaration and therefore checks the transitive axiom footprint of all four
private helpers it uses (`uncurryComponent_eq`, `localizedHomEquiv`,
`localizedHomEquiv_map`, `tensorModelMap_isIso`). There are no unused private
helpers or other uninspected declarations. The chain-level module's gate probe
did run successfully.
