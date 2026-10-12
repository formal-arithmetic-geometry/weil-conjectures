## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_isConstructibleSheaf_hom_of_henselianRing`
by a complete proof from the existing `exists_constructible_restriction_class` and
`finite_locally_constant_module_values_iff` interfaces. The proof transports the class through
one natural inverse-image/forgetful comparison, obtains a constructible representative,
converts its finite-value stratification to the source-library predicate, and uses naturality
and the inverse identity to prove the required equality.

Added the proof-only imports `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass`,
`Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues`, and
`Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`. All original public imports,
definitions and declaration signatures are retained. Updated the approximation node's proof
and dependencies to record this argument; its statement is unchanged.

Added `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`, whose single public theorem
`AlgebraicGeometry.Etale.exists_upperStar_forget₂_natIso` is fully proved. It composes Mathlib's
sheafification and left-Kan-extension natural comparisons; no new sorry is introduced.
The existing objectwise theorem `pullback_forget_modules_iso` was inspected: an independent
choice of its isomorphism for each object does not supply naturality at the chosen C→F.
The new interface exposes precisely that additional coherence, with a complete proof.

Both delivered modules compile together without warnings through lcompile.py (about 4 seconds
for the naturality module and 22 seconds for Gabber). The supplied induction proof of the main
comparison theorem continues to compile. No library-wide build was run.

## Proved and sorry left

Closed 1 of the 5 original sorries:
`AlgebraicGeometry.Etale.exists_isConstructibleSheaf_hom_of_henselianRing`
(node `lemma-weil-pbc-constructible-approximation`). This proof still depends on existing named
statement modules, notably `Scheme.exists_filtered_colimit_constructible`,
`Etale.restrictedCohomology_isColimit`, and `Scheme.finite_locally_constant_module_values_iff`.
Their remaining proofs are separate items, as intended in stage 3.

Also proved `AlgebraicGeometry.Etale.exists_upperStar_forget₂_natIso`
(node `lem-weil-pbc-etale-module-pullback-forget-naturality`). It has no sorry and uses the
ordinary Mathlib comparison constructions.

The four original sorries left unchanged in Gabber are:

- `AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_of_henselianRing`.
  This is the affine abelian H⁰ input of `prop-weil-pbc-gabber-pair-comparison`;
  the existing `lemma-weil-pbc-etale-degree-zero` record points to the proper module-section
  theorem, not to this abelian-cohomology declaration. Its separate attachment is missing.
- `AlgebraicGeometry.Etale.exists_cohomologyMap_eq_zero_of_isLimit`
  (node `lemma-weil-pbc-finite-stage-killing`).
- `AlgebraicGeometry.Etale.exists_isFinite_cohomologyMap_eq_zero_of_henselianRing`
  (node `lemma-weil-pbc-finite-cover-killing`).
- `AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing`
  (node `lemma-weil-pbc-gabber-effacement`).

No sorry is split off or added. The main theorem
`AlgebraicGeometry.Etale.bijective_cohomologyMap_of_henselianRing` was already proved by
induction and is preserved; it still rests on degree-zero restriction and effacement.

## No longer needed

No original import is removed, and no node or module is claimed globally pruned.
The approximation proof reuses the constructible-restriction-class theorem rather than
rebuilding filtered diagrams, colimit cocones, and extraction of representatives in Gabber.
Those ingredients remain needed through that theorem, so they are not listed as eliminated.
The objectwise `Sheaf.AlgebraicGeometry.EtalePullbackForgetModules` comparison need not be
imported here: the complete natural comparison is proved directly from the generic Mathlib
constructions. The unrelated existing finite-cover and finite-stage declarations are retained.

## Where the brief, the DAG or earlier work was wrong

The approximation node has two natural-language clauses (torsion abelian sheaves and finite
coefficient module sheaves), but the attached Gabber declaration formalizes only the finite
coefficient clause. This delivery proves that declaration unchanged; it does not assert that
the unrepresented torsion-abelian clause has now been formalized. Its original argument is
retained in the node after the updated finite-ring argument.

The existing pullback/forgetting node exposes only objectwise existence in Lean, although its
proof describes natural Mathlib constructions. Objectwise existence cannot justify the
naturality square used for class representatives. The new, fully proved naturality node
makes this missing interface explicit. No change to an existing signature is necessary.

The existing continuity statement `cohomology_continuity_of_isLimit` assumes torsion and thus
cannot directly prove Gabber's finite-stage auxiliary theorem, which has arbitrary abelian
coefficients. The finite-cover sketch also does not state the existence of the integral
killing cover as a dependency; the reviewed effacement route instead follows Stacks 09ZE.
These auxiliary sorries are left untouched rather than silently inserting those hypotheses.

For degree zero, the existing proper henselian theorem concerns module global sections.
Transferring it to abelian Ext cohomology needs coefficient/adjunction compatibility as well
as the degree-zero identification. The original sorry is retained.

The local checkout does not contain the Stacks .tex bodies. The relevant source statements
were checked on the official pages [03D3](https://stacks.math.columbia.edu/tag/03D3),
[03D7](https://stacks.math.columbia.edu/tag/03D7), and
[09ZE](https://stacks.math.columbia.edu/tag/09ZE); the new proof itself is complete Lean from
Mathlib. Tag 03D6 is a definition of ringed-topos pullback, not an abelian inverse-image lemma;
the new module uses the correct module adjunction tags instead.

## New nodes

`lem-weil-pbc-etale-module-pullback-forget-naturality` records the single natural isomorphism
between module pullback followed by forgetting and forgetting followed by abelian pullback.
Its module is `lean/Sheaf/AlgebraicGeometry/EtaleModulePullbackForgetNaturality.lean`, and its
proof is complete. Identity maps, empty schemes, zero coefficient rings, arbitrary coefficient
rings and degree zero require no extra hypotheses. The proof does not use henselianity,
torsion or constructibility. Searches of the DAG and blueprint found the existing objectwise
comparison but no interface supplying this functor naturality. Actual Mathlib search logs are
in the sandbox; LeanSearch was unavailable, while Loogle/LeanFinder and grep identified the
generic ingredients. The unit route is retained; this is a coefficient-comparison tool below
the unit, not a replacement for any unit step. No change record is needed.

## Second reading by U1

1. **Unchanged visible statements.** Compared the delivered Gabber module and existing node
with the repository versions. Existing declaration signatures and definitions are unchanged;
the approximation proof only replaces its `sorry`. The new theorem is recorded by its new DAG
node and does not alter an existing declaration.

2. **Proof validity.** Compiled both delivered modules with `lcompile.py --all`. The files have
no undeclared `sorry` beyond the four named Gabber obligations retained in the report, and no
axiom, unsafe, opaque, extern, or implemented_by declarations. The new naturality theorem is a
complete construction from Mathlib comparisons; the approximation proof typechecks and uses its
natural square. The remaining sorries retain their named source and blueprint documentation.

3. **Split statements and nodes.** The naturality interface is a genuine intermediate result,
strictly weaker than Gabber and required to transport the coefficient comparison. Its statement
has no extra finiteness, torsion, or henselian hypotheses and is recorded in
`lem-weil-pbc-etale-module-pullback-forget-naturality.json`; searches found no duplicate in the
library or Mathlib. No other statement was split off.

4. **Route and pruning.** The proof follows the existing constructible-restriction route and
retains the unit route. The old colimit implementation is replaced by the already-proved
constructible restriction class theorem, with the naturality and finite-value criteria added as
dependencies. No additional import or node can be removed without losing a used declaration;
the report's `No longer needed` section records that conclusion.

5. **DAG agreement.** The approximation node's proof, dependencies, and origin now match the
Lean proof. The new node has the required statement, source, proof steps, searches, Lean record,
chapter, unit, and split status. The unit's realized route is unchanged.

I changed only the approximation proof, added the proof-only imports it uses, added the complete
module-level naturality interface and node, and documented this second reading.
