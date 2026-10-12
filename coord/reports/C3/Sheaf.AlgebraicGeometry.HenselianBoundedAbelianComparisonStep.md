## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep`
with the complete successor-degree diagram chase. The declaration's signature and its two
public imports are unchanged. The proof effaces source classes using the identity closed
immersion and fibre classes using the quotient immersion. It constructs the cokernel short
exact sequence, proves the cokernel remains killed by the same n by epimorphism cancellation,
and uses the proved `pullbackCohomology_longExact_ladder`. Injectivity lifts a fibre preimage
through preceding-degree comparison for G' and then uses comparison injectivity for Q.
Surjectivity lifts a boundary representative through preceding-degree comparison for Q.
No higher-degree comparison or general Gabber effacement is imported.

Added `Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement`, with a complete proof reducing
bounded abelian effacement to the constructible finite-module case. It uses the already
proved canonical module lift, represents the class by a constructible module sheaf,
transports the representing equation through the natural pullback/forgetful isomorphism,
and constructs a module-valued pushout. Its underlying map is monic because forgetting
preserves finite limits. The pushout equation proves the killing equation. The exponent
condition is proved sectionwise using n = 0 in ULift(ZMod n).

Added `Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement` for the remaining
constructible finite-module step of Stacks 09ZE. It is strictly smaller than the original
successor comparison: it has no henselian or predecessor comparison hypothesis and no
comparison conclusion; only constructible coefficients are considered. The arbitrary
coefficient and pushout steps, and both long-exact-sequence chases, have been written in Lean.
Updated the original node's proof route and supplied a node for each new public theorem.

All three files compile together under `lcompile.py --all` without warnings. Each is below
the 60-second file limit. The two generic-effacement construction steps rely on theorem
witnesses only inside proofs; no new definition or arbitrary data choice was introduced.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.bijective_cohomologyMap_succ_of_henselianRing_of_nsmul_eq_zero`
(node `lem-weil-pbc-henselian-bounded-abelian-comparison-step`).

Also proved the new declaration
`AlgebraicGeometry.Etale.exists_bounded_mono_closed_cohomology_eq_zero`
(node `lem-weil-pbc-bounded-abelian-closed-effacement`).

Added one hole, whose complete body is `by sorry`:
`AlgebraicGeometry.Etale.exists_constructible_module_mono_closed_cohomology_eq_zero`
(node `lem-weil-pbc-constructible-module-closed-effacement`).

This is a decomposition: one old hole closed, one strictly lower hole added, net zero holes.
The original module has no remaining `sorry`. The delivery has exactly one `sorry`.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit`
- `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass`
- `Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`
- `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective`
- `Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Mathlib.CategoryTheory.Abelian.Basic`

The old proof dependencies no longer used directly by the successor proof are:

- `lem-weil-pbc-module-sheaf-colimit-constructible`
- `lem-weil-pbc-constructible-restriction-class`
- `lem-weil-pbc-constant-module-sheaves-forget-colimits`
- `lem-weil-pbc-cohomology-filtered-colimit`
- `lem-weil-pbc-etale-module-pullback-forget-naturality`
- `lem-weil-pbc-constructible-module-finite-pushforward-embedding`
- `lemma-weil-pbc-finite-exchange`
- `lem-weil-pbc-finite-pushforward-cohomology`
- `lem-weil-pbc-integral-cover-kills-constant-cohomology`
- `lem-weil-pbc-finite-surjective-unit-mono`
- `lem-weil-pbc-finite-pushforward-unit-edge-compatibility`
- `lem-weil-pbc-abelian-pushout-mono`
- `lem-weil-pbc-cohomology-pullback-functorial`

These are retained transitively through the effacement reduction or its existing
prerequisites; none is claimed globally retired.

The original node now directly needs only bounded closed-subscheme effacement and the
long-exact ladder. The finite-coefficient construction dependencies are retained under
the new constructible-effacement node, while the constructible approximation and its
colimit dependencies are used through `exists_constructible_restriction_class`.
A source-import-graph comparison of the original item and the delivered overlay found
no modules removed from the transitive closure. Thus no globally pruned module or node
is claimed. The removed imports factor the argument; they do not retire their underlying
results. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG omitted the already proved canonical lift
`AlgebraicGeometry.exists_module_sheaf_of_nsmul_id_eq_zero`
(node `lem-weil-pbc-killed-sheaf-module-lift`); the bounded-effacement proof reuses it
instead of reconstructing scalar actions. No mathematical statement was changed or
found false.

Read Stacks Tags 09ZE and 09ZI directly. The finite-ring module specialization of 09ZE
preserves the fixed exponent because embeddings and pushouts are performed in module
sheaves. The general-coefficient effacement in Gabber depends on bounded comparison,
so using it here would have been circular. The unit `sk-thm-p1` and its realized steps
were checked; none is replaced by this finer coefficient reduction.

Edge cases: n=1 forces every coefficient module to be zero; the module lift and pushout
proof still work. The successor proof includes q=0 and uses only the degree-zero
predecessor hypothesis in that case. Zero classes, zero rings, empty spectra and empty
finite sums introduce no additional hypothesis. The new effacement statements require
q>0, which is necessary. The target and all existing statement signatures are unchanged.

Mathlib searches were run through `msearch.py`: LeanFinder found homological and section
restriction lemmas, Loogle found `Function.Exact` and its elementary consequences, and
grep found no exact effacement theorem. LeanSearch returned an internal server error;
it is recorded as unavailable, not as a failed mathematical match. Blueprint searches
for effacement, finite pushforward and closed subscheme found no statement preserving
the fixed exponent in this interface. `blueprint_refs.py ancestor` returned None for
the item despite its recorded provenance chain; the new nodes record that chain to
`lemma-weil-pbc-gabber-effacement` explicitly.

## New nodes

`lem-weil-pbc-bounded-abelian-closed-effacement`: arbitrary abelian coefficients killed
by a fixed positive n, any affine scheme and any closed immersion, and positive degree.
Its proof is complete from the canonical lift, constructible approximation and the new
constructible effacement. This node isolates the coefficient and pushout glue from the
successor comparison.

`lem-weil-pbc-constructible-module-closed-effacement`: a positive restricted class of a
constructible sheaf over a finite commutative ring can be killed by a monomorphism of
module-valued sheaves. Its sole remaining hole follows Stacks 09ZE's finite-pushforward
construction using 09Z7 and 09ZD. Its proof plan specifies the finite exchange, edge,
unit compatibility, and finite-biproduct steps. No comparison theorem is a dependency.

No statement/interface change records or forced adaptations are needed.

## Second reading by C3

1. Interface: PASS. Compared the delivered successor module with the repository by
   diff and byte-for-byte signature extraction. The existing theorem signature and
   both public imports are unchanged; only its proof and private proof imports differ.
   There are no new definitions, interface changes, or forced adaptations.
2. Proof: PASS. Read the cokernel annihilator argument, both exact-sequence chases,
   representative transport, and module pushout proof. All three modules compiled
   together without warnings (6.8, 29.8, and 25.1 seconds). Explicit scratch-copy
   `#print axioms` checks on all three public theorems show only propext,
   Classical.choice, Quot.sound, and sorryAx. The one textual sorry is the whole
   proof of the named constructible-effacement theorem. There is no forbidden
   declaration and no data definition chosen from an unproved existence theorem.
   One initial combined scratch-probe run timed out; isolated probes passed within
   the file limit. This remains a decomposition with an open dependency, not an
   axiom-free completion of the successor theorem.
3. Split statement: PASS. Read Stacks 09ZE, 09Z7(3), and 09ZD(2) independently.
   Module-linear constant units, finite pushforward and biproducts preserve the
   coefficient ring, so the stated constructible-module specialization is valid.
   Checked zero classes, zero rings, empty schemes and sums, n=1, and q=0 in the
   successor proof; effacement itself correctly requires positive degree. The new
   hole has no predecessor-comparison hypothesis or comparison conclusion and
   isolates the finite-constructible construction; it does not restate the item.
   Its source, complete proof docstring and node are present. Independent msearch
   LeanFinder, Loogle and grep searches with embedding/annihilation terminology,
   plus source searches in lean/Sheaf and lean/WeilConjectures, found no matching
   theorem. The generic module-acyclic ladder requires an additional pullback
   acyclicity hypothesis, and Gabber's general effacement depends on bounded
   comparison; neither closes this step without extra assumptions or circularity.
   Formalizing the remaining finite-base-change/biproduct construction is not a
   few-minute closure, so no further hole was introduced.
4. Route and pruning: PASS. The successor proof directly uses bounded effacement
   and the existing long-exact ladder; the coefficient reduction reuses the proved
   canonical module lift and constructible restriction theorem. Proof-only imports
   stay private. Imports in the open module document its specific proof plan.
   Checked sk-thm-p1.json realized statement and all realized steps: none is
   bypassed by this reduction below the unit level. No transitive module pruning
   is claimed. Completed the report's explicit list of old proof dependencies
   no longer used directly, distinguishing them from globally retired nodes.
5. Records: PASS. Existing node changes are exactly proof, proof_deps and
   proof_origin. For all three nodes checked that proof_deps is the union of the
   steps' uses and that lean.statement matches the delivered signature verbatim.
   The two new nodes have source, self-contained statement, searches, provenance,
   created record, chapter/unit and Lean records. Their proof plans agree with
   the completed reduction and the remaining open construction respectively.

Second reading changed only report.md: added the complete old-dependency list and
this independent review. The Lean proofs and statements needed no repair.
