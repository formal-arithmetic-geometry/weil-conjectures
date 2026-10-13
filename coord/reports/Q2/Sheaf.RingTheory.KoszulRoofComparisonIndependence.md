## What changed
Proved `ExteriorAlgebra.koszul_roof_comparison_independent` without changing its
signature, definitions, or original public imports. Added two proved auxiliary
modules with proof-only imports in the item:
- `Sheaf.RingTheory.KoszulGeneratorChainMap`: exterior powers of the generator
  substitution form a chain map; its integer extension commutes with both
  normalized augmentations and has the required top component.
- `Sheaf.RingTheory.KoszulDerivedTopEvaluation`: K-projectivity reflects derived
  equality to a homotopy, whose top contribution has values in the generated ideal.
The item constructs the substitution, cancels the shift and augmentations,
and proves the final determinant comparison using conormal surjectivity,
change of conormal vectors, and pairing injectivity. The local linear-algebra
helpers reuse the proved arguments of the downstream
`KoszulRegularSequenceDualComplex`, which cannot be imported without a cycle.
Updated the parent DAG proof and added nodes for the two proved auxiliary results.

Returned-delivery repair: removed the duplicate private `boundary_wedge` from
`KoszulDerivedTopEvaluation`. Its proof-only import of `KoszulGeneratorChainMap`
now supplies the existing helper, made public in that new auxiliary module.
The helper’s binders and statement are unchanged; its proof is kept only once.
Updated the evaluation node to record this shared contraction dependency.

## Proved and sorry left
Closed the item's sole hole, `ExteriorAlgebra.koszul_roof_comparison_independent`
(node `lem-sc-koszul-roof-comparison-independence`). No holes were added or split off.
Both new public theorems are proved:
`ExteriorAlgebra.exists_koszul_generator_chain_map`
(node `new-q2-koszul-generator-chain-map`) and
`ExteriorAlgebra.koszul_derived_top_evaluation_eq`
(node `new-q2-koszul-derived-top-evaluation`). The shared public `ExteriorAlgebra.boundary_wedge` and all private helpers are proved.
The three modules compile together without errors or warnings.
`#print axioms` for all three public theorems reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Rank zero is handled explicitly by the zero source term in degree 1; the
construction works for the zero quotient and does not invert the generator matrix.

## No longer needed
No original imports were removed: the public import interface is preserved.
The duplicate evaluation-module proof of `ExteriorAlgebra.boundary_wedge` is
removed; the chain-map module supplies the single shared theorem.
The proof does not need these planned proof dependencies:
- `new-j3-koszul-projective-resolution` / `Sheaf.RingTheory.KoszulProjectiveResolution`:
  natural terms are directly projective by their exterior bases; no resolution is chosen.
- `lem-sc-hom-cocycle-homotopy-quotient-formulas`: direct `Homotopy.comm`
  replaces conversion to cocycles and quotient-class arithmetic.
- `lem-sc-hom-single-cocycle-component-formulas`: the component is extracted
  directly from the homotopy and `extend_d_eq`.
The K-projectivity, map-reflection, finite-exterior-basis, and complex nodes remain
needed through the new auxiliary nodes. The old proof dependency `def-sc-koszul-dual-complex` /
`Sheaf.RingTheory.KoszulDualComplex` is no longer a proof step; it remains a
statement dependency through `KoszulConormalComparison`. No globally unreachable module is claimed: other targets
may still need these nodes.

## Where the brief, the DAG or earlier work was wrong
The landing import-pruning check correctly rejected the duplicated
`ExteriorAlgebra.boundary_wedge` proof in the evaluation module. This repair
imports and uses the chain-map module’s theorem instead. No statement error was found. The planned HomComplex cocycle route was unnecessary;
Mathlib's homotopy equation gives the needed boundary directly. The conormal-basis
and downstream comparison arguments are already proved and can be reused locally.
LeanSearch was unavailable; LeanFinder, Loogle and source searches were recorded.
The unit route is unchanged (`sk-thm-picard-duality` has no realized nodes here).

## New nodes
`new-q2-koszul-generator-chain-map` is the proved generator-substitution chain-map
step, in `Sheaf.RingTheory.KoszulGeneratorChainMap`. It assumes neither regularity
nor a derived roof equality, and is strictly the first part of the argument.

`new-q2-koszul-derived-top-evaluation` is the proved same-source homotopy-invariance
step, in `Sheaf.RingTheory.KoszulDerivedTopEvaluation`. It assumes no conormal
comparisons or augmentations, and concludes only equality of scalar evaluations
modulo the ideal. No change record or forced adaptation is needed.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: pass.** Read the repository version and the full diff of
   `KoszulRoofComparisonIndependence.lean`. The existing theorem signature,
   including both regularity assumptions, both normalized comparisons, the
   augmentation formulas, quasi-isomorphism instances, the shift in the roof
   equality, and the determinant-valued conclusion, is byte for byte unchanged.
   No existing definition, public import, or other module was changed. The two
   auxiliary modules add proved theorems, not replacement definitions. The
   existing parent node differs only in `proof`, `proof_deps`, and `proof_origin`.
2. **Proof and axioms: pass.** Compiled all three modules in import order with
   `lcompile.py`. No errors or warnings. Scanned every delivered Lean file:
   no sorry, axiom, unsafe, opaque, implemented_by, extern, or sorryAx tokens;
   all lines meet the width requirement. Scratch copies with `#print axioms`
   of the three public theorems show only `propext`, `Classical.choice`, and
   `Quot.sound`. The delivery tool also probes every declaration, including
   private helpers. Coefficient vectors are chosen from a theorem proved here
   by membership in the range of linearCombination; no object is chosen from
   an unproved mere existence statement.
3. **Auxiliary statements: pass; no split-off holes.** Read both auxiliary Lean
   files and their nodes. The generator theorem requires only the functional
   equation for t and normalization of augmentations. Its proof constructs
   exterior powers, verifies contraction on wedges, extends the map, checks
   degree zero, and identifies degree -r. The evaluation theorem requires
   only span(range f)=I and equality of Q-maps; free terms give K-projectivity,
   Qh injectivity gives an actual homotopy, and its component equation reduces
   the difference to contraction with coefficients in I. In rank zero the
   degree-one term vanishes; in rank one contraction is multiplication by f_0;
   for I=A reduction is zero. Singular t is allowed, with no determinant
   inverse. These are strictly separate portions of the argument, and both
   are proved. Independent Loogle search for contractLeft and LeanFinder
   searches for functorial exterior contraction and derived equality versus
   homotopy found generic map/homotopy APIs, not either specialized theorem.
   Source searches in lean/Sheaf, lean/WeilConjectures and the pinned Mathlib
   exterior-power and K-projective modules found no shorter matching route.
   Search services mention bijective_pairingDual in a newer Mathlib; rg confirms
   that it is absent from the pinned local Mathlib, so it cannot replace the
   basis argument here. Read Stacks Tags
   [0BQY](https://stacks.math.columbia.edu/tag/0BQY) and
   [0BQZ](https://stacks.math.columbia.edu/tag/0BQZ): the local Koszul/Ext
   computations are the source context; the explicit comparison and homotopy
   glue is correctly identified in the nodes as an argument written by Q2.
4. **Top-down route and pruning: pass after report repair.** The parent first
   constructs the substitution from the common ideal, cancels the shift and
   augmentations, applies the same-source evaluation result, and finally
   compares normalized values on lifts of arbitrary conormal wedges. Pairing
   injectivity follows from the conormal basis, rather than assuming the desired
   comparison. The local conormal and pairing helpers match proved downstream
   arguments; importing that downstream module would create a cycle. All added
   parent imports are proof-only; the auxiliary public imports supply objects
   in their signatures. Tested removing Dual.Basis: compilation fails at
   b.dualBasis, so restored it. Existing public reexports remain intact. Checked
   every old proof dependency: three are bypassed entirely; the signed dual
   complex remains only in the signature dependency chain; K-projectivity,
   derived-map reflection, exterior bases, and the Koszul complex remain through
   the new auxiliary nodes. Added the missing explicit signed-dual node entry to
   No longer needed. The unit sk-thm-picard-duality has empty realized statement
   and step lists; none is bypassed or changed. No globally pruned module is
   claimed without an import-closure calculation.
5. **DAG agreement: pass.** All three node lean.statement strings equal the
   corresponding Lean signatures exactly. Each proof_deps set is the union of
   its proof steps' uses. The parent records precisely substitution, cancellation,
   top evaluation, and conormal normalization; the new nodes record the
   contraction, extension, K-projectivity, homotopy, and ideal calculations
   actually present. Both new nodes have source, proof_origin, three search kinds,
   creation provenance, chapter/unit, blueprint ancestry, and complete lean
   records. They leave no open statements.

Second-reader changes: completed the pruning report with the old signed-dual
proof dependency and recorded the concrete independent review above. No proof
repair was necessary; the attempted import removal was reverted after checking.

## Second reading by Q2

1. **Visible interface: pass.** Compared the current item with the repository by
   `diff -u` and checked its signature byte for byte. The original declaration,
   regularity and generation hypotheses, normalized comparisons, augmentations,
   quasi-isomorphism instances, derived roof equality and conclusion are unchanged.
   Only proof imports, proved private helpers and the proof body were added.
   The two auxiliary modules are new; no existing module besides the item is
   delivered. The existing node changes only proof, proof_deps and proof_origin.
2. **Proof: pass.** Read all three modules and compiled them in import order through
   lcompile.py. Scratch copies of the current files print axioms for boundary_wedge,
   exists_koszul_generator_chain_map, koszul_derived_top_evaluation_eq and
   koszul_roof_comparison_independent: each uses exactly propext, Classical.choice
   and Quot.sound. No forbidden declaration, sorry token or over-width line occurs
   in the delivered Lean files. The coefficients are chosen from a proved range
   calculation; no arbitrary data is chosen from an unproved existence theorem.
3. **Auxiliary results: pass; zero split-off holes.** Read the new nodes against
   their Lean signatures. Substitution is exteriorPower.map, with its differential
   compatibility proved on wedges using the functional equation ht. Degree-zero
   naturality and the zero terms of the target prove augmentation compatibility.
   The evaluation proof obtains projectivity from exterior bases, reflects derived
   equality with Qh_map_bijective, and applies Homotopy.comm. In rank zero the
   source degree-one term is zero; in rank one the boundary is f_0 times the scalar
   coefficient, which lies in I. For I=A quotient evaluations vanish. Singular t
   is allowed throughout. These are proved parts of the argument, not renamings
   of the parent. Independent Loogle pairingDual and LeanFinder substitution and
   bounded-above-projective/homotopy searches found generic APIs but no matching
   specialized theorem. Source searches found only private top-boundary formulas
   and downstream private conormal helpers. The newer online bijective_pairingDual
   is absent from the pinned Mathlib. Read Stacks Tags
   [0BQY](https://stacks.math.columbia.edu/tag/0BQY) and
   [0BQZ](https://stacks.math.columbia.edu/tag/0BQZ): these provide the local
   Koszul/Ext source context; the explicit comparison glue is Q2's argument,
   as proof_origin records.
4. **Route and pruning: pass.** The proof constructs t and U, cancels the common
   shift and augmentations, applies top evaluation, then uses conormal lifts and
   pairing injectivity to compare the normalized values. Every new parent import
   is proof-only. Each auxiliary public import supplies objects in its signatures;
   K-projectivity, exterior bases and projectivity imports used only in proofs are
   plain imports. The current repair correctly shares boundary_wedge rather than
   duplicating it in evaluation. The downstream helpers cannot be imported because
   their module imports this item. Checked all old proof_deps against the new
   transitive route: the resolution and two cocycle-formula nodes are bypassed;
   the signed dual remains a statement dependency; the other old nodes remain
   directly or through auxiliaries. No longer needed records these distinctions.
   The unit sk-thm-picard-duality has no realized statement or step nodes here,
   and its route is unchanged. No globally pruned module is claimed.
5. **Nodes: pass.** All three lean.statement fields occur verbatim in their modules,
   each proof_deps equals the union of the steps' uses, and the steps match the
   actual constructions and calculations. The evaluation node explicitly records
   its shared contraction dependency on the chain-map module. The new nodes have
   sources, proof origins, search records, creation provenance, blueprint ancestry,
   chapter/unit and complete Lean records. No change record is required.

This reading repaired documentation only: added the missing module blueprint tags
and a complete proof description and blueprint tag for the newly public shared
boundary_wedge helper. Proofs, signatures, imports and DAG data required no further
repair. The sole original hole is closed and no holes are added.
