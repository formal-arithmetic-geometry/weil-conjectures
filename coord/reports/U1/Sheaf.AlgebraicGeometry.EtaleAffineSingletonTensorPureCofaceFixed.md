## What changed

Proved the body of AlgebraicGeometry.Scheme.singletonTensorDegreeComparison_pure_coface_fixed without changing its signature or visibility. A private, fully proved amitsurMap_tprod helper expands an indexed pure tensor as a product of single-factor inclusions, maps each factor using amitsurMap_comp_singleAlgHom, and proves that the coface inserts one. The public proof lifts this calculation to the coefficient tensor module and ULift, rewrites the Amitsur-side argument, then applies the geometric normalized Čech coface lemma with he n and he (n+1).

Added Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface, containing only the remaining geometric step. This step permits arbitrary normalized homomorphisms in the two relevant degrees, needs no invertibility or family of degree isomorphisms, and does not assert or use the Amitsur coface's tensor action. Its docstring gives the complete singleton evaluation, semilinearity, projection, restriction-composition, and inserted-unit proof. It is a strictly geometric part of the original argument; the algebraic part is proved in this delivery.

## Proved and sorry left

Closed the original hole: AlgebraicGeometry.Scheme.singletonTensorDegreeComparison_pure_coface_fixed (new-etale-affine-singleton-tensor-pure-coface-fixed). The item's module has no sorry. The private amitsurMap_tprod helper is fully proved.

Added one hole: AlgebraicGeometry.Scheme.singletonTensorCech_normalized_coface (lem-sc-singleton-tensor-cech-normalized-coface), in its own new module. This is a decomposition, with one upper hole closed and one geometric hole added; it is not a claim of net sorry reduction or axiom-free closure.

Both delivered modules compile cleanly through lcompile.py. No definitions, existing public imports, target signatures, or axioms were changed. Edge cases checked in the geometric argument: n=0, j at either boundary, zero coefficients, and empty W; only ring maps, section restrictions, and singleton-product evaluation are used.

## No longer needed

Removed the redundant proof-only imports Sheaf.AlgebraicGeometry.EtaleTensorSections and WeilConjectures.RingTheory.FaithfullyFlat.Amitsur from the item. Their definitions remain available through the unchanged public DegreeComparison import; this is import cleanup, not pruning those foundational modules from the whole target closure.

The item's former proof dependency new-etale-affine-singleton-tensor-pure-cofaces, module Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorPureCofaces, is not needed by this proof. It is an upper consumer of this item, so it remains needed elsewhere. No whole module is claimed to have left the targets' closure. The newly added Mathlib.Algebra.BigOperators.Pi import supplies univ_prod_mulSingle. The new geometric module is the only added proof-dependency module.

## Where the brief, the DAG or earlier work was wrong

The original fixed-degree node's proof_deps points to new-etale-affine-singleton-tensor-pure-cofaces, but its Lean theorem directly applies the fixed-degree theorem being proved here. Importing that recorded dependency would create a cycle. The delivered node replaces this circular proof edge with the actual geometric dependency and records the completed algebraic steps.

The unit sk-prop-h2 has empty realized statement and step lists. This delivery changes no unit or chapter route and keeps the singleton Čech/Amitsur calculation of the existing source route. The referenced blueprint source file is absent on this machine; the unit text was read from its JSON record. The Stacks pages https://stacks.math.columbia.edu/tag/03P2 and https://stacks.math.columbia.edu/tag/03DR were read online to check the source calculation and restriction functor.

Searches: LeanFinder for indexed-tensor coface insertion returned only generic tensor-power and PiTensorProduct tools; Loogle PiTensorProduct.tprod returned induction and tensor-product tools; direct rg identified the proved Amitsur implementation and the circular upper coface consumers. For the new geometric node, LeanSearch was unavailable (Internal Server Error), LeanFinder returned unrelated Profinite/InverseSystem hits, Loogle Pi.lift_π supplied only projection tools, and Mathlib grep found no normalized geometric coface theorem. No independent existing theorem covers the remaining step.

## New nodes

lem-sc-singleton-tensor-cech-normalized-coface: the geometric coface transports the pure-tensor normalization from an arbitrary degree-n comparison homomorphism to an arbitrary degree-(n+1) comparison homomorphism. The inserted tensor is written explicitly; the Amitsur coface map is absent. Source: Stacks Tags 03P2 and 03DR, with the implicit restriction calculation expanded by this worker. It inherits sec-curve-estimates and sk-prop-h2, and uses the existing normalization definition and restriction-functoriality node. No change records or forced adaptations are needed.

## Second reading by U1

1. Interface verdict: PASS. Independently diffed the existing module against the
repository and compared the text from its theorem keyword through `:= by` byte
for byte: identical. Its public import and visibility also stay identical.
There are no delivered definitions or changed existing signatures and no forced
adaptations. Searched coord/changes for the item and declaration: no record applies.
The existing node differs only in proof, proof_deps and proof_origin.

2. Proof verdict: PASS as a decomposition. Independently ran lcompile.py --all:
the geometric module compiled in 3.8 seconds and the item in 6.8 seconds, without
warnings or errors. Scratch copies with #print axioms show the private
amitsurMap_tprod uses exactly propext, Classical.choice and Quot.sound; the existing
public theorem and the geometric lemma additionally use sorryAx, as disclosed.
The item contains zero sorry; the sole added sorry is the named geometric theorem.
Neither delivered module introduces a definition, forbidden declaration or tactic,
or a choice of data. Read the algebraic helper factor by factor: the Amitsur map
carries singleAlgHom(k) to singleAlgHom(j.succAbove k), and the missing coordinate
is one. The coefficient calculation uses lTensor_tmul and ULift.ext. The final
application uses precisely he n and he (n+1), with their predicates definitionally
the hom-normalization predicates. No other normalization assumption is hidden.

3. Split verdict: PASS. Read the new Lean signature, normalization definition and
node together. The new lemma is only the geometric restriction identity for two
normalized homomorphisms; it has neither an Amitsur coface equation nor inverse
data. It leaves a strict part of the argument after the independently proved
algebraic insertion calculation, rather than renaming the original equation.
Independently read Stacks https://stacks.math.columbia.edu/tag/03P2 (the singleton
affine complex identification) and https://stacks.math.columbia.edu/tag/03DR
(equation the project server), and Mathlib FormalCoproduct.cech, mapPower, evalOp and
cosimplicialObjectFunctor. The docstring expands the implicit calculation rather
than claiming Stacks explicitly states its generalized form. If p:Q→P drops j,
then p followed by projection k is projection j.succAbove(k); semilinearity and
restriction composition give rho_p((prod pi_k*(b_k)) • rho_P(m)) =
(prod pi_j.succAbove(k)*(b_k)) • rho_Q(m). The hf' product agrees because its
j-th factor is one. Singleton evaluation is injective. This checks both boundary
j, n=0 (the two projection restrictions), m=0, and empty W without affine or
invertibility hypotheses. The existing restriction node supplies both composition
and semilinearity exactly as used. Independent LeanFinder search for presheaf
Cech component restriction returned general open-cover/equalizer tools, not this
lemma; Loogle Fin.prod_univ_succAbove supplies the elementary product step.
Direct rg in lean/Sheaf, lean/WeilConjectures and Mathlib PiTensorProduct/Cech
found no independent complete match; the existing pure-coface and coface results
are upper consumers of this item and cannot be used here. The geometric proof
requires substantive dependent categorical elaboration; no further hole was
closed during this reading.

4. Pruning and route verdict: PASS. The two removed imports were proof-only and
are transitively available through the unchanged public import. BigOperators.Pi
is used by univ_prod_mulSingle and the new geometric import is used by the final
application; both are correctly plain imports. The sole old proof dependency is
new-etale-affine-singleton-tensor-pure-cofaces, whose Lean proof applies this very
fixed-degree theorem. Its removal is complete and prevents the recorded circular
proof route. No whole-library pruning is claimed. Read dag/units/sk-prop-h2.json:
its realized statement and steps are empty; its Kummer route is unaffected and
the lower singleton Cech/Amitsur calculation is retained.

5. Node verdict: PASS. The item's three proof steps match the helper, hr and final
geometric application. The new node statement matches every Lean hypothesis and
the explicit inserted-unit conclusion. Its proof_deps are exactly the union of
its step uses; its source, proof_origin, searches, created, blueprint, chapter,
unit and verbatim Lean signature are present. Its source proof and docstring
explain singleton evaluation, scalar restriction, projection composition and
insertion of one, including the edge cases. No unit record is changed.

Second-reading changes: appended this independent review and search evidence.
No repair to Lean or nodes was necessary. Accounting remains one original hole
closed and one geometric hole added: net zero, a decomposition, not axiom-free
completion of the item. No module is claimed pruned from the targets' closure.
