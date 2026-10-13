## What changed

Replaced the sorry in CategoryTheory.homTensorDegreewise_reverse_construct with the
reverse construction in the node's plan. Restrict to each tensor summand, curry to
its iterated internal Hom, lift through the inner Hom product, then lift through the
outer Hom product. Both product factorization identities give the original localized
evaluation equation. The statement and existing visibility are unchanged.

Added proof imports HomComplexProjections, HomTensorReversePair, and InternalHomProduct.
HomTensorReversePair now also imports all
Sheaf.Algebra.Category.ModuleCat.Sheaf.HomTensorPair for its existing private currying
and uncurrying constructions. The two new generic module-sheaf lemmas separate the
localized tensor calculation from product assembly. Their signatures retain separate site object and morphism universes.
The unit's realized statement and steps are unchanged (its realized arrays are empty).

## Proved and sorry left

Closed: CategoryTheory.homTensorDegreewise_reverse_construct
(lem-sc-hom-tensor-reverse-construction), the sole original sorry.

Also proved: SheafOfModules.homTensorReversePair_construct
(lem-sc-hom-tensor-reverse-pair) by explicit presheaf evaluation, associativity, braiding,
and two currying operations; SheafOfModules.internalHomProductFanIsLimit
(lem-sc-internal-hom-product-fan) by sectionwise limit reflection.

No sorry remains in the delivered modules; no hole was added. No axiom, definition,
existing signature, or target was changed. Classical choices in the assembly select
maps uniquely determined by all localized evaluations or by product universal properties.

## No longer needed

No existing import removed: HomTensorDegreewiseEquation is needed for the statement.
Removed the entire duplicate private presheaf helper block from HomTensorReversePair:
tmulRight_pair, tensorHomCurryApp_pair, tensorHomCurryApp_app_apply_pair,
tensorHomCurryApp_add_pair, tensorHomCurryApp_smul_pair, tensorHomCurryApp_map_pair,
tensorHomCurry_pair, homObjEvalId_pair, and tensorHomUncurry_pair. Their existing
HomTensorPair implementations are now reused, so these are not new proof obligations.
The reverse construction no longer invokes lem-pc-sheaf-modules-tensor-closed or
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed as a direct proof dependency.
The generic closed structure is replaced by the explicit separate-universe pair
calculation and sectionwise products.

The original proof dependencies def-pur-sheaf-tensor-product and
def-weil-presheaf-modules-sheafification are still used by the pair construction;
def-pur-hom-complex and def-pc-tensor-complex-sheaves remain used by the main proof.
These nodes are not globally pruned. No claim is made that a module leaves the target
import closure merely because this proof does not directly invoke its theorem.

## Where the brief, the DAG or earlier work was wrong

Repair of return X-c47e9: the prior delivery copied four identical private
lemma statements from HomTensorPair, which import_prune_check correctly refused.
Removed all nine copied helper declarations and reused the existing implementation
through import all. No existing library module or visibility was changed.
The prior second reading has been removed because it described the superseded copy;
the second reader must review this repaired version. deliver3.py --no-push rebases
the concrete delivery onto current origin/sheaf-dag without pushing.

The original plan is mathematically sound. The generic tensorClosed theorem is stated
with a single site universe, whereas this module has separate object and morphism
universes. The needed localized formulas can be proved directly instead of changing
that theorem's interface. The existing source currying code supplies the formulas;
HomTensorPair already provides the required private helpers in separate universes;
the repair imports them with a proof-only import all instead of copying them.

The local literature files are not present in this clone. The stated sources were read
from https://stacks.math.columbia.edu/tag/03EO and
https://stacks.math.columbia.edu/tag/0A90. Stacks omits the proof; the delivered docstrings
and nodes expand the local evaluation and product argument.

During the session the compilation wrapper acquired a remote fallback. One fallback
attempt could not see sandbox imports; the updated wrapper now excludes local-artifact
compiles from that fallback. Subsequent checks use the sandbox overlay.

The initial main proof unfolded the chosen Hom-complex bifunctor repeatedly while
checking the product projections. The proof now keeps the chosen component maps and
product-limit witnesses abstract. A proved private hom_product_spec lemma identifies the
chosen product projections once; the main proof uses local irreducibility attributes on
homComplex, homComplexFunctor, and homTensorCurryProjection. These attributes are local
and change no imported interface or behavior of a downstream module.


## New nodes

lem-sc-hom-tensor-reverse-pair: reverse currying for one pair of module sheaves,
with its full localized evaluation equation. This has no complexes, products, or
coproducts and is strictly the first part of the original proof.

lem-sc-internal-hom-product-fan: internal Hom from a fixed module sheaf preserves
integer-indexed products in its second argument. This has no tensor, complex, or
reverse comparison and supplies only the inner product assembly.

Both are proved and carry explicit source-based proof sketches, recorded Mathlib searches,
and the original node's chapter, unit, and blueprint ancestry. The local reducibility command is documented in
coord/changes/homTensorReverseConstruction-local-reducibility.md for the conservative
preflight command scanner; no external interface is changed.

## Second reading by W3

1. **Interface comparison:** compared each delivered module against the repository copy. The existing declaration `CategoryTheory.homTensorDegreewise_reverse_construct` has the same signature byte for byte; the two added declarations are new split nodes with their recorded statements. Verdict: pass.

2. **Proof and axioms:** compiled all three modules with `lcompile.py --all`; searched for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and `debug.skipKernelTC`, finding none. The delivered proofs use only the permitted foundations, with upstream open statements accounted for in the node records. Verdict: pass.

3. **Split statements:** checked both new statements against their docstrings, source references, and uses in the main proof. The pair construction and product-limit theorem are strictly smaller than the target and introduce no hollow definition or arbitrary witness. Local searches and the recorded Mathlib searches found no existing duplicate. Verdict: pass.

4. **Pruning and route:** the proof uses the pair construction, Hom-complex projections, and both inner and outer product limits, preserving the unit route. The proof-only imports are minimal for the delivered declarations; no old proof dependency can be removed without bypassing that route. Verdict: pass.

5. **DAG agreement:** checked `proof`, `proof_deps`, `proof_origin`, Lean declarations, and source/provenance fields for all three nodes. They agree with the code and no unit `realized` entry is altered. Verdict: pass.

Changed during second reading: no Lean proof or statement changes were needed; this section records the checks above. The delivery dry run is being rerun through the project validator before final delivery.
