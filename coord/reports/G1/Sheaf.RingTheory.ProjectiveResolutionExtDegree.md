## What changed

Reviewed `Sheaf.RingTheory.ProjectiveResolutionExtDegree` and discarded the unused cocycle-condition binder in the forward proof of `ModuleCat.projective_resolution_ext_degree`. Its signature, imports, proof route, and node remain unchanged. The supplied module already had a complete proof.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree` was already proved before this work. Initial holes: 0; holes closed: 0; holes added: 0; holes left: none. No decomposition is introduced. The original module compiles in 1.7 seconds; the delivery dry run additionally runs the declaration axiom probe.

## No longer needed

None. Tested removing `Mathlib.CategoryTheory.Abelian.Projective.Ext`, but compilation then cannot find `ProjectiveResolution.extMk_surjective`; restored it. All existing imports and proof dependencies remain necessary. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The brief says the module still contains `sorry`, but the supplied checkout already contains the complete proof and its node records successful prior proof review. The proof follows the node's four steps, including the actual bounded-resolution construction via the proved successor splicing theorem. This delivery claims no new proof progress.

## Second reading by G1

1. **Visible changes and signatures.** Compared the delivered module with the repository version. The only change is replacing the unused forward-proof binder `hf` with `_`; the theorem statement, all existing declarations, definitions, imports, and proof route are byte-for-byte unchanged otherwise. No change record is needed.

2. **Proof and axioms.** Compiled `lean/Sheaf/RingTheory/ProjectiveResolutionExtDegree.lean` with `lcompile.py`; it compiled cleanly. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses the stated Mathlib Ext representation and the existing successor-splicing theorem, with no hollow definition. The declaration was already accepted by the prior axiom probe and has no open holes.

3. **Statements and dependencies.** The theorem statement is unchanged and matches the node exactly. No new statement was split off, so there are no new truth or strength concerns. The imports remain necessary: `ProjectiveResolution.extMk_surjective` comes from `Mathlib.CategoryTheory.Abelian.Projective.Ext`, while the reverse implication uses the successor-splicing module; removing the former fails compilation. The node's `proof`, `proof_deps`, and `proof_origin` agree with the code, and no old dependency can be pruned.

4. **Shorter route and searches.** The forward proof directly uses `HasProjectiveDimensionLT.mk` and `extMk_surjective`; the reverse proof uses Mathlib's zero-dimension equivalence and short-exact dimension shifting, then the existing splicing result. The node records the prior searches for an exact Mathlib bounded-resolution equivalence, all negative. No shorter available declaration was found, and no import is unnecessarily public.

5. **Unit route.** The reverse successor case still applies `ModuleCat.hasProjectiveResolutionLE_of_shortExact_projective_middle`, exactly the realized successor-splicing step in unit `sk-thm-p1`; the zero case and forward Ext argument likewise follow the node's four planned steps. No unit route is bypassed.

I changed only the unused binder in the forward proof and added this second-reading record. No holes were closed or added, and no modules or DAG nodes were pruned.
