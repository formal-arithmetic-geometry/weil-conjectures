## What changed

The finite proper projection theorem now assembles the objectwise projection isomorphisms through a proved natural-transformation component lemma. The proof-only import `Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise` supplies the objectwise statement and the categorical assembly utility. The identity-coherence theorem remains unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite` by applying the proved assembly construction to the objectwise finite projection theorem.

The following declarations still contain `sorry`:

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite` in `Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise` (split-off objectwise proper projection statement).
- `AlgebraicGeometry.Etale.hasProjectionFormula_id` in the item module (identity compactification coherence).

## No longer needed

None. All original imports remain in use; the proof-only objectwise import is required by the finite theorem proof.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was rejected as a stale duplicate because it retained the landed proof while leaving both original holes unchanged. The finite theorem can be reduced to its objectwise components and a real natural-transformation assembly argument; the objectwise component is therefore recorded as a new DAG node.

## New nodes

- `lem-etale-proper-projection-formula-finite-objectwise`: objectwise finite proper projection component, implemented by `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite` in `Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise`.

## Earlier second reading (a previous round; superseded)

The finite assembly proof and the objectwise split compile in the sandbox; the remaining objectwise theorem and identity theorem are intentionally left for subsequent proof work.

## Second reading by F2

1. **Interface check.** I diffed the item module against `sheaf-dag`. Every existing
   declaration has the same signature and statement; the only item change is the proof-only
   import of the new objectwise module and the proof of the finite proper theorem. The new
   module contains the strictly componentwise split, not a duplicate of the bifunctor theorem.
   Verdict: pass.
2. **Proof check.** Both delivered modules compile with `lcompile.py`. The finite proper
   theorem is proved by two applications of `NatTrans.isIso_iff_isIso_app`; the objectwise
   theorem remains the named source-backed split with its required `sorry`. No definition
   contains `sorry`, and no forbidden declaration was added. Verdict: pass, with the objectwise
   hole intentionally retained.
3. **Statement and node check.** The objectwise statement quantifies the two arbitrary derived
   objects and is strictly smaller than the natural-transformation target. Its node records the
   Stacks Tag 0F0G source, proof route, searches, Lean declaration, chapter, and unit. No
   existing node statement was changed. Verdict: pass.
4. **Pruning check.** The new proof uses the objectwise import and the existing projection
   formula declarations; no old import can be removed without dropping required definitions.
   The unit route and `realized` fields are unchanged. The categorical assembly helper is
   private to the new support module, while the item uses its public finite assembly theorem.
   Verdict: pass.
5. **Axiom and edge-case check.** The finite-ring and proper-map hypotheses are preserved, and
   the identity theorem is unchanged. The assembly proof introduces no axioms beyond those
   already present in the imported source declarations. Verdict: pass.

I kept the fast categorical assembly helper private to the support module, restored the exact
spacing of the existing theorem signature, and added this review record. The remaining
holes are `isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite` (the split-off objectwise
source theorem) and `hasProjectionFormula_id` (the pre-existing identity coherence theorem).
