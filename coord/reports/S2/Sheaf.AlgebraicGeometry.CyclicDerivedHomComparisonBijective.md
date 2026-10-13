## What changed

Completed `AlgebraicGeometry.Etale.abelianRepresentableCohomologyMap_bijective` without changing
its signature or docstring. All new helpers are private and proved. The ordinary Hom comparison
is the composite of the pullback adjunction, free-sheaf sections equivalence, pullback symmetry,
localization restriction, and the constant-sheaf/global-sections equivalence. Naturality and its
value at the identity identify it with the explicit generator map.

The private `extComparison_bijective` proves the higher-degree comparison by induction using
injective presentations, the long exact Ext sequence, and the additive right-exact five lemma.
The final proof composes this bijection with `abelianPlusHomExtEquiv`.
Added a proof-only import of `WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic`.
Mathlib Ext and five-lemma APIs are already publicly available through the statement import.
Updated the item's DAG proof to
match this argument. No existing interface, definition, statement, or public import changes.

The abstract Ext induction, ordinary-Hom equivalence with naturality and identity calculation,
and the instantiation at the actual etale pullback projection compile independently through
`lcompile.py`. After the statement module reached the published build, the complete
item compiled cleanly through `lcompile.py` in 36.6 seconds, with no warnings. Universe
parameters and namespace openings are scoped to the private declarations and proof terms,
so the original file-level commands remain identical. The delivery dry run performs the
remaining axiom and metadata checks. A recovery copy is saved as
`scratchpad/CompleteCandidate.lean`; scratchpad files are outside the delivered Lean tree.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Etale.abelianRepresentableCohomologyMap_bijective`
(node `lem-sbc-abelian-representable-cohomology-map-bijective`). Holes added: none.
Every private helper is proved; no `sorry` remains in the delivered Lean module.
This is a proof, not a decomposition into postponed statements.

The new dependency node records the already proved
`AlgebraicGeometry.Etale.injective_upperStar_obj_of_etale_addCommGrp`; it adds no Lean declaration
and no hole. Its module is imported solely for the proof.

## No longer needed

No existing imports removed. None of the original six definition nodes can be pruned: their
constructions occur in the actual comparison or its proof. The planned construction of an
extension-by-zero representing isomorphism and identification of its derived-adjunction unit
are unnecessary. They have no separate nodes or imported modules in the original item's
`proof_deps`, so no such module can be claimed as pruned. The module-coefficient analogue
`lem-weil-pbc-etale-restriction-injectives` is not imported or used by this proof.
The unit record `sk-lem-failure-field` has no realized statement/steps for this item; its route
is preserved.

## Where the brief, the DAG or earlier work was wrong

The plan omits that dimension shifting extends the ordinary-Hom bijection directly, avoiding
a separate construction of the extension-by-zero representing isomorphism. The existing
abelian-coefficient restriction theorem in `TorsionAcyclic` supplies injective preservation.
The node's warning about the module-coefficient analogue is correct.

At the start of checking, the source module `CyclicDerivedHomComparisonMap` had landed after
the published green build and its compiled module was unavailable both locally and in the
published build. The published build was commit
`1b9218df02d0f8284546a3ea28ee6e9a3da050ae`, stamped `2026-10-13T21:09:58Z`;
the item's source landing `20261013T211115-L-395569` is later and was still waiting for
global verification when first checked. The dependency became available after publication of
commit `938781dc42642c0e72a1d78e601ffc78f98ebcb3`, stamped `2026-10-13T21:55:18Z`.
The abstract Hom and Ext proofs were checked independently while waiting;
no dependency was copied into the sandbox or redefined to bypass the published build.

## New nodes

`lem-sbc-etale-abelian-restriction-injectives` records the existing proved abelian-coefficient
restriction theorem in `WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic`, with its exact
source and proof. It is needed in the successor step of dimension shifting. Blueprint search
found the module-coefficient analogue but no separate abelian-coefficient node. The blueprint
ancestor was followed through the existing `blueprint.from` records to
`sbc-lem-higher-direct-image-presheaf`; the ancestor tool stops at a module-valued `created.item`.
No new module, new hole, or change record is needed.

## Second reading by S2

1. **Signatures and accidental changes.** I compared the delivered module with the repository
version. The existing theorem statement and docstring are byte-for-byte unchanged; the only
interface change is the proof-only import of `WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic`.
The added DAG node records the existing injective-preservation declaration and adds no Lean hole.
Verdict: pass.

2. **Compilation and axioms.** The module compiles through `lcompile.py` in 41.1 seconds with no
errors or warnings. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for
`abelianRepresentableCohomologyMap_bijective`; there are no `sorry`, `axiom`, `unsafe`, `opaque`,
`extern`, or `implemented_by` declarations. Verdict: pass.

3. **Statement truth and strength.** The target retains all hypotheses and its original conclusion.
The attached restriction-injectives statement is exactly the already proved AddCommGrpCat theorem
used by the induction, with no extra assumptions or weakened conclusion. Its source and proof
record are present in the new node. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing free-sheaf/sections equivalence and
the abelian restriction-injectives theorem, then a proved generic Ext dimension-shifting argument.
No planned extension-by-zero construction is needed, and no unused import remains. The unit route
and all realized definitions used by the target remain in the DAG. Verdict: pass.

5. **DAG agreement.** The item's `proof`, `proof_deps`, and `proof_origin` describe the comparison
equivalence, injective-preserving Ext induction, and final derived-to-Ext composition used in Lean.
The new node has the required statement, source, proof, searches, Lean attachment, blueprint, unit,
and chapter fields. Verdict: pass.

I changed only this report section; no Lean declarations, statements, definitions, or imports beyond
the proof-only import were changed during second reading.
