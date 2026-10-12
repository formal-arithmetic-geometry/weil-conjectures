## What changed

The target theorem is reduced to two named intermediate results. `SheafCoinductionAdjunction.lean` states the sheaf-level restriction-of-scalars adjunction with its canonical action and evaluation counit. `AffineInternalHomEvaluationBijective.lean` states the affine-open evaluation bijection. The target module constructs the required functor, isomorphism, adjunction, action, counit, and linear equivalence from these results and from quasi-coherence of affine pushforward. The target node proof dependencies were updated to match this route.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.sheafHom_affine_rightAdjoint` now has a complete Lean reduction, but still depends on `sorryAx` through the two intermediate theorems. This is a decomposition, not an axiom-free proof: one hole closed, two added, net -1 before pruning. Two strictly smaller intermediate theorems remain as named holes: `AlgebraicGeometry.sheafHom_restrictScalars_adjunction` (node `lem-sc-sheaf-coinduction-adjunction`) and `AlgebraicGeometry.affine_internalHom_evaluation_bijective` (node `lem-sc-affine-internal-hom-evaluation-bijective`).

## No longer needed

The original direct import of `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism` remains needed for the affine pushforward quasi-coherence theorem. The old direct proof dependency `lem-weil-pbc-affine-tilde-gamma-adjunction` is no longer used directly by the target proof; it remains needed indirectly in the affine evaluation node. Thus no old dependency module is globally pruned. The new affine evaluation statement needs only the quasi-coherence predicate and scheme modules, so its unused public import of `Mathlib.AlgebraicGeometry.Modules.Tilde` was replaced by those signature imports. The new coinduction statement does not need `Mathlib.AlgebraicGeometry.Morphisms.Affine`, whose direct import was removed.

## Where the brief, the DAG or earlier work was wrong

The original plan treated the sheaf adjunction and affine section computation as one proof step, although they have independent hypotheses: the adjunction does not require `IsAffineHom`, while the evaluation bijection does. The target statement itself is unchanged. LeanSearch was unavailable during the search run; Loogle, LeanFinder, and grep were run and recorded.

## New nodes

`lem-sc-sheaf-coinduction-adjunction` and `lem-sc-affine-internal-hom-evaluation-bijective` are new strictly smaller statements corresponding to the two independent steps of the Stacks proof.


## Second reading by F1

1. Compared the target module with the repository by `diff`: its existing theorem signature is byte-for-byte unchanged. Only proof imports, a local elaboration option and its proof changed. No definitions, existing statements, or target meanings changed; no change record is required.
2. Compiled all three delivery modules in import order with `lcompile.py`; they compile without warnings. Checked the complete sources: no forbidden declaration or attribute, no data definition containing a hole, and exactly two named whole-proof sorries. The target builds the linear evaluation map explicitly and only uses the bijectivity theorem to obtain its inverse. The adjunction witnesses are eliminated within a proposition, not chosen as arbitrary public data. The delivery axiom probe and explicit `#print axioms` check allow only the standard three axioms and the reported remaining `sorryAx`.
3. Read both split-off signatures, docstring arguments and nodes. The adjunction is independent of affineness, and the evaluation lemma isolates only the section calculation; neither restates the whole target. Checked identity morphisms, zero modules and the empty open: the adjunction becomes the unit-Hom adjunction, and empty sections give the unique maps of zero modules. General morphisms need no finite presentation, and evaluation needs quasi-coherence only of the source. Verified the sources against [Stacks 0A6F](https://stacks.math.columbia.edu/tag/0A6F), [Stacks 0BUZ](https://stacks.math.columbia.edu/tag/0BUZ) and [Stacks 01I7](https://stacks.math.columbia.edu/tag/01I7). Repeated searches with different wording using LeanFinder, Loogle and local `rg`: constant-ring sheaf coextension is not the varying-ring adjunction here; upstream affine Hom surjectivity assumes a quasi-coherent target, which this statement does not. No exact existing theorem was found. The Spec tilde adjunction supplies the affine argument, but transport from over-opens and compatibility with evaluation remain substantial, not a few-minute closure.
4. Reviewed the reduction from the top down: sheaf coinduction supplies precisely action and counit, affine pushforward supplies source quasi-coherence, and the bijective evaluation map supplies the final linear equivalence. The tilde/global-sections argument works for arbitrary target modules, without invalid localization of Hom. The unit `sk-thm-picard-duality` has empty realized statement and step lists; none is bypassed, and the original two mathematical steps are retained. Corrected the old-dependency account in `No longer needed`. No global module pruning is claimed.
5. Checked all node fields, signatures, source and proof steps against Lean. The target's new proof dependencies are exactly the union of its steps. New nodes have source, full natural-language proofs, searches, creation and blueprint provenance, chapter/unit and matching Lean records. The old tilde dependency remains in the new evaluation node.

Changes by the second reader: removed the unused affine import from the new coinduction module; replaced the proof-only exposed Tilde import in the new evaluation module with the minimal signature imports; corrected the report to count this as a decomposition and to identify the old direct dependency now used indirectly. The mathematical reduction is retained.
