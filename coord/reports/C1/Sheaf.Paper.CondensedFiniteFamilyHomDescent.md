## What changed

Return repair: removed the duplicate private `scalar_unit` and `mixedScalarMap_unit` declarations from `CondensedOverlapFactorTranspose`. Their single shared proofs live in `CondensedLocalCoefficientAdjoints` and are exported for the overlap module to use through its existing import. No theorem statement or definition body changes in this repair. The local-adjoints node and change record name the shared API.

Proved `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_family_hom_factorizations` with its original signature. The proof forms colimits of the actual pulled coefficient rings and scalar extensions, transports them to each oriented overlap, applies finitely presented Hom continuity, chooses one common filtered stage for the finite family, and transposes the resulting factors. Both directions use the same field; filteredness also handles an empty family.

The new module `Sheaf.Paper.CondensedOverlapFactorTranspose` proves the fixed-field, single-overlap transposition calculation completely. Its proof composes the scalar and pullback module adjunctions, uses monoidal naturality to compare restrictions, and applies injectivity of the resulting Hom equivalence. The scalar-unit formula identifies its compatibility equation with the specified canonical local adjoints.

Two representation repairs make this argument check efficiently. `CondensedLocalCoefficientAdjoints` constructs the underlying mixed-scalar map explicitly and proves equality to its original canonical adjunct. The existing source `FiniteCoefficient.UpperLowerStar.Iso` gives the square comparison explicitly typed component maps and proves equality to its previous composite by rfl. Every existing declaration signature and visibility is preserved. The three unclaimed consumers `ProEtaleLocalQuotientVanishing`, `FiniteCoefficient.UpperLowerStar.CoherenceLegacy`, and `WeilSheaf.UpperStarComp` use that equality API in precisely the proof steps that previously unfolded the old composite. Their mathematical statements are unchanged.

Change records: `coord/changes/C1-condensed-local-adjoint-underlying-map.md` and `coord/changes/C1-condensed-overlap-component-comparison.md`. They list all downstream modules and exact-name users, current holders, effects, and the definition bodies. The equality theorems identify the old data exactly; the records flag the prescribed target-meaning review. No target text changes.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_family_hom_factorizations` (node `lem-weil-pbc-condensed-finite-family-hom-descent`). Added 0 holes. This is a proof, not a decomposition.

The new theorem `AlgebraicGeometry.ProEtale.finiteCoefficient_overlap_factor_transpose` (node `lem-weil-pbc-condensed-overlap-factor-transpose`) is also fully proved. All supporting unit, colimit, module-comparison, linearity and representation-equality lemmas are proved. No sorry remains in any delivered Lean file, including the definition-repair and consumer files. There are no open split-offs.

The item and its helper compiled against the original scalar-extension construction after an experimental global scalar-carrier refactor was removed. All direct-name consumers of the square-comparison repair were checked; the three necessary proof adaptations compile, and the other direct-name consumers compile unchanged. The unchanged direct consumer of the local-adjoint repair, `CondensedFiniteLocalSubmodules`, also compiled.

## No longer needed

The two duplicate private scalar-unit proofs in `CondensedOverlapFactorTranspose` are no longer needed. Their uses now resolve to the imported shared lemmas. No additional import or DAG dependency is needed.

Removed the proof import `Sheaf.Paper.CondensedCoefficientFamilyHomStage` and proof dependency `lem-weil-pbc-condensed-coefficient-family-hom-stage`: generic `condensed_fp_hom_stage` suffices. Removed `def-weil-pbc-condensed-e-module-category` from this item's proof dependencies: the argument keeps actual pulled coefficient rings instead of normalizing every overlap ring. Its definitions can still be reached through statement imports; this is pruning of this proof route, not a claim that no other module uses them.

Removed the redundant proof import of `CondensedCoefficientComplexDiagram` from the overlap helper because the local-adjoint definition now publicly supplies the required mixed-scalar API. Unused generic transitivity and identity-model helpers were removed from the overlap module. The scalar-extension carrier/action experiment was excluded entirely: no delivery change to `CategoryTheory.ModuleObjects.ExtendScalars` is needed. No additional planned lemma, node or module is imported only to follow the old route. The blueprint unit's route is retained.

## Where the brief, the DAG or earlier work was wrong

The returned delivery proved two identical unit formulas in both the local-adjoint and overlap modules. The return correctly identified this duplication. This repair keeps one proof of each formula and imports it at the overlap uses.

The earlier attempt had not obtained a compiling delivery and left the fixed-field transpose open. That theorem is now proved. No false mathematical statement or missing hypothesis was found. The original DAG's coefficient-normalization detour is unnecessary; actual pulled diagrams give the required colimits directly.

A syntactic composite of natural isomorphisms caused kernel timeouts when specialized at finite coefficient sheaves. Naming its component maps fixed the representation without changing the comparison, as witnessed by `upperStarCompIso_eq_composite`. After that repair, the original quotient proof failed at line 47 because its composite rewrite pattern disappeared, and the original WeilSheaf proof failed at lines 53 and 118 for the same reason. The original CoherenceLegacy consumer exceeded the 60-second limit while comparing the rebuilt comparison with its factorization composite. Rewriting each through the equality API restores the original argument; the adapted files compile in 3, 15 and 5 seconds respectively. These modules were unclaimed, and no signatures or visibility changed.

Large rewrites of equations between module homomorphisms also exhausted elaboration heartbeats. Generic formulas for underlying cocone legs and direct composition of equalities remove those rewrites. The full family proof then compiles within the ordinary file limit. No file or proof was split to evade that limit, and no limit was raised.

## Forced adaptations

All three adapted consumers were unclaimed. Existing signatures and visibility are identical; only the proof lines below change. The original files were compiled against the repaired comparison before adaptation.

- `Sheaf.AlgebraicGeometry.ProEtaleLocalQuotientVanishing`: original line 47 reports `Tactic rewrite failed: Did not find an occurrence of the pattern ?f ≫ ?g ≫ ?h`. At line 46, the `simp only` list replaces `upperStarCompIso` with `upperStarCompIso_eq_composite`. This restores the composite expected by the following unchanged conjugation calculation.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`: the original file reports `timeout after 60 s` when checking the comparison-factorization equality. The sole added line, line 172, is `rw [upperStarCompIso_eq_composite]`; it restores the original composite before the existing proof. The adapted file checks within the original limit.
- `WeilConjectures.WeilSheaf.UpperStarComp`: original line 53 reports `Tactic rewrite failed: Did not find an occurrence of the pattern upperStarCongr A`, and original line 118 reports `simp made no progress`. The rewrite lists at lines 53 and 118–119 replace unfolding `upperStarCompIso` with `upperStarCompIso_eq_composite` (the latter list wraps onto an extra line). The original symmetry and composition arguments then apply unchanged.

## New nodes

`lem-weil-pbc-condensed-overlap-factor-transpose`: a completely proved fixed-field, single-span scalar-adjunction compatibility theorem. Its inputs include the coefficient field and an E-linear factor; it does not supply a common stage, assume finite presentation or qcqs, or assert finite-family descent. Its node records the composed-adjunction and monoidal-square argument, and its docstring gives the full mathematical proof, including zero modules and empty overlaps.

## Second reading by C1

1. Compared the delivered item and adapted modules with the repository versions. Existing declaration signatures are unchanged; the two representation repairs have change records, and the forced consumer edits are proof-only. Verdict: pass.
2. Compiled all seven delivered Lean files with `lcompile.py --all` (main item 39.4 seconds) and searched for `sorry`, forbidden declarations, and hollow definitions. The build is clean and the search found none. A scratch `#print axioms` check of the family theorem, overlap theorem, `finiteCoefficientLocalAdjoint_eq_canonical`, and `upperStarCompIso_eq_composite` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Read the new overlap theorem and its DAG node. The statement is a strict fixed-field, single-overlap reduction, is true in empty and zero cases, has a complete source proof, and is not duplicated in the library. Verdict: pass.
4. Checked the proof route from the target downward, including the realized proper-base-change unit, and checked imports and the `No longer needed` pruning claims. The proof uses the generic finite-presentation stage and the named overlap transposition; no shorter existing theorem was found. Verdict: pass.
5. Checked the item and helper DAG `proof`, `proof_deps`, `proof_origin`, Lean records, and the unit record against the proofs. Added node metadata and change records agree with the delivered declarations. Verdict: pass.

Independently compiled the three original consumer files against the delivered dependency overlay. The quotient and WeilSheaf consumers fail at the reported rewrite steps; `CoherenceLegacy` times out at the unchanged 60-second limit. Their adapted versions compile. Existing declaration-header comparison reports no differences in any of the six existing modules. A fresh semantic search found only ordinary `ModuleCat` scalar-adjunction formulas, not this internal-module overlap statement; local searches found the existing pullback-scalar API already accounted for by the proof.

Changed during second reading: added the missing `UpperLowerStar.Restriction` user row to the comparison change record, restored the original public import in `WeilSheaf.UpperStarComp` to avoid an unnecessary interface change, and added this section.
