Files written:
- dag/nodes/sec-picard-framework/lem-sc-flat-base-change-coherent.json: statement, split; no Mathlib match, no new nodes.

Attachments: none. The matching Lean declaration, AlgebraicGeometry.Scheme.Modules.nonempty_H_pullback_linearEquiv (WeilConjectures/AlgebraicGeometry/Cohomology/EulerChar.lean:100-116), contains sorry, so it is not a closed attachment.

WANTED: none.

The imported proof was already a valid one-level split. Its main risk was the phrase "finite intersections are affine": that is valid here because proper over a field implies separated over the affine base. The parallel DAG node lem-pc-flat-base-change-cohom states a more general theorem but is not substituted for this item's proof. No statement or blueprint error was found. Nothing remains unfinished at this stage.

## Review by F1

I read the item, unit sk-thm-picard-rr, the Lean statement and its sorry at EulerChar.lean:100-116, and Stacks Project coherent.tex, Lemma 30.5.2 (Tag 02KH). The source assumes a quasi-compact quasi-separated morphism and flat base change. Here X proper over Spec k supplies both finiteness properties; k to k' is flat by hypothesis, F is quasi-coherent, and the field specialization is explicitly within the statement. The algebraically closed condition is stronger than needed for the final dimension equality, but does not change the claim.

For Step 1, def-weil-proper-morphism gives separatedness and finite type, hence a finite affine cover with affine intersections over the affine base; def-pc-base-change gives its pullback; lem-pc-cech-computes states precisely that the Cech complex on an affine-intersection cover computes quasi-coherent cohomology. I checked that this last node's hypotheses hold for both X and its base change. In Step 2, the affine pullback formula follows from def-pc-base-change and the affine description of quasi-coherent modules: Spec A_J becomes Spec(A_J tensor_k k'), and tilde M_J pulls back to tilde(M_J tensor_k k'). Restriction maps are induced by localization and the formulas commute with them. This is the affine calculation in the proof of 02KH. In Step 3, flat tensor is exact by the definition of flatness; the short exact sequences for cycles and boundaries show explicitly that tensor commutes with cohomology. Combining Steps 1 and 2 then yields the natural isomorphism. In Step 4, def-pc-field-extension supplies the field-extension setting; every vector space has a basis and its scalar extension has the corresponding basis, including zero and infinite-dimensional cases. This gives dimension equality for O_X.

I checked the B-E return checklist against the sole node: no new node requires a self-contained statement or Mathlib search, all cited nodes exist and state the used claims, there is no off-unit tool use, the proof is not a restatement of the conclusion, and no hypothesis is borrowed from a different setting. Small cases considered were X empty (both complexes zero), X = Spec k (degree zero equals k', positive degrees vanish), and k'=k (identity base change). No correction to the mathematical content was needed; I added the split status and split_report with blueprint realization.
