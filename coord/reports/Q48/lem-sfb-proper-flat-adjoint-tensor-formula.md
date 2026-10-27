# Stage-1 delivery: lem-sfb-proper-flat-adjoint-tensor-formula

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-flat-adjoint-tensor-formula.json`: split statement; Mathlib verdict: no match. Six proof steps, using existing nodes only.
- `citations.json`: one verbatim statement quotation for every cited node in every proof step.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `prepare.py` is a sandbox-only preparation script.

New nodes: **0**. New Mathlib leaves: **0**.

## Attachments

None. I searched the live `lean/WeilConjectures/` both for the blueprint tag and for proper-flat/right-adjoint/tensor/dualizing terminology. No declaration states the whole item. The nearby `proper_flat_rightAdjoint_baseChange_hβ` is base change of ordinary derived direct image, and explicitly uses no right adjoint. `smooth_proper_diagonal_tensor_formula` is about a perfect proper closed immersion over Noetherian schemes. Neither is an attachment. The general `perfect_rightAdjoint_tensor_hom_comparison` is instead reused through its existing node as the counit calculation in step 2. The general direct-sum, exact-structure and generation declarations correspond to existing DAG inputs, not to the complete item.

## WANTED

None. The item's source and all the mathematical inputs needed for this split are already available locally, or are existing DAG statements. No SGA source was used.

## Findings and corrections

The item statement agrees with Stacks `duality.tex`, Tag 0E4K (`lemma-compare-with-pullback-flat-proper`), equation 0A9S, and the trace square of Tag 0B6S (`remark-relative-dualizing-complex`). I left its statement unchanged, including its supplied adjoint, unbounded domain, qcqs base, finite-presentation condition and lack of Noetherianity.

I removed `def-pur-derived-internal-hom` from `stmt_deps`: the statement does not use internal Hom. The proof now gives the actual duality calculation on perfect objects, extension by perfect localizing generation, and the exact original-counit identity. In particular it does not cite the Noetherian versions of the perfect-case or localizing-comparison theorems as though they applied here.

An existing input has a source-label imprecision: `lem-sc-proper-flat-right-adjoint-direct-sums` names Tag 0E4H, which the local tag map identifies as the *section*. The theorem actually used is Tag **0E4I**, `lemma-proper-flat`, directly read in `duality.tex`. Its statement has exactly the needed hypotheses. This delivery cites its correct existing statement and records 0E4I on its own proof step; it does not change that other node.

`blueprint_refs.py ancestor lem-sfb-proper-flat-adjoint-tensor-formula` reports `None` because the inherited creation chain has no recognized imported ancestor. The inherited `blueprint.from.place` already describes the intended `det-thm-sf-ctf-stability-direct-images` proof (3) chain precisely, through the polynomial dualizing model. I retained the maintainer-owned `from.node` and `via`. I read the current `literature/blueprint/latest/` unit and direct-image proof, rather than an old snapshot. This generic scheme-duality input supports that existing chain; it does not replace a unit-level direct-image argument.

## Not duplicates

No new nodes were created. The searches of the DAG and whole blueprint for 0E4K, tensor/adjoint, Grothendieck duality and perfect generation found reusable generic inputs. The existing `lem-sc-smooth-proper-tensor-perfect-case` and `lem-sc-right-adjoint-tensor-locus-localizing` assume Noetherian schemes, whereas this item does not. Their general ingredients already exist separately and are used instead. `lem-pc-perfect-generator-exists` and `lem-pc-derived-qcoh-perfect-generation` provide the needed generation; I use the latter directly, without creating a second generation lemma. No new node restates the item or one of its clauses.

## Review by Q48

I read delivery-errors B--E and audited the actual statement of every cited node; `citations.json` copies those statements verbatim. There are no new nodes needing separate source or Mathlib checks. For the item I read Stacks Tags 0A9S, 0A9T, 0E4I, 0E4K and 0B6S in `duality.tex`, together with the unbounded projection formula 08EU in `perfect.tex`, and checked their labels in `tags/tags`. The proof follows their perfect-object and localizing-generation argument.

**Step 1.** `def-weil-pbc-scheme-conventions` explicitly includes qcqs in finite presentation. `lem-pc-derived-direct-image-preserves-qcoh` applies because the given map is therefore qcqs. `lem-pc-derived-pullback-tensor-qcoh` gives both closure claims, not just underived pullback closure. `lem-sc-derived-pullback-across-universes-monoidal-adjunction` gives the canonical K-flat monoidal pullback and its derived adjunction, with no finiteness restriction. `lem-pc-projection-formula` states the canonical unbounded quasi-coherent projection map is invertible. Its inverse is the projection isomorphism used in the statement. Defining its mate and checking its naturality is written out, rather than inferred from a definition of some unrelated comparison.

**Step 2.** `lem-pc-perfect-tensor-hom-duality` provides the dual, the two tensor-Hom bijections and the pulled-back dual pair, for every scheme. `lem-pc-projection-formula` supplies the middle Hom identification. Crucially, `lem-sc-perfect-right-adjoint-tensor-hom-comparison` states that these precise bijections send q to its composition with the counit-pinned comparison. Its hypotheses are exactly the closure, monoidal adjunction and canonical projection maps of step 1; I checked its full statement and its live Lean signature, which impose no Noetherianity. Thus the chain proves invertibility of the specified morphism, not merely existence of an isomorphism between the two objects. The two substitutions producing a two-sided inverse are explicit. This is the source's perfect-complex calculation, not a hidden new lemma.

**Step 3.** `lem-sc-proper-flat-right-adjoint-direct-sums` has the same qcqs/proper/flat/finite-presentation hypotheses as the item. The supplied right adjoint is the one used throughout. `lem-pc-ringed-spaces-derived-adjoint` and `lem-weil-pbc-left-adjoint-preserves-colimits` give pullback preservation of sums. `lem-sc-derived-tensor-right-coproducts` applies to the fixed arbitrary derived object omega, without any perfection assumption on omega. I also cite both ambient sum existence and quasi-coherent closure (`lem-pc-derived-ambient-has-coproducts`, `lem-pc-derived-qcoh-closed-coproducts`), as well as subcategory sum existence (`lem-pc-derived-qcoh-direct-sums`); existence alone would not identify the ambient sum. Restriction of the universal property to a full subcategory justifies the identification in a few lines. All sums use the same fixed indexing universe.

**Step 4.** `lem-sc-derived-separate-exact-structures` really covers arbitrary scheme morphisms with the stated derived adjunction and closure hypotheses. Its statement gives exactness of both functors without requiring the Noetherian geometric comparison theorem. `lem-sc-perfect-localizing-iso-locus` accepts separately chosen exact shift structures and a natural transformation, and requires invertibility on every shift of every perfect object. The same statement supplies stability of perfection under shifts, so step 2 verifies precisely that premise. Step 3 verifies its coproduct premise. I have not silently assumed a shift-compatibility statement absent from either node.

**Step 5.** `lem-pc-derived-qcoh-perfect-generation` says that the closure under shifts, cones, retracts and arbitrary sums of all perfect complexes is the entire quasi-coherent derived category on a qcqs scheme. It applies to S, which has that hypothesis explicitly. It gives the needed localizing closure conclusion directly; it is not merely a weak-generator detection statement.

**Step 6.** This is an elementary calculation with the adjunction bijection, whose inverse sends a map t to the original counit composed with R(t). The transferred bijection along the now-proved natural isomorphism yields the counit epsilon composed with R(tau). That is exactly the composite defining tau. This verifies the trace normalization of 0B6S without adding any adjoint-existence claim or an unproved compatibility theorem.

For edge cases, I checked the identity map (omega is the tensor unit and the comparison is the unit isomorphism), an empty source (both sides and the resulting map are zero, with zero counit), M=0, all integer shifts of a perfect complex, and arbitrary coproducts of those shifts. For finite locally free maps over a possibly non-Noetherian affine base, the formula specializes to dualizing a finite projective algebra, so none of the argument smuggles in a regularity or Noetherian condition. The proof never asks that omega itself be perfect, that a preserve colimits other than direct sums, or that M be bounded. No non-elementary step exceeds 2000 characters (the longest is 1173); every non-elementary input in these steps has an existing cited statement. No statement dispute was found.

The five fresh Mathlib searches were actually run by `msearch.py`: two LeanFinder phrasings, Loogle, grep and LeanSearch. All services answered. I read their hits: they concern ordinary module-sheaf adjunctions, abstract tensor duality, representably flat right adjoints, or condensed tensor projectivity, not the present geometric duality theorem. I inspected the ordinary scheme-module adjunction in Mathlib's `AlgebraicGeometry/Modules/Sheaf.lean` (declaration at line 189 and instances at 198--199) to exclude that tempting match. Previous inherited searches are retained, and the exact new queries and actual hit summaries are appended to `mathlib_searches`.

## Unfinished work

None in the stage-1 split. All cited inputs were already DAG nodes. No Lean was written, compiled or built. The required server dry run and final push follow this review.
