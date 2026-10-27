# Stage-1 report: lem-sfb-quotient-pullback-tensor-coherence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-quotient-pullback-tensor-coherence.json`: statement, split into six proof steps; no exact Mathlib match. Statement unchanged.
- `citations.json`: fourteen exact excerpts, one for every proof-step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `write_split.py` is a sandbox-only writing aid.

No new nodes; no Mathlib leaves. No chapter or unit record changed.

## Attachments

None. I searched the project under `lean/WeilConjectures/` for the precise blueprint tag and for quotient/pullback/scalar tensor normalization. The precise tag has no hit. The pro-etale scalar-extension projection files concern other comparisons and do not give all the clauses, including the specified quotient comparison and its tensor equation. I made no finished-proof claim from a sorry declaration.

## WANTED

None: the blueprint and all Stacks source files needed here are present.

## Problems and changes

The item was statement-only. The blueprint integral proof paragraph (3) asserts compatibility of reduction with the canonical maps but does not supply the tensor calculation. The split supplies that argument and retains the actual coefficient quotient, the specified lambda, the internal module category and the uncompleted tensor product. There is no statement dispute or source correction.

I reused the general ringed comparison and K-flat lemmas already present in the DAG. I did not create a lemma for a clause of the item, for its elementary naturality square, or for the elementary balancing calculation. I explicitly kept the zero-based indexing of `def-sfb-integral-quotient-coefficients` separate from this item's n >= 1: its index is n-1.

Mathlib searches used the required command with this item id and two semantic phrasings, Loogle patterns for pullbackComp and NatTrans.IsMonoidal.tensor, and two grep patterns. All seven calls succeeded; their results were read and recorded as returned in `searches.jsonl`. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, especially pullbackComp at line 167, its adjunction normalization at 177, and pullback_assoc at 192. Those are ordinary module-sheaf pullbacks, without the unbounded internal quotient tensor comparison. I also read `Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean`, lines 43-52: IsMonoidal.tensor is conditional on the IsMonoidal instance, whose existence here is precisely what must be established. The Tor and condensed sheafification hits do not have the required objects or normalized comparison. Existing inherited search records were retained; only searches actually run here were added.

## Not duplicates

No new node was created. Whole-DAG searches for 0D6D, pullback composition, normalization and tensor coherence identified the existing ringed comparison lemmas used here. Whole-blueprint searches for pullback tensor, scalar pullback and tensor coherence found no alternative blueprint statement of this item; the general tools and the neighboring projection formula statements are not duplicates of this specified coefficient-square assertion. `blueprint.same_as` remains empty. The nearest blueprint ancestor is `det-thm-sfb-proper-base-change-integral`, paragraph (3), through `lem-sfb-integral-quotient-projection-comparison`.

## Review by NU

I read the chapter and unit records, the current blueprint's integral proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.proof.md`, and the coefficient-morphism and pullback-from-point unit texts. The unit route is unchanged: this is the canonical-map compatibility needed in its integral step, not an alternate proper-base-change theorem. I read Stacks `sites-cohomology.tex`, Tags 06YS (lemma-K-flat-resolution), 0G7D (lemma-factor-through-K-flat), 07A2 (lemma-tensor-product-K-flat), 06YU (definition-derived-tor and its preceding localization construction), 0G7E (lemma-pullback-K-flat), 06YY (lemma-derived-base-change), 0D6D (lemma-derived-pullback-composition), and 07A4 (lemma-pullback-tensor-product), and `sites-modules.tex`, Tag 03EL (lemma-tensor-product-pullback). The additional internal/section normalization is taken from the existing node's statement, not attributed to a single Stacks theorem. The proof is honestly marked agent-written because I supplied the explicit square calculation.

In step 1 I read `def-sfb-integral-quotient-coefficients`: it defines the actual condensed quotient by postcomposition and pulls it to each site. I read `sk-def-sfb-coefficient-morphisms`: alpha is the component of one natural isomorphism. Naturality at that quotient gives the displayed structural-ring equation, including its direction. No interchange of inverse image with the integral inverse limit is used. This is the only elementary step.

In step 2 I read the full statement of `lem-sfb-quotient-section-tensor-normalization`. It supplies the fixed internal/section equivalences, the action on scalar extension, b's balancing formula, the actual pullback tensor maps, and the specified lambda's formula as identifications of natural transformations in unbounded categories. It says more than an existence of isomorphic objects, which is essential here. Its small-site conventions apply to the schemes of this item, and it imposes neither boundedness nor flatness of the quotient.

In step 3 I checked the statements of `lem-pc-kflat-resolution`, `lem-pur-kflat-total-tensor-model`, `lem-weil-pbc-ringed-pullback-preserves-kflat`, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. They respectively give flat-term K-flat representatives of arbitrary complexes, a flat-term K-flat tensor total, preservation of that same resolving class by every ringed pullback, and computation of derived pullback/tensor on those models. In particular the preservation statement has no flatness condition on the structural ring map: it applies to the identity-topos quotient edges. I never treated ordinary scalar extension as exact on arbitrary complexes.

In step 4 I checked `lem-sfb-ringed-derived-monoidal-comparisons`: it gives canonical composition comparisons computed by ordinary module pullback on flat-term K-flat complexes, and induced comparisons for a specified geometric 2-isomorphism commuting with ring maps. Step 1 verifies precisely that structural-ring hypothesis. I give the direction chi = c_B h c_A^{-1}, describe both routes' common balanced module, and compare its actual generator formula with the lambda formula in `lem-sfb-quotient-section-tensor-normalization`. Equality on every resolving representative extends to every object by naturality and an isomorphism from a resolution. I use none of the general node's unneeded projection or direct-image conclusions.

In step 5 the normalization node again supplies the formulas for b, t and lambda. I checked `def-weil-pbc-ringed-tensor-section-calculus`: its actual sheaf pure tensors commute with restrictions and determine linear maps; it also specifies scalar-extension units. I compute both routes on a local source generator, including an arbitrary outer S_X scalar a. They both send it to (p-tilde tensor 1) tensor (q-tilde tensor a s'). I corrected an intermediate notation in the first draft: lambda acts first on the unsplit tensor, and D_X(t_R) then splits it. No claim that global sections generate a sheaf is used.

In step 6 the total-model node supplies direct-sum totals even for doubly unbounded inputs. I checked that all comparison maps are degree zero and never interchange p and q, so the two differentials have the same (-1)^i factor. `lem-weil-pbc-site-derived-tensor-descent` explicitly states uniqueness of natural transformations after restriction in both variables to flat-term K-flat representatives. It therefore supplies precisely the descent of the equality, rather than merely existence of individual resolutions. Finally the normalization node identifies the resulting maps back in the internal category. I checked source and target of each composite against the displayed equation in the item.

I tested f = identity (the calculation reduces to the same scalar balancing map), a zero input, n = 1, and nonzero inputs shifted into odd degrees. In the odd case there is no variable swap and hence no extra sign. The test A = Z_l with quotient A/(l) is nonflat, yet the argument still only uses resolutions over A followed by scalar extension in the flat-term K-flat resolving class over the quotient. This confirms that neither flatness nor a vanishing Tor assumption entered the proof. Arbitrary doubly unbounded complexes use direct sums in each total degree; no infinite-product total or convergence assumption is hidden.

I checked delivery-errors B through E: all objects in the statement remain introduced with their original hypotheses; no unsplit new node or duplicate was made; every non-elementary input is a cited statement, not an internal proof detail; citations.json quotes are literal substrings; the proof-dependency list is exactly the union of uses. Generic off-unit tools are explained in split_report.tool_uses, with no change of unit route. None of the six steps exceeds 2000 characters, and I found no hidden independent lemma in them. The candidate dependencies do not lead back to this item. The server review_split check passed before this report was written.

## Unfinished work

None in this one-level stage-1 split. Existing cited nodes retain their own proof status; no Lean was written and no compiler, Lake or build command was run. Full delivery preflight and push follow this report.
