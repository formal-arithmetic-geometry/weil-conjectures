## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-localizing-exceptional-bounded.json`: split into seven proof steps; no Mathlib match.
- No new nodes and no new Mathlib leaves. `citations.json` contains a verbatim statement quotation for each of the 24 step citations. `searches.jsonl` records five searches actually run. Both are sandbox evidence.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the item tag, the recorded declaration name, and localizing/right-adjoint boundedness terms. No exact finished declaration was found. Its ordinary pro-étale `Derived/UpperShriek.lean` concerns transported finite-coefficient exceptional functors, not this condensed adic localizing adjunction. The master's recorded adic interfaces are reference material, not completed proofs.

## WANTED

None for this split. The coefficient-specific bridge lemmas already exist in the DAG; their obligations are retained and cited rather than represented as consequences of a definition or of a literature passage that does not prove them.

## Statement corrected

STATEMENT-DISPUTED: the original shorthand says only that the characteristic differs from ell, but then says “as in” the parent. The parent's statement and the standing-setting definition explicitly require positive characteristic. At k = Q the explicit shorthand holds but the positive-characteristic hypothesis needed to instantiate those interfaces does not. I made that inherited positive-characteristic requirement explicit, matching the parent and source; I am not claiming the characteristic-zero assertion is false. I expanded the ambient categories and the supplied adjunction rather than referring to the parent statement (which depends on this item). No target statement or definition was changed.

The returned delivery identified a coefficient mismatch: `def-sfb-adic-coefficient-certificate` calls its third case all continuous maps into `Qbar`, while the blueprint and this item use the finite-subextension-valued ring of `sk-def-sfb-qlbar-condensed`. I repaired the item consistently by removing that certificate dependency and stating the three source coefficient rings directly, with finite `E/Q_ell` and the finite-subextension condition explicit. The read-only master `CategoryTheory/RingObjects/Condensed/EllAdic.lean:157–164` likewise defines the algebraic-closure coefficient by finite-intermediate-field-valued sections. This is not an identification with all norm-continuous maps: on the profinite convergent sequence S = {infinity} union N, choose nonzero alpha_n in finite extensions of unbounded degrees, scale them by rational ell-powers to tend to zero, send n to the scaled alpha_n and infinity to zero. This map is continuous but its image is contained in no finite extension. The item now cites only the two direct coefficient definitions, so every hypothesis used in its proof matches its stated coefficient.

## Problems repaired

The original single sentence, “finite affine factorization ... give a common finite cohomological interval”, did not compare the supplied G with the adjoints appearing in the restriction theorems, did not match their categories, and did not give the claimed bounds. The replacement exposes both comparisons, uses the existing rational and integral restriction statements, and extracts the bounds only after the comparison is established.

The general ring-object constructibility predicate is not the scalar-constant predicate by definition. Rational local-freeness bridge statements and the existing integral lfp/constant-model comparison supply this missing implication. In particular I did not infer it just from the Tor-amplitude equality node.

The existing `blueprint.from.node` named a non-blueprint stage-3 child. I repaired the worker-owned `from` field to the actual imported ancestor already named by the parent's provenance, `lem-sfb-dc-proper-pushforward-left-adjoint-e`, with the intermediate parent in `via`. The ancestor script follows immutable `created.item` into stage-3 module names and prints None for this item, so it cannot recover this provenance mechanically. I retained `created`, `lean`, reviews, chapter and unit unchanged. The proof follows the common existence/restriction route for all three adic examples; it does not use the stale external-source entries attached to the imported ancestor.

## Unfinished work

No missing step of this one-level split. Existing cited lemmas retain their own stage-1/proof obligations. No Lean was written, compiled, or built.

## Not duplicates

No new nodes. Whole-DAG searches for localizing adjoints, finite-constant versus locally finitely presented modules, and coefficient restriction found the existing integral comparison and rational bridge nodes, which are reused. Blueprint-wide searches (`right adjoint`, `bounded adjoint`, `cohomological boundedness`) found broader restriction/preservation statements, not a second node stating this arbitrary-supplied-adjoint boundedness component. Those broader results are cited instead of duplicated.

## Review by N6

I read the chapter and unit records, the current main-20261015 `det-existence-restriction.proof.md` rational/integral bullets, both restriction theorem statements, the proper comparison statement and proof, and the localizing-closure and constructibility definitions. The proof origin is agent: it expands that blueprint route, rather than claiming a human source contains the whole supplied-adjoint argument. I also read Bhatt–Scholze Definition 6.8.10 and Proposition 6.8.11 (printed pp. 60–61), Hemo–Richarz–Scholbach Example 3.1 and Theorem 6.2, and Stacks 01T6 (`lemma-finite-type-noetherian`). Those sources distinguish scalar local models from arbitrary finite presentations; the cited bridge nodes, not those passages alone, carry the additional comparisons.

Step 1 uses the direct coefficient definitions `sk-def-sfb-condensed-ring` and `sk-def-sfb-qlbar-condensed`, then the exact finite-type-over-Noetherian and qcqs-over-affine statements on Z and Y. The minimal-closed-subset statement supplies topological Noetherianity; the subspace ACC argument is written out. Spec k is Noetherian directly from its two ideals. This verifies the hypotheses of the coefficient bridges before they are invoked.

Step 2 uses the E and bounded-image Qbar local-triviality statements, each of which explicitly turns local finite cokernel presentations on a topologically Noetherian scheme into finite free local models. On each chosen stratum these are finite scalar-vector-space models. The converse is precisely the last assertion of `det-def-sfb-constructible-local-model`; the definition node supplies the finite stratification, not the bridge theorem. I checked the Qbar ring in the actual source, as described above.

Step 3 quotes the integral comparison's conditions (i) and (ii) on each of Z and Y. It allows arbitrary integral torsion and changes of stratification. I do not replace integral finitely presented modules by free modules or assume derived completeness.

Step 4 applies the preceding cohomology-module comparisons to arbitrary ambient complexes, then uses only clause (2) of the ctf/bc equality statement. Its qcqs hypothesis was proved in step 1. Equality of the two hulls is elementary from their intersection definitions after equality of the generators; the coproduct indexing universe is fixed to u+1 on both sides. This is the ordinary unbounded category on both sides, with no completed coproducts or completeness subcategory. Thus the input K and its full inclusions are the same objects for the restriction theorems.

Step 5 uses clause (1) alone of `det-cor-existence-ii-restriction` to compare compact-support and canonical proper direct image on the hull. It does not use that node's stronger preservation clause. `sk-prop-sf-existence` supplies the reference adjunction; `sk-thm-restriction` gives preservation in the two rational cases. In the integral case `det-prop-int-brown-adjoint` explicitly identifies its adjoint with that reference adjoint, and `sk-thm-int-restriction` supplies preservation. All are in the same positive-characteristic standing setting; properness gives the separated finite-type hypothesis. These are existing finer route results, not new nodes restating a clause of this item.

Step 6 writes the Hom-bijection transport with its inverse and invokes the exact statement of `det-sp-unique-right-adjoint`, a Mathlib leaf. I read Mathlib `CategoryTheory/Adjunction/Unique.lean:102–130`: `rightAdjointUniq` gives the isomorphism and the following theorems give its transpose/counit formula. This comparison is on the whole hull; testing merely against bounded constructibles would not suffice. Applying the full inclusion needs no new comparison lemma.

Step 7 uses the definition of ctf as a subcategory of bounded constructibles to choose a finite interval for H(K). A homology functor sends an isomorphism to an isomorphism by applying it to the two inverse identities, and being a zero object transfers across that isomorphism. These elementary details are written out. The interval is allowed to depend on g, K and the coefficient; no uniform bound absent from the theorem is claimed.

For small cases I checked the identity morphism (a supplied right adjoint is isomorphic to identity), K = 0, the empty source (the zero derived category), degree shifts, and integral torsion such as O_E/ell in degree zero. None is excluded or incorrectly declared locally free in the integral argument. The proof does not use finite base-field cohomological dimension, perfection of k, or a fixed algebraic closure of a finite field.

Against delivery-errors B–E: there are no new statement-only nodes to audit; each cited statement was opened and quoted verbatim in `citations.json`; neither a definition nor the proof of another node is used as a substitute for a theorem statement. The argument retains the unit's restriction route and declares the comparison/Noetherianity tools from other units in `split_report.tool_uses`. It cites no SGA source. Every step is under 2000 characters and contains no separately hidden comparison: the non-elementary comparisons are the cited existing nodes. I corrected the initially tempting identification of the two constructibility predicates before writing the final proof. The tool checks and dry run are recorded below once completed.

Validation: the server `review_split` check passed with zero new nodes. The full `deliver.py --no-push` invocation exited 0 and printed `OK (not pushed)` with preflight passed; the final receipt is recorded by the delivery tool. Its independent DAG/preflight checks introduced no blocking finding. The route diagnostics record the rational/integral restriction interfaces; these are exactly the two bullets in the current unit's cited existence theorem, not a replacement route. The final delivery is rechecked after this validation note.
