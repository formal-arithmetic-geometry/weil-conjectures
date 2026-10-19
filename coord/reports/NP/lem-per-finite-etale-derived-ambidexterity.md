## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-etale-derived-ambidexterity.json`: statement, split into seven proof steps; no Mathlib match for the entire assertion.
- `citations.json`: 27 verbatim statement quotations for the seven steps.
- `searches.jsonl`: actual Mathlib searches retained, with their returned results.

No new DAG nodes or Mathlib leaves. The item is not its unit's key node, so the unit record is unchanged. No Lean was written or compiled, and no live repository or launcher file was modified.

## Attachments

No new attachment. Searches of `WeilConjectures/` by the exact blueprint tag and by finite-etale/trace/adjunction/ambidexterity concepts found no declaration giving the whole item. The existing sheaf shriek-to-star theorem `AlgebraicGeometry.Etale.isIso_etaleLowerShriekToLowerStar` was read in `SixFunctors/Etale/UpperLowerStar/FiniteEtale.lean:682`; it gives a sheaf comparison, not the item's derived trace and orientation assertions. Its existing DAG node is reused. The mirror does not contain the later `AlgebraicGeometry/FiniteEtaleModuleTraceDegree.lean` recorded in the live DAG; this split does not propose a new attachment from that record.

## Literature wanted

None. I read ILO, Expose XVI, Lemma 3.5.10 and proof, printed page 250 (PDF page 256), and the preceding Lemma 3.5.8 explaining tensor extension of the transpose. I read Stacks `etale-cohomology.tex`, Tag 03SH (`section-trace-method`), Definition 03SE (`definition-trace-map`), Tags 03S3/03S5/03S7 (extension by zero, exactness, and finite-etale shriek equals star), the graph construction in Tag 0F4L; `etale.tex`, Tag 04HN (`lemma-finite-etale-etale-local`); `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`) and Tag 09T5 (`lemma-derived-adjoint-functors`); and `sites-modules.tex`, `lemma-extension-by-zero` and its proof. For the derived normalization I also read Mathlib `CategoryTheory/Localization/Adjunction.lean:89,118,125`. The dimension-zero comparison follows the existing normalization statement and the current main-20261015 smooth-purity proof; no SGA source is used.

## Findings and corrections

The statement is preserved verbatim, as are its five statement dependencies. No statement dispute was found. The imported item had no proof. The split now specifies both adjunctions, their actual maps on representatives, the ordinary compact-support comparison, and the normalization of the Gysin map.

The degree computation is an equality of sheaf maps in each degree before localization. One must not infer equality of arbitrary derived morphisms merely because their etale pullbacks agree. Likewise sheafification of a sum presheaf is not computed by taking that raw sum on every disconnected test object; Step 2 uses its universal property and the sheaf condition instead.

The whole-DAG searches by 04HN, 03SH, 03SE, finite-etale splitting, shriek/star and derived adjunction, together with `blueprint_refs.py search 'finite etale'`, `'ambidexterity'` and `'trace degree'`, found all needed ingredients already present. `prop-exc-finite-etale-adjoint` is on pro-etale sites and is deliberately not substituted for this ordinary-etale assertion. The existing module trace-degree existence lemma alone does not identify its existential map with this specified adjunction counit, so the proof does not use it for that identification. Blueprint ancestry was checked with `blueprint_refs.py ancestor` and its current Step 3 was read. Existing `blueprint.from` is already precise and is retained; no equivalent blueprint node was found.

Mathlib searches used the prescribed `msearch.py` command: all four kinds ran successfully, followed by a second semantic phrasing. Their hits concern structural O-module sheaves, general site adjunctions or Dold-Kan summands. The structural-sheaf adjunction signatures in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` and the generic localization adjunction were inspected: none states this finite-etale ordinary-derived trace/orientation theorem. Existing searches in the imported node remain intact.

## Not duplicates

No new node is proposed. The elementary split-cover sums, finite-product identification with a finite sum, restriction as diagonal, and degree multiplication are proof steps, not new nodes.

## Unfinished work

None in the one-level split. Existing unsplit dependencies retain their own work; this delivery does not change their statements or claim they are proved in Lean.

## Review by NP

I checked the item against ILO XVI 3.5.10, which explicitly concerns every object of ordinary D+ and both canonical adjunctions. The sheaf exactness and trace normalizations are exactly the ones in Stacks 03S3, 03S5, 03S7 and 03SH. Unlike the surrounding proper-degree descent proposition, this lemma does not need the degree invertible. The additional orientation clause is supplied by the existing diagonal/deformation normalization, with n=1, on Noetherian schemes; it is not an appeal to a pro-etale or constructible theorem.

Step 1 uses the full constant-ring module assertion of `prop-weil-pbc-inverse-image-modules-exact`, the exact left adjoint explicitly stated in `lem-weil-pbc-etale-restriction-injectives`, and the natural isomorphism explicitly stated in `lem-weil-pbc-etale-shriek-star-finite-modules`. These statements suffice to transport the adjunction and exactness; no stalk exactness theorem is silently used.

Step 2 uses the defining sum-extension presheaf, the inverse-image restriction statement, module sheafification's stated universal property, the canonical shriek-to-star map's stated graph formula, and the stated split-product isomorphism. The counit is computed by transposing the identity: each summand evaluation is the identity, and the graph map puts it in its own factor. This is a direct universal-property calculation, marked elementary. I checked that the graph formula occurs in the cited definition's statement, not just its proof.

Step 3 uses the termwise-adjunction node, including its unit/counit and bounded-below clauses; the exact-factorization node, which actually provides quasi-isomorphism preservation and termwise representatives; the exact-derived-functor node, which actually identifies these with RF on D+; and the localization-adjunction node, whose statement actually gives the unit and counit formulas. Thus both triangle identities and the prescribed maps survive localization. The general derived-adjoint theorem by itself would not fix the maps as explicitly.

Step 4 uses the pointwise etale-local splitting statement, the inverse-image node's explicit formula for the unit, the split-product isomorphism, and the trace-existence node's naturality, localization and split-sum clauses. It derives the diagonal and identifies the counit with that trace. A-linear means F_ell-linear here, so additivity suffices. I did not use a trace-existence statement for arbitrary R to infer uniqueness it does not state.

Step 5 uses finite implies proper and the proper definition to check separatedness and finite type. The identity/proper compactification is admissible between the given Noetherian schemes. `def-amb-etale-compact-support` actually defines its functor as Rr_*Dj_!, and the exceptional-adjoint theorem supplies the ambient right adjoint for finite A. `det-sp-unique-right-adjoint` explicitly supplies the unique counit-compatible comparison. The support-map compatibility node's graph and degreewise normalization agrees with the canonical sheaf comparison in this particular compactification; no arbitrary compactification comparison is assumed.

Step 6 checks every hypothesis of `lem-pur-finite-smooth-gamma-normalization`: n=1, invertibility of ell, Noetherian source and target, etale, separated, finite type and compactifiable. Its conclusion explicitly says that the tensor map's adjoint is the sum/evaluation counit. The ordinary-smooth-orientation node explicitly identifies its dimension-zero case with etale inverse image. Together with uniqueness of the counit-compatible comparison these prove both the identity normalization of g_f and its tensor extension. This is a pre-existing general orientation normalization, not a new node restating a clause of this item.

Step 7 uses the actual splitting statement, computes sum after diagonal on each module sheaf, and glues equality of sheaf maps. Passing equal chain maps to localization is elementary; equality after derived etale pullback is never used. Small cases checked: the empty finite cover (d=0), identity cover (d=1), the disjoint ell-fold cover (composite zero in F_ell), a non-surjective finite etale clopen immersion with varying local degree before the final constant-degree hypothesis, and disconnected bases. Zero sheaves and shifted or unbounded-above bounded-below complexes cause no exception. No field, regularity, excellence, perfection, connectedness or constructibility assumption was added.

All 22 cited node statements were opened. Each citation in `citations.json` is copied from the cited statement; incomplete snippets were expanded during self-review. All non-elementary inputs are cited. No new node needs source, definition or duplicate repair. Every proof step is below 2000 characters, so none hides a long separate comparison argument. Off-unit generic tools are declared in `split_report.tool_uses`; the unit's route is unchanged. The changes are a full seven-step proof of the item, not a relocation into a new lemma.
