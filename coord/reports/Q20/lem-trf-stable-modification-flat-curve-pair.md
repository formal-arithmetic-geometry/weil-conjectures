# Stage-1 report: lem-trf-stable-modification-flat-curve-pair

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-stable-modification-flat-curve-pair.json`: repaired split, seven proof steps; no Mathlib match; item statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-temkin-stable-modification.json`: retained statement-only external theorem input, with the missing marking morphism and its generic isomorphism supplied; no Mathlib match.
- `citations.json`: regenerated verbatim statement citations for all 23 uses in the seven steps.
- `report.md`: retained findings from the first delivery, updated with this repair and its mathematical review.

## Attachments

None. The earlier search by item id and stable-modification terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` was repeated during repair (including Temkin and multipointed); no project declaration states this item. The upstream master is reference material only. No Lean code was written and no compiler, Lake or build was invoked.

## WANTED:

- WANTED: Temkin, *Stable modification of relative curves* (2010), §1.2 and Theorems 1.1 and 1.5, for `lem-trf-temkin-stable-modification` and the item: an archival copy in `literature/` is still absent. I read those passages online at [the author's paper](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf) during this repair, without writing a download. The local source remains ILO Exposé X §3.2.2 and Theorem 3.4 Step 3. The item's proof remains marked agent-origin for its added refinement arguments.

## Not duplicates

- `lem-trf-temkin-stable-modification` vs `lem-trf-dejong-relative-marked-semistable`: the latter assumes a proper integral total space and gives the larger alteration square, a Cartier divisor and an exceptional base subset; the new input is the flat multipointed-curve theorem, allowing nonproper and nonseparated curves. It is used in the parent's step 6 through this item, so citing the parent instead would be circular.
- `lem-trf-temkin-stable-modification` vs `lem-trf-flatification-horizontal-curve-pair`: the latter flatifies an already projective generic curve and horizontal marking; it does not create semistable fibres.
- `lem-trf-temkin-stable-modification` vs `lem-trf-stein-smooth-generic-curve`: the latter constructs a finite Stein base with geometrically connected fibres; it makes no semistable modification or marking.
- `lem-trf-stable-modification-flat-curve-pair` vs `lem-trf-alteration-finite-refinement`: the latter is only a refinement of alteration bases, not a modification of a marked curve.

Whole-DAG searches for Temkin, stable modification and semistable multipointed, and `tools/blueprint_refs.py search` for Temkin, stable modification and multipointed, found no existing blueprint theorem replacing the new input. The ancestor is still `lem-trf-local-term-locality`. No additional node was created in the repair: the new dependencies are existing generic tool statements, declared in `split_report.tool_uses`.

## What was wrong or incomplete

The imported item had no proof. The first delivery supplied Temkin's input and a Chow refinement but had the four faults in the return at head `723fc2864e`. I retained its statement, blueprint ancestry, source route and recorded searches, comparing all inherited metadata against the current shared item; only the split fields differ from current main. The following are substantive repairs, not an unchanged rebase.

1. **C4/E4:** the external input now supplies `d: H̃ → H ×_S S̃`, the equality making it a morphism of pairs, and the generic-fibre isomorphism of `d`. Properness of the curve modification is explicit as well. An arbitrary empty marking can no longer satisfy the node when the input generic marking is nonempty. These clauses are exactly the content of Temkin's definition of a modification of multipointed curves and of an eta-modification, not an assertion about an unrelated closed subscheme.
2. **E3:** step 4 first proves `r` proper by proper closed immersion and composition. Projective space is proper, hence separated over `S`; `lem-weil-pbc-proper-over-separated` makes the immersion into it proper, and `lem-weil-pbc-proper-immersion-closed` makes that immersion closed. Only then is `def-kun-projective` applied.
3. **E1:** steps 2–3 use the schematic image of `W = π⁻¹(V) → T`, not `lem-chow-scheme-theoretic-closure`. The latter requires ambient density, which Chow does not supply. The kernel theorem gives the closed image and `lemma-nagata-immersion-open-in-scheme-image` gives density in that image. The affine kernel-to-domain argument proves integrality without asserting density in `T`. Over `V` the closed image contains the whole open `W`, so the restriction is the original isomorphism.
4. **C1:** step 6 cites `lemma-nagata-relative-proj-base-change-arbitrary` for the Proj comparison and `lem-weil-pbc-proper-fp-permanence`(b) for the pulled-back closed immersion. It writes the symmetric-algebra identification by its universal property and checks finite generation after pullback. It also applies the properness base-change clause to the proper `b` rather than silently inferring properness from a definition of projectivity.

The additional requests are addressed in step 5: the finite generic fibre of the integral alteration base is one point, so the closed image `a(S̃ ∖ V)` avoids the generic point. Removing it from an open where `a` is finite makes `q` an isomorphism over the entire preimage and proves `r` finite there. Step 6 corrects the marking target to `H ×_S S′` and keeps the curve map's target `C ×_S S′`.

No dispute of the item statement is needed. The open applicability risk was resolved by reading Temkin §1.2: its definition explicitly permits curves without separatedness, and Theorem 1.5 applies to multipointed curves with semistable generic fibre. Theorem 1.1 supplies projectivity of the stable curve modification. I did not extrapolate the stronger general input just from ILO's quasi-projective special application.

## What I could not finish

The only remaining source acquisition request is the archival Temkin copy above. Stage 1 deliberately leaves the external theorem as one unsplit statement-only node. There are no new Mathlib leaves. The required server preflight is the delivery gate; no local DAG-check scripts were run.

## Review by Q20

I read the retained delivery, the current shared item, the return, `sk-i-curve-zero`, the trace-formula chapter and parent `lem-trf-dejong-relative-marked-semistable` step 6. I read ILO printed pp. 158 and 160–161 (§3.2.2 and Theorem 3.4 Steps 1–7), Stacks 0200 (`coherent.tex`, `lemma-chow-Noetherian`), 01R8 (`morphisms.tex`, `lemma-quasi-compact-scheme-theoretic-image`), 01W6 (`lemma-image-proper-scheme-closed`) and 01IQ (`schemes.tex`, `lemma-immersion-when-closed`). I also read the existing arbitrary relative-Proj base-change statement, its blueprint chart argument, and Stacks 01O3 (`constructions.tex`, `lemma-relative-proj-base-change`). All statements used below were opened in full; citations.json copies their actual text.

For the sole new node I checked the integral excellent Noetherian base, finite presentation and flatness of both maps, pure relative dimensions 1 and 0, the closed immersion, and the generic smoothness and etaleness against Temkin's multipointed-curve definition. These hypotheses make the generic pair semistable. Temkin's eta-modification includes both the curve and marking maps, and their generic isomorphisms; Theorem 1.1 supplies projectivity of the stable curve map. ILO supplies the compatible semistable form and base-change statement. Excellence and Noetherianity of the alteration base are compatible with finite type over the given base. The new node has no proof or proof dependencies. It is a general external input with a proper alteration base, whereas the item still has to construct the finite-projective-space refinement, prove that refinement integral, and pull back the projective-bundle factorization. The repair does not turn the item into an application of a restated identical node.

Step 1 takes the pair and generic isomorphisms from the repaired Temkin node. Unlike the returned split, it can point to an explicit commuting marking map in that statement. The source imposes no properness or separatedness hypothesis on the curve, so the item's nonproper cases are included.

Step 2 takes exactly proper surjectivity, an immersion and an isomorphism over some dense base open from Chow; it takes no density assertion about its inverse image in `T`. The proper-composition and finite-type-over-Noetherian statements make `T` Noetherian, so that open immersion is quasi-compact. The schematic-image kernel node supplies a closed subscheme; the immersion-to-image node supplies a dense open immersion into that closed subscheme. Step 3 uses exactly that affine kernel formula: a nonempty open in the integral `V` has domain sections, so the affine image rings are domains. This is an elementary ring argument from the cited formula and the definition of integral scheme, not an additional external lemma. It also verifies the isomorphism over `V` scheme-theoretically, rather than from a set-theoretic containment.

Step 4 takes properness of closed immersions and composition, composition of immersions, properness of projective space, proper-over-separated, and proper-immersion-closed from their respective statements. Thus the projectivity definition receives a closed immersion, as it requires. The finite-type and excellence tools concern schemes over a Noetherian base and finite-type affine algebras over excellent rings respectively; the hypotheses hold on the chosen affine charts. No global affine hypothesis on `S` is used.

Step 5 uses the already constructed integral `S′` and the generic isomorphism of `q`, plus the definition that proper maps are closed. The finite algebra over the generic field is a domain and hence a field. Since `a⁻¹(η)` has that one point, the image of the complement of `V` cannot contain `η`. This justifies the common dense open, rather than assuming two unspecified generic conditions compose. This step is elementary from the finite-over-an-open convention and those supplied facts.

Step 6 takes the semistable family and its base-change stability from the repaired input, the pair of induced maps from the fibre-product universal property, and the projective-bundle factorization from its definition. The Proj node allows an arbitrary base morphism, so no flatness of `q` is assumed. Its coefficientwise pullback applies to the symmetric graded algebra; the universal property identifies the pulled-back symmetric algebra with that on the pulled-back generators. The permanence node explicitly preserves both closed immersions and proper maps under base change. The generic fibre of `q` is an isomorphism since it is already an isomorphism over `V`.

Step 7 checks properness of the marking map rather than assuming it. Pull back the proper curve map to `H ×_S S′`, then factor the marking through that closed fibre product. On affine pieces the ideal containment gives a surjection of quotient rings, so that factor is a closed immersion. The closed-immersion definition and the proper permanence statement give precisely the two facts used here.

For edge cases I checked the empty marking, the identity modification of an already smooth pair, a nonempty generic marking (which rules out the old spurious empty output), and a Chow model with extra components disjoint from `W` (which the schematic image discards). None requires the marking to be finite over the whole base. The finite-open argument also works when the base itself is a field. All seven proof steps have fewer than 2000 characters; no long step hides an additional lemma.

The earlier eight Mathlib search records and their log were retained and read. Since the marking clause changed, I also ran and read new LeanFinder, LeanSearch, Loogle and grep searches on that question. The search hits concern flatness/smoothness and their preservation, or bicategorical modifications, and supply no existence theorem for marked curves. The malformed two-string Loogle query is recorded as invalid, not as evidence of absence, and was followed by a valid single-name search. The earlier result name for the etale postcomposition-property hit was corrected to agree with its saved log. Every recorded query ran. No SGA source or live-project mutation was used.
