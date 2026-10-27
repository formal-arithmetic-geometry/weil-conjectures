# Stage-1 report: lem-sfb-supported-valuation-finite-elements-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-valuation-finite-elements-model.json`: statement, split into eight explicit steps; not a Mathlib match. Statement and statement dependencies unchanged.
- `citations.json`: 20 entries, one for each step/node citation, with literal statement text.
- `report.md`: this report. No new DAG nodes; no new Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and supported/valuation/finite-elements terminology, and inspected the blowup directory's relevant vocabulary. No declaration states this supported valuation-model construction. The scattered hits concern unrelated valuation/module facts or admissible blowup operations, not the item's quantified conclusion.

## WANTED

None for this item. All inputs are available in the local Stacks sources. No SGA source is used. The parent's Milne reference is motivation only: this item has an independent agent-written construction from the Stacks blowup and ideal-extension lemmas.

## What was wrong or incomplete

The live item was statement-only. It needed the supported denominator argument: blowing up just `(b,a_i)` would generally modify points outside the prescribed closed boundary. Adding `J^N` repairs that construction while preserving the chosen valuation chart. No error in the statement was found, and no hypothesis or conclusion was changed.

The source list includes Tag 0806, but the proof does not need its universal property: the inclusion `A[I/b]` into `R` constructs the lift explicitly. This also identifies the actual center and the images of the given elements, rather than relying on an unspecified lift.

`blueprint_refs.py ancestor` reports `blueprint.from.node = None`, matching the existing item. I preserved the inherited null ancestor and its entire via chain rather than inventing a blueprint node. The whole-blueprint searches `valuation`, `blowing up`, and `finite elements` found no exact imported statement for the item. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md`, the current `sk-thm-sf-ctf-stability/_section.md` and its proof, alongside the chapter/unit records. This algebraic-geometric tool remains below the existing open-image finiteness branch; it does not replace a six-functor unit step. The unit record's older chapter association/text differs from latest, but changing those records is outside this non-key item's scope.

## Proof and source checks

I read `divisors.tex` Tags 0804 (lemma-blowing-up-affine), 0806 (lemma-universal-property-blowing-up), 02ND (lemma-blow-up-integral-scheme), 02NS (lemma-blowing-up-projective), and 080M (lemma-extend-admissible-blowups), including the proof of 080M. I also read `properties.tex` Tags 01OW/01OY/01OZ (Noetherian affine rings, quasi-separatedness and Noetherian topology), 01PB (lemma-finite-type-module), and 01PF (lemma-extend); `algebra.tex` Tag 00PD (lemma-characterize-dvr), its final unit-times-power assertion and proof; `schemes.tex` Tag 01HV (lemma-spec-sheaves); and `morphisms.tex` Tags 01QO (lemma-closed-immersion) and 01RV (lemma-integral-scheme-rational-functions). The proof is marked agent-written because the supported finite-elements consequence is not a verbatim Stacks lemma.

## Review by NR

I checked delivery-errors B–E against the node and these sources. There are no new statement-only nodes to audit, and none of the item's clauses was hidden in a new node. The item carries the actual common denominator, the supported ideal and its valuation calculation, the globalization, the affine chart and the local-ring inclusion. All eight steps are under 1000 characters, so none reaches the long-step review threshold. I read every cited node's statement, not merely its proof or title, and citations.json copies those statements verbatim.

Step 1 uses exactly the affine function-field fraction statement (`lem-sc-integral-function-field-affine-fraction`), Noetherianity of affine opens (`pqf-lem-affine-open-locnoeth`), locally Noetherian quasi-separatedness, and Noetherianity/quasi-compactness of open subschemes. These give respectively `A` inside `K`, Noetherian `A`, qcqs `X`, and quasi-compact `U`. The factorization of `c` through `V` is written out using specialization to the maximal ideal; no separatedness of `X` is assumed.

Step 2 uses only the definition of a Noetherian ring for finite generation of `J`. The previous fraction-field identification supplies the common denominator. I checked explicitly `a_i=b h_i`, `b` nonzero, `J` nonzero, and `J R` contained in the maximal ideal. In particular `Z` proper matters: it excludes the generic point, so `V(J)` is not all of `V`. This step is elementary, with its ring calculations written out.

Step 3 cites the DVR definition and the exact unit-times-uniformizer-power theorem. The definition supplies a uniformizer and the equivalent Noetherian-local-domain hypothesis of that theorem; the theorem supplies the exponent of the particular nonzero `b`. Taking `N=max(1,e)` really gives `J^N R` contained in `bR`, even when `e=0`. This avoids an uncited assertion about arbitrary valuations being Archimedean.

Step 4 uses the closed immersion definition's affine criterion and the ideal-sheaf definition to obtain the actual quasi-coherent ideal sheaf `~I` of Spec(A/I), and the affine finite-type equivalence to obtain its finite type. Each cited statement says that, and no global ideal extension is assumed yet. The products of the chosen generators explicitly prove finite generation. The equality `IR=bR` follows in both directions: every generator maps into `bR`, and `b` itself is a generator. The inclusion `J^N` in `I` shows the center is supported in `Z`.

Step 5 cites the precise finite-type-ideal gluing statement and the precise extension-existence statement. I checked all their hypotheses: the three opens `U`, `V`, `U union V` are quasi-compact, `X` is qcqs, and the two ideals agree as the unit ideal on the overlap. These are the actual hypotheses of the proof of Stacks 080M. The resulting extended ideal is nonzero on `V`; no unproved normality or excellence is needed.

Step 6 cites the blowup definition, the integral blowup geometry statement, blowup properness and the complement isomorphism theorem. The integral geometry lemma requires a nonzero finite-type quasi-coherent ideal, all supplied by Steps 4–5; its statement actually includes integrality. Properness is cited separately, not inferred from an ambiguous definition of projective morphism. Since the extended ideal is the unit ideal on `U`, the complement isomorphism restricts to all of `U`. Nonempty opens of integral schemes are dense, so the asserted birationality follows without a new lemma.

Step 7 uses the chart-density statement for the actual open-chart identification `Spec A[I/b]`, the chart-ring definition for its generators, and the affine-spectrum definition for the ring-map-to-morphism construction. The first cited statement applies to the global nonzero finite-type ideal and its restriction, and allows a generating list beginning with the nonzero `b`. I checked the inclusion into `R` on every generator `i/b`, not merely on the `a_i/b`. The equation `g c_1=c` is checked on the common coordinate ring `A`.

Step 8 uses exactly the affine stalk-localization clause of `lem-weil-pbc-spec-domain-stalks-function-field`. At `q=B intersection m_R`, every denominator outside `q` is a unit in `R`, so the displayed stalk map is both injective and local. All embeddings are the same embeddings into `K`, and `A subset B subset Frac(A)` gives `Frac(B)=K`; this verifies the specified identity of generic maps, as well as every membership of `h_i`. No uniqueness theorem for valuation lifts is required.

I tested the empty list (`b=1`, `I=A` locally), zero elements, elements already in `A`, unit denominators, and a center ideal which becomes principal. I also checked a genuine denominator example: on `Spec k[s,t]` with the divisor valuation of the blowup at `(s,t)`, take `h=t/s`, `J=(s,t)`, `b=s`, and `N=1`. Then `I=(s,t)` and the s-chart contains `t/s`, just as required. For `h=t^m/s^m`, one can take `b=s^m` and `N=m`, and all degree-m boundary monomials divide into `R` by `s^m`. The scheme may be nonseparated; the proof uses only qcqs ideal extension and relative properness. It never assumes intersections of affine opens are affine.

I checked dependency paths of all theorem inputs back to the item: none reaches it. I reused the same-unit `lem-sfb-integral-blowup-projective-geometry` and `lem-sfb-integral-blowup-chart-density`; there is no reason to create another 02ND/0804 node. The generic off-unit scheme/ring tools are declared in `split_report.tool_uses`, as required by the current brief. Definitions are used only for notions or their explicit stated equivalences.

## Not duplicates

No new nodes. Searches by tags 0804/0806/080M/02NS and blowup/affine/extension keywords found the existing inputs, all reused. Both `lem-sfb-integral-blowup-projective-geometry` and `lem-per-integral-blowup-projective-geometry` state the same integral blowup geometry; I used the same-unit sfb version and did not edit either. Neither states the finite-element supported consequence of this item.

## Mathlib searches

Preserved the imported item's searches and ran the required logged searches under NR with LeanFinder (two new phrasings, plus the original phrasing), Loogle, LeanSearch and source grep (blowup terminology and the specific Proj hit). All services answered. Read the candidate `AlgebraicGeometry.Proj.valuativeCriterion_existence_aux` in `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:200`: it assumes an existing graded ring and projective data; it does not construct a supported modification for specified rational functions. The other hits concern DVR characterizations, valuation membership and regular sequences, not this scheme construction. The item is not a Mathlib leaf. Every added search entry comes from searches.jsonl; no unrun search is claimed.

## Unfinished work

None in the natural-language split. Its cited nodes remain independent obligations of the project. No Lean was written, compiled or built; no repository or launcher file was changed, and no agents were started.

## Validation

The required `deliver.py NR lem-sfb-supported-valuation-finite-elements-model --no-push` exited successfully and printed `OK (not pushed)` at `76d43262770`, with server preflight passed. The final report update is followed by another dry run before the push. All sandbox JSON parses, every citation quote equals the cited statement, the proof-dependency list equals the union of the uses, and every step is shorter than 1000 characters.
