## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-nodal-etale-local-form.json`: statement item, now split in six steps, unchanged statement; inherited searches retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-dvr-principal-neighbourhood.json`: one new statement-only unsplit lemma, not a Mathlib leaf. It isolates the base-ring neighbourhood, without any curve or nodal hypothesis.
- `citations.json`: 19 verbatim statement quotations, one per step/cited-node pair. `searches.jsonl` records all new searches. These are sandbox evidence; the delivery packages the node files and this report.

## Attachments

None. Searching the entire read-only `lean/WeilConjectures/` for the blueprint tag, nodal and semistable terminology found no declaration proving the item. Hits were contextual comments in the derived Kunneth, dualizing, projection-formula and lisse-cover files. In particular no existing project proof supplies the nodal-family chart or the principal DVR neighbourhood.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## What was wrong or incomplete

The item had no proof. Its statement agrees with Stacks models.tex Tag 0CDD, `lemma-etale-local-at-worst-nodal`, without properness, excellence, completeness or connectedness assumptions. I preserved its statement and all existing metadata/searches. I checked the expanded geometric-fibre assumptions against curves.tex Tags 0C59/0C5A, `lemma-nodal-family` / `definition-nodal-family`, and the general chart at Tag 0CBY, `lemma-etale-local-structure-nodal-family`.

The closed-point convention in the item's hypotheses is slightly more explicit than the existing general chart's all-point convention. Step 1 supplies the justification: on finite-type affine pieces of reduced geometric curves, a nonclosed point is generic and is smooth by the existing generic-fibre smoothness lemma. Thus the general chart really applies; no extra completion hypothesis was added.

The inherited blueprint chain has a null `from.node`. `python3 tools/blueprint_refs.py ancestor lem-sfb-dvr-nodal-etale-local-form` itself returns `None`. I preserved that anchor and the named ancestor/place chain, appending the precise base-shrinking task on the new node. The chapter and unit were read, but neither was edited: this is a generic local-equation prerequisite of the inherited constructibility route, not a replacement of a unit step. Searches of the whole blueprint for `nodal`, `nodal local equations`, `Dedekind`, and `principal open discrete valuation` found no duplicate statement. The broader valuation search was also inspected; its imported coefficient and valuation statements do not state this neighbourhood lemma.

## Source error

The last paragraph of Tag 0CDD writes the change of coordinates as `u_new = epsilon u` after writing `h = epsilon pi^n`. Read as new coordinates in the old ring, this gives `u_new v = epsilon^2 pi^n`, not `pi^n`. For example in Q[[pi]] with epsilon=2 it gives 4 pi^n. Step 6 instead writes the actual inverse ring maps: `u_0 -> epsilon^{-1}u`, `v_0 -> v`, and inversely `u -> epsilon u_0`, `v -> v_0`. This corrects the proof's coordinate description and leaves its true statement unchanged.

The use of 0AP2 is restricted to a point above the closed point of a DVR. One must not claim that all maximal localizations of every etale DVR algebra are nonfield DVRs: the etale algebra R[1/pi] is a field. The new statement explicitly assumes contraction to the nonzero maximal ideal and makes no claim about this generic-only case.

## Mathlib and duplicate searches

The new lemma was searched with the prescribed msearch.py command: LeanFinder in two phrasings (principal open neighbourhood of a special-fibre point; localization in an etale algebra over a local Dedekind domain), Loogle `"IsDiscreteValuationRing", "Etale"`, LeanSearch for an affine open DVR neighbourhood of a special-fibre point, and two source greps. All services answered. The searches and actual result summaries are recorded exactly in the new node and `searches.jsonl`.

LeanFinder returned `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` and `IsDedekindDomainDvr.is_dvr_at_nonzero_prime`; I read Mathlib/RingTheory/DedekindDomain/Dvr.lean:128-136 and the grep lines at 60-61. They localize an already Dedekind domain at a nonzero prime, and do not construct a principal open in a possibly disconnected etale algebra over R. `Algebra.exists_etale_of_isEtaleAt` and the etale-locus results in RingTheory/Etale/Locus.lean spread etaleness, without the DVR/local conclusion; the ring-hom localization-span results have the same limitation. The other returned standard-etale, valuative-square and number-field declarations do not assert the required conclusion. None is a one-line specialization of the new node. No new Mathlib leaves are claimed.

Before creating the node I searched the whole DAG by 0AP2, etale/DVR neighbourhood, Dedekind extension and the proposed id, and searched the blueprint with blueprint_refs.py. The relevant existing statements are distinguished below. The stronger existing `lem-sfb-trait-nodal-etale-dvr-model` includes the item's conclusion and a smooth-generic refinement; it is unsplit and is not used to move the item into another node. The existing general `lem-trf-nodal-family-etale-local-model` is the genuine general input and is cited directly.

## Not duplicates

lem-sfb-etale-dvr-principal-neighbourhood vs lem-sbc-etale-trait-stalk: the latter proves the actual stalk is a DVR and the structural map is injective; it gives no principal affine open whose section ring is that DVR, and no etale finite-presentation map to that stalk.

lem-sfb-etale-dvr-principal-neighbourhood vs lem-sbc-etale-trait-section-lift: the latter constructs a DVR mapping into an etale chart along a specified section; it neither gives a principal open of an arbitrary etale R-algebra nor asserts that its resulting map from R is etale.

lem-sfb-etale-dvr-principal-neighbourhood vs lem-per-cyclotomic-local-ring-dvr: the latter concerns localizations of the particular cyclotomic integer ring and gives a field-or-DVR alternative, not a principal open neighbourhood in an arbitrary etale DVR algebra.

lem-sfb-etale-dvr-principal-neighbourhood vs lem-per-local-cyclotomic-group-algebra-split: the latter is a matrix-product splitting of a cyclotomic group algebra; it says nothing about principal open DVR neighbourhoods.

## Review by NW

I read models.tex 0CDD in full, including both the smooth and nonsmooth branches. I read curves.tex 0CBY's statement and its initial approximation/splitting setup, and 0C59/0C5A's description of nodal families. For the new lemma I read more-algebra.tex 0AP2, `lemma-Dedekind-etale-extension`, and the paragraph of 0CDD that actually shrinks the etale base to a DVR. I also read morphisms.tex 054L, `lemma-smooth-etale-over-affine-space`, 02FY, `lemma-dimension-fibre-after-base-change`, and the relative-dimension definition 02G2; varieties.tex 056V supplies the generic smoothness check. No SGA source is used.

Step 1 uses the local finite-presentation definition for finite affine presentations, the DVR definition for Noetherianity, the finite-type-over-Noetherian statement for Noetherian affine pieces, and `lem-trf-generic-fibre-points-smooth` precisely for generic points of the geometric fibres. On those affine geometric-fibre pieces the source and base are Noetherian and the map is finitely presented and flat over a field. All further geometric fibres are reduced by the original hypothesis for all algebraically closed fields. In a one-dimensional fibre a nonclosed nongeneric point would yield a chain of length two, so the only potentially nonsmooth points are the closed ones to which the original completion hypothesis applies. This verifies the input of step 4 rather than silently changing the item's condition.

Step 2 uses `lem-sc-fibre-dimension-after-base-change` for equality of fibre dimensions after passing to a geometric fibre, the smooth definition's equidimensional-fibre interpretation, and `sbc-lem-smooth-relative-dimension-locally-constant` to keep relative dimension one on the chosen neighbourhood. I checked that `lem-sc-standard-smooth-local-relative-dimension` really fixes d, unlike the more weakly worded general normal-form node. Its conclusion followed by the exact Mathlib polynomial-chart leaf gives an etale map to A^1, including the equality with the original structure map. A base open containing the closed point of a local spectrum is all of S. No section, separatedness, or finite-field assumption from a different chart lemma has been smuggled in.

Step 3 uses the etale base-change statement only for the restriction to D(t), and the open-immersion clause of etale-composition only for the source inclusion. The coordinate shift, choice between t and t+1, and Laurent-polynomial quotient isomorphism are written out. In particular the argument works in characteristic two and for a nonclosed x. It gives the n=0 model with R'=R.

Step 4 takes exactly the diagram and point promised by `lem-trf-nodal-family-etale-local-model`, not any construction internal to that node's proof. All its hypotheses were checked in step 1 or are assumptions of the item. The etale-composition statement makes the chosen affine base open etale over S. The new lemma's closed-fibre hypothesis holds because the chosen point lies over x in X_k. It supplies a principal base open, a domain DVR, and an injective local etale map from R; the stalk-only nodes do not supply these open-neighbourhood data.

Step 5 uses the base-change lemma on U->W and the open-immersion/composition lemma on U_1->U->X. The restriction is along V_1, so the same chosen point is retained and every structural triangle remains commutative. The fibre-product polynomial presentation is evaluated explicitly, with h restricted to h'. No unsupported localization at an arbitrary prime is treated as an etale finite-presentation extension.

Step 6 uses precisely the existing unit-times-uniformizer-power leaf. Its Noetherian local domain and nonzero maximal-ideal hypotheses follow from the DVR definition; it is applied only when h' is nonzero. I wrote both inverse maps for the quotient-ring isomorphism, thereby checking the unit direction rather than saying merely that the unit is absorbed. The zero-parameter case is retained, and coordinate identification preserves the local finite-presentation, flatness and unramifiedness conditions of etaleness. Every map is over R', so the commutative diagram is preserved. The generic fibre need not be smooth.

For the new node I verified the argument intended for its future splitter: an affine etale algebra over a trait has finitely many primes (both fibres are finite etale algebras over fields), and its closed-fibre stalk is a DVR by 0AP2. Prime avoidance selects b outside q and in every prime not contained in q. Then Spec B[1/b] consists exactly of primes contained in q, hence B[1/b]=B_q. The open is etale, and its local flat structural map is injective. This paragraph is report context, not a proof embedded in the new statement; the node is left unsplit. The principal-neighbourhood construction needs these finiteness and etale-Dedekind inputs, so it is a genuine general lemma, not a new name for a curve clause or an elementary coordinate substitution.

I tested the new statement on B=R (b=1), a product R x R (an idempotent isolates the selected factor), R x Frac(R) (isolate the R factor), a finite unramified local extension (already a DVR), and B=Frac(R) (there is no prime over the closed point, so the hypothesis fails). This checks why finiteness as an R-module and completeness must not be added, and why the special-fibre hypothesis must not be removed. For the item I checked smooth points, persistent nodes uv=0, and unit/nonunit smoothing parameters, including residue characteristic two. The empty X case is vacuous; all other empty-fibre cases cause no problem because x is specified in X_k.

I checked delivery-errors B1-B10: the new node is self-contained and statement-only, all nonbasic notions have actual definition nodes, sources give tags and labels, JSON contains ordinary single TeX escapes, searches are logged verbatim, no Mathlib leaf or attachment is invented, and blueprint places/searches are recorded. For C1-C8 I opened every cited statement and copied it into citations.json; the citations supply the exact diagram, dimension, permanence and factorization facts used, without reading extra conclusions out of their proofs. Cross-unit generic tools are declared in split_report, and no cited dependency was chosen from above the item. For D1-D5 the proof retains both branches and the explicit coordinate calculations; the one new node is purely a base-ring neighbourhood theorem. For E1-E7 I checked the hypotheses and actual objects at each application, corrected the source's coordinate slip, and kept the distinct field-versus-DVR and closed-versus-generic cases. No step exceeds 2000 characters; no long step conceals a separate comparison lemma. The server review_split check passed before packaging.

## What remains

Stage 1 is complete for this item. The single new general base-neighbourhood lemma remains unsplit for a subsequent worker, as required. No Lean was written or compiled. The repository and launcher files were only read; all authored files are in the assigned sandbox.
