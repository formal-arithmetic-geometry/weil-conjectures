## Worker report

Item: lem-sfb-normal-smooth-group-local-ample-line. Group NJ, stage 1, 2026-10-24. Direct delivery under the dispatcher's brief. The statement is unchanged. There was no previous sandbox node, proof, report or search log; I copied the current item and retained its original searches and provenance.

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-normal-smooth-group-local-ample-line.json: item, now split into six proof steps.
- lem-sfb-smooth-normal-affine-boundary-cartier.json: statement-only prerequisite, unsplit, no Mathlib match.
- lem-sfb-group-affine-section-ampleness.json: statement-only prerequisite, unsplit, no Mathlib match.

Also written: citations.json (every use in every item step, with the cited statement verbatim), searches.jsonl (the search command's own records), this report and build_split.py (sandbox-only preparation helper). No Lean was written or compiled. No repository or launcher file was edited, and no git command was run in the repository.

## Attachments

None. I searched lean/WeilConjectures for the exact item tag and for group/quasi-projectivity, normal-base ampleness, Ramanujam--Samuel and the supplied-section criterion. GroupScheme/QuasiProjective.lean and AmpleFamilySmooth.lean concern groups over a field and do not prove the item over a normal base. A field theorem is not an attachment to this item. The source library has no exact declaration for either new prerequisite.

## Wanted literature

WANTED: Michel Raynaud, Faisceaux amples sur les schémas en groupes et les espaces homogènes, LNM 119 (1970), VI Corollary 2.4 (and VI Theorem 2.1), for lem-sfb-normal-smooth-group-local-ample-line. The item's path literature/raynaud-faisceaux-amples-schemas-groupes.pdf does not exist locally. I did not claim to have read this missing original or download it.

WANTED: Ning Guo, Divisors on coherent schemes and homogeneous spaces, version dated March 31, 2026, Proposition 3.3 pp.5--6, Proposition 5.9 pp.13--14, Corollary 6.6 p.16, Theorem 6.8 p.17, and Corollaries 6.13--6.14 p.18, for both new prerequisites and the assembly. Local destination named in the nodes: literature/guo-divisors-coherent-schemes-homogeneous-spaces.pdf. I read those parts online at https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf, without saving a copy. The item has proof_origin.by=agent, as required for missing local literature.

For the Cartier input, Guo explicitly identifies the Noetherian argument as EGA IV4 Proposition 21.14.3 (Ramanujam--Samuel), after EGA IV4 Corollary 21.12.7. No Stacks tag for that normal-base Cartier theorem was found; I did not substitute the weaker regular-total-space Tag 0BCW. Existing elementary/permanence inputs retain their precise Stacks tags in their own nodes. No SGA source is used by this delivery.

## What was missing and what changed

The imported item had no proof or proof dependencies, and its original Raynaud source is unavailable locally. I supply the affine-boundary construction rather than replacing it with a new local-quasi-projectivity existence assertion. The first prerequisite turns a supplied fibrewise dense affine open into a Cartier divisor on a general smooth scheme; it has no group law or positivity conclusion. The second starts with a supplied line and section and detects its ampleness; it constructs no line. Neither is the item or one of its existential clauses.

I chose a principal open W inside the inverse image of an affine V under the identity section. Then U=V intersect H_W is a principal open of V and is affine. Merely intersecting arbitrary affine opens without this argument would not have sufficed on an arbitrary scheme. I also wrote the local coefficient of the canonical divisor section explicitly, so the identification of its nonvanishing locus with U is an argument rather than an unexplained transport.

The ancestor command reports blueprint.from.node=None. This auxiliary chain ends at lem-sfb-admissible-direct-image rather than an imported node. I preserve the item's null ancestor and existing via list, and prepend the item for each new node. Their from.place records the actual local-ample-line input in lem-sfb-symmetric-line-power-prolongation proof step 3. I read the current literature/blueprint/latest six-functor unit and its direct-images proof, not an older snapshot. It supplies the upstream context, not either new geometric assertion. I did not invent a nearest blueprint ancestor.

## Searches and nonduplication

Before creating the nodes I searched the whole DAG by source, tag, statement keywords and likely declarations. In particular, the searches included Raynaud/VI 2.4, Ramanujam, 21.14.3, Picard-admissibility, affine boundary and group ampleness. I opened the existing field-level affine-boundary, translated-divisor family, group ample-line and normal-base line-locality nodes, as well as every node cited in the item. The blueprint searches `group ample`, `quasi-projective`, `Cartier normal`, `group invertible`, `Cartier affine`, `ample group`, `affine boundary`, and `group ampleness` produced no node stating either prerequisite. The quasi-projective hits are curves, Hilbert representability or finite descent, not the present normal-base group theorem.

The new nodes each record five actual msearch.py searches: grep, LeanSearch, Loogle and two LeanFinder phrasings. The item also records five new actual searches, preserving its inherited searches. All services responded. I read the returned signatures/descriptions. They give basic opens, smooth affine presentations, reducedness, normalization, projective-spectrum charts and section denominators, with no normal-base Cartier-boundary or group-action ampleness theorem. Generic basic-open lemmas are not matches for these geometric statements. No new node is a Mathlib leaf.

## Not duplicates

lem-sfb-smooth-normal-affine-boundary-cartier vs lem-sfb-smooth-affine-cartier-boundary: the existing node assumes a smooth integral finite-type scheme over a field; the new node treats a smooth family over a possibly singular normal locally Noetherian base and requires fibrewise density. The total space need not be regular, so the existing regular-total-space proof cannot be applied.

lem-sfb-smooth-normal-affine-boundary-cartier vs lem-sfb-affine-open-boundary-codimension-one: codimension one does not assert local principality over a singular normal base; the new node supplies the latter under smoothness and fibrewise density.

lem-sfb-group-affine-section-ampleness vs lem-sfb-finite-type-group-ample-line: the existing field-level existence assertion supplies some ample line; the new criterion concerns a specified line and section over a normal base and does not supply that data.

lem-sfb-group-affine-section-ampleness vs lem-sfb-translated-cartier-parameter-family: the existing field-level parameter-family assertion supplies potentially different translated lines and section loci, not ampleness of a specified line over a normal base.

lem-sfb-group-affine-section-ampleness vs lem-sfb-normal-smooth-group-local-ample-line: the item constructs local lines without any line or section in the input; the new node only detects positivity once the affine section locus has already been constructed by the item's preceding steps.

## Review by NJ

I reread the unchanged statement against Guo's discussion of Raynaud in the introduction, the normal-base construction in Theorem 6.8, and Corollary 6.14. The proof keeps an arbitrary normal locally Noetherian base, smooth separated finite presentation, and connected fibres; it never assumes commutativity, a regular base, an abelian or semiabelian group, or properness. Absolute ampleness and relative ampleness are both retained. The empty base has the empty covering.

For the first new node I read Proposition 3.3(iii) and its final Noetherian proof paragraph on p.6. Its affine-open-immersion condition follows from affineness of U and separatedness of X over the affine base (Stacks 01SG); fibrewise density is explicitly an input. The reduced boundary has no embedded associated points. The source then gives the Cartier conclusion. The source states an integral normal base; a normal Noetherian affine scheme is a finite disjoint union of normal integral components (Stacks 0357), so applying the statement component by component gives exactly the version recorded here. This is recorded in source.place, rather than pretending to quote a verbatim source statement over a disconnected base.

For the second new node I read the final assertion of Proposition 5.9 and Corollary 6.6(ii), including their hypotheses. For the translation action on G, smooth connected group fibres are geometrically integral. The normal integral-base assertion of 5.9 gives a positive power with the square property; the affine nonvanishing locus persists when the section is raised to that power. Corollary 6.6(ii) then applies, since the affine open meets every irreducible fibre and so contains its maximal point. Ampleness of a positive power is equivalent to ampleness of the line. Finite disjoint normal base components are handled separately and the resulting lines are the supplied line on their disjoint inverse images. I place this proof plan here, not in the new node's statement or proof fields: it remains a statement-only item for a later split.

Step 1 uses only the smooth clause of lem-pc-proper-base-change, separated base change from lem-weil-pbc-separated-base-change, and finite-presentation base change from lem-weil-pbc-qcqs-morphism-permanence(3). I opened their statements: no properness of H or Noetherianity of an auxiliary target is being taken from those lemmas. The group operations restrict by def-sc-group-scheme. The exact part (0) of lem-weil-pbc-affine-ideals-closed-subscheme supplies affine principal opens. The selected W lies inside e^{-1}(V), so every restricted identity really belongs to U. Local normality and local Noetherianity persist on open subschemes; pqf-def-locnoeth explicitly includes the latter.

Step 2 uses lem-weil-pbc-finite-type-over-noetherian for residue-field fibres only, then lem-sc-noetherian-closed-subset-finite-components for their finitely many components. The actual statement of lem-sfb-group-local-minimal-prime gives a unique minimal prime at every group point. The finite disjoint-component argument is written in the step; the node is not misquoted as asserting connectedness implies irreducibility. The hypothesis that the fibres are connected is used exactly here, and the identity ensures nonemptiness. This proves the fibrewise density required in step 3 without silently strengthening connected fibres to geometric connected fibres in the item's hypotheses.

Step 3 checks every input of the new Cartier-boundary node before applying it. It does not apply a theorem for regular schemes to the normal total space. Step 4 uses the actual invertibility statement of lemma-nagata-effective-cartier-is-invertible and the definition of O(D) as the dual ideal in def-pc-divisor-line-bundle; def-sc-invertible-module gives locally rank-one frames and their duals. In such a frame the inclusion section has coefficient f, so its nonvanishing locus is exactly the constructed affine U. This is the sole elementary step and the calculation is written out.

Step 5 uses precisely the statement of the supplied-line criterion with exponent 1. The base is affine and normal locally Noetherian, the group retains all three morphism properties, and the section locus is affine and meets every fibre because it contains the identity. Step 6 uses only the first assertion of lem-trf-affine-base-ample-canonical-data, whose statement explicitly gives ampleness on every affine base open from absolute ampleness over an affine base. Quasi-compactness follows from finite presentation. The point-indexed W_s cover S by construction.

I tested the new statements on the empty scheme and the empty Cartier divisor, the trivial group G=T, additive and multiplicative groups over a normal affine base, an elliptic curve with an effective nonzero divisor over a field, and disjoint normal base components. For U=X the Cartier ideal is O_X and sigma=1; the criterion then asserts ampleness of O_G when G is affine, as required. A zero section over a nonempty group fails the nonempty-locus hypothesis; the trivial line on a proper positive-dimensional group cannot meet the criterion through an affine section locus. The normal base need not be factorial; that is why the relative Cartier input is essential and was not folded into a purported elementary closure argument.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the written files. The prerequisites have no proofs, proof dependencies, or hidden proof sketches in their statements; every object and notion is introduced, TeX is singly escaped, source places and online-reading limitations are explicit, and all recorded new-node searches actually ran. Every non-elementary fact in the item's assembly is a cited node, with a verbatim quote in citations.json. Off-unit permanence, component finiteness, Cartier ideal invertibility and affine-base ampleness are declared in split_report.tool_uses as generic tools; no upstream unit route is replaced. No step exceeds 2000 characters. There is no statement dispute or unresolved mathematical gap in the assembly; the two substantive prerequisite proofs are intentionally the next queue items.

## Validation and delivery

The preliminary remote review_split exited 0 (PASS). The required deliver.py --no-push then exited 0 with “OK (not pushed)” at 3351571a8a5: the server preflight passed and saved its durable dry-run receipt. This report update is included in the final dry run and delivery. No local DAG check, compiler, Lake or build was run.
