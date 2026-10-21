# Stage-1 delivery: lem-sfb-adic-perfect-model-complete-reduction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-perfect-model-complete-reduction.json`: existing statement, split in seven steps; no Mathlib match.
- `citations.json`: sixteen entries, one for each use in each step, quoted verbatim from the live dependency statements.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only preparation.

There are **0 new nodes and 0 Mathlib leaves**. No unit, repository, launcher, or Lean file was written. The existing statement, statement dependencies, provenance, blueprint ancestry, and inherited searches are retained.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for adic/perfect/completion combinations. The perfect tower and ordinary projective-complex declarations do not state the module-sheaf completion and residue theorem. In particular a tower definition or a partial statement would not justify attachment.

## WANTED

None. All sources used are present locally.

## Issues in the imported item

The statement is valid as written; no STATEMENT-DISPUTED correction was needed. The inherited item source and the existing bounded-above-flat dependency cite Tag 06YS for `lemma-bounded-flat-K-flat`, but the local authoritative tag table identifies that lemma as 06YQ (06YS is `lemma-K-flat-resolution`). The delivered proof uses 06YQ. I retained the maintainer-owned source field and report this bibliographic correction here; it does not change any mathematical statement. Its proof was empty. The new proof supplies the perfect-model argument underlying the reverse implication of Bhatt–Scholze Proposition 6.6.11, as used by the existing parent `lem-sfb-adic-stratified-perfect` in steps 4 and 5. This is below the unit's comparison with the integral criterion; it changes no unit or chapter route.

One must prove completeness in the precise locally derived ringed-ideal convention, rather than assume that ordinary inverse-limit completion alone proves it on every site. Step 2 explicitly uses the pro-etale torsion-limit completeness theorem and then scalar restriction. One must compute the residue over B rather than assume that A/I has a finite projective A-resolution: the complex being reduced is K-flat over B, which suffices.

## Unfinished work

None for this one-level split. Existing unsplit dependencies remain the maintainers' queue items. No new unsplit node was necessary.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. DAG searches for Tags 093J, 093M, 099Q and 06YQ and for completed constant coefficients, torsion-limit completeness, exact constants and slice restriction found the existing nodes cited. Whole-blueprint searches (`blueprint_refs.py search`) for `completion flat`, `derived complete`, `perfect model`, `constant reduction`, and `torsion limit` found no additional exact statement of the item. The pre-existing `same_as: []` remains correct. The existing local integral perfect-model cohomology node concerns DVR coefficients and the *unreduced* cohomology calculation after an immersion, so is not this general Noetherian-ring residue-and-completeness statement. The existing completion equivalence and torsion-limit statements are the more general tools actually used, rather than new specializations of them.

## Mathlib searches

Ran the prescribed msearch command with this group and item for both LeanFinder phrasings, Loogle, source grep, and LeanSearch. Read every result and preserved the command's own `searches.jsonl`. LeanFinder's first query returned K-projective complexes, projective resolutions, and cohomological bounds; its second returned ordinary algebraic adic completion and Fontaine period rings. None is a ringed-site completeness theorem. LeanSearch returned constant sheaf definitions and essential-image criteria. Loogle and the completion/residue source grep returned no hits. All services answered; no unavailable service is misreported as absence. These actual searches are appended to the inherited records, without replacing the latter. The item is not an exact or one-line Mathlib specialization.

## Review by Q134

I read delivery-errors B–E, the stage-1 brief, the chapter and unit records, GOAL.md, and SETUP's three-level rule. I read the current blueprint comparison node under `sk-lem-integral-models` and the parent's completed-model proof. In the Bhatt–Scholze PDF I read Proposition 6.6.11, including the definition immediately above its proof of a constant perfect completed model and the reverse implication: completeness of local perfect models and their perfect first reduction. Its broader constructibility and finite-stratification assertions are not used to prove this item.

For the concrete algebraic tools I read sites-modules.tex `lemma-constant-exact` (093J), `lemma-tensor-with-finitely-presented` (093K), `lemma-flat-sections` (093L), and `lemma-completion-flat` (093M), including the canonical quotient identifications. I read proetale.tex `proposition-enough-weakly-contractibles` (099Q), in particular its weak Serre, inverse-limit and cohomology clauses, and the start of its proof. I read algebraization.tex `lemma-restriction-derived-complete` (099C) and its proof: the extended ideal is essential and the result has no flatness assumption. I read sites-cohomology.tex `lemma-bounded-flat-K-flat` (06YQ) and its proof. All tag/label identifications were checked in the local Stacks tag table. No SGA source was used.

For step 1 I opened and read the statements of the projective-module definition, constant-module section properties, and sectionwise module limits. Projectivity explicitly gives a lift along the chosen finite-generator surjection, not just an abstract summand of a possibly infinite free module. Constant exactness supplies finite-sum compatibility and preserves the splitting maps. Sectionwise limits supply precisely the compatible tuples used to show that the image of a fixed idempotent commutes with this inverse limit. The finite-projective identification is written out rather than made into a duplicate lemma. The chosen splittings are only used degreewise; no false assertion that the entire complex is a summand of a free complex with constant differential is made.

For step 2 I read the entire torsion-limit-sheaf-completeness statement. It explicitly covers bounded complexes whose terms are inverse limits of sheaves killed at level n by I^n, with arbitrary schemes and no residue-set finiteness. These are exactly the terms obtained in step 1. Noetherianity supplies finite generation of I. I read the restriction-local-completeness statement and checked that it preserves and reflects precisely local derived completeness for the extended ideal. Applying it to underline A → B proves IB-completeness, including the sections of IB that need not come from a single global scalar of I.

For step 3 I read the quotient clause of the existing constant-completion-equivalence statement, not merely its title or proof. It gives the canonical projection B/I^n B ≅ underline(A/I^n), for all Noetherian A and ideals I, and hence the n=1 identification used here. Only that clause is taken; no inference that an arbitrary B-complex is complete is drawn from the equivalence.

For step 4 I checked the sheaf tensor definition and the two K-flat statements cited. The flatness argument uses the actual finite-summand description from step 1 and local lifts of sections in exact sequences; it does not assume that a sheaf epimorphism is sectionwise surjective. The bounded-above flat theorem applies because b is a bound and the terms have just been proved flat over B. The derived-change-of-rings statement explicitly computes its functor on K-flat complexes, so no hypothesis on the projective dimension of the residue quotient is missing.

For step 5 I checked that the canonical tensor formula is balanced for both coefficient rings and respects the same splitting idempotents. Its agreement with each differential is written on elementary tensors and hence holds after sheafification. This proves a chain isomorphism, with the canonical coefficient quotient of step 3, rather than just unrelated isomorphisms of terms. The constant exactness statement used here supplies preservation of the finite split presentations; the remaining tensor balancing and direct-summand restriction are elementary.

For step 6 I checked that the constant-module statement actually asserts exactness, sufficient to identify kernels, images and their quotient and hence constant cohomology. Finite-dimensionality is proved over the field k: each term is a summand of a finite k-vector space, and subspaces and quotients have dimension at most that of the term. This says finite-dimensional, not finite as a set. Vanishing uses the actual degree support, not a Tor-amplitude assumption on A/I^n over A.

For step 7 I read all four cited statements. Weakly etale localization identifies the sites and the restricted constant ring sheaves; the module-limit theorem is sectionwise and therefore commutes with restriction. The restriction K-flat theorem states exactness as well as preservation of K-flat complexes. The localized tensor theorem gives the precise ordinary tensor comparison, so, on the K-flat model already chosen, it also identifies the derived reduction. Completeness follows by repeating steps 1–2 on U, with no illicit appeal to a global underlying stalk computation. Every covering object U is a scheme and all unchanged coefficient hypotheses hold there.

I tested the proof on T empty; the zero complex; a one-term projective module; a disconnected coefficient ring with I a maximal ideal; I=0 when A is a field; an infinite residue field such as Q; and a singular coefficient ring such as k[e]/(e^2) with I=(e), where the residue need not be perfect over A. The argument remains valid in all of them. A zero ring has no maximal ideal, so the stated hypotheses exclude it; I=A is similarly excluded. No completeness of A itself, Noetherianity of T, or residue-characteristic invertibility is used. The complex's actual support supplies both bounds even when the interval is empty.

I checked every non-elementary fact against a cited node's statement and every quoted fragment against the live text, without using a dependency's proof as an unstated interface. The longest step is below 1100 characters; none hides a long comparison argument. All non-elementary steps have explicit sources and all proof dependencies are exactly the union of their uses. Off-unit statements are declared as generic tool uses in split_report, not inserted into the maintainer-owned tool_uses field. No elementary fact, item clause, or duplicate has been promoted to a new node.
