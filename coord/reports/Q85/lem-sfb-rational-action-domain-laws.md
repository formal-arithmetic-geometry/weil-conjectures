# Stage-1 report: lem-sfb-rational-action-domain-laws

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rational-action-domain-laws.json: item, split into four explicit steps; no exact project attachment found.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-map-maximal-representative.json: statement, Mathlib leaf. RationalMap.toPartialMap and the restriction/quotient lemmas in Mathlib/AlgebraicGeometry/Birational/RationalMap.lean give all clauses.
- citations.json: exact statement quotations for all five step/node pairs.
- report.md: this report. searches.jsonl retains the command-generated searches.

## Attachments

None. Searched the live lean/WeilConjectures source for the exact blueprint tag, rationalAction/rational_action/RationalAction, actionDomain/action_domain/domain_laws, and RationalMap/PartialMap. The project has valuation-ring extensions and inverse partial maps, not these domain action laws. No project declaration is used as an attachment.

## WANTED

WANTED: J. S. Milne, A Proof of the Barsotti-Chevalley Theorem on Algebraic Groups (2013), Definition 4.2 and Lemma 4.3, local copy for lem-sfb-rational-action-domain-laws. Read the primary article online at https://arxiv.org/html/1311.6060v2, including the unit/double-graph proof. No literature file was downloaded or modified.

## What was wrong and what changed

The item was statement-only, with an article reference but no proof. Its mathematical statement agrees with Milne 2013, Definition 4.2(a),(b) and Lemma 4.3. In particular the conclusion includes actual definedness at (gh,x), not merely equality where both sides happen to be defined. I retained that assertion. I normalized the inherited doubled TeX backslashes in the statement; this is a typographical correction only, not a mathematical statement correction.

I read the local iAG2017 book around Proposition 8.25 (printed pp.153-154), including its reference to the rational-action argument and its warning that equivariant completion cannot be used to prove this result. The 2013 article proves this using two graph closures. Here the proof_origin is honestly agent: fixing the given k-point h makes a simpler local representative possible, so graph-closure descent is unnecessary. The explicit formula F(u,z)=alpha(u h^{-1},alpha(h,z)) is regular on the specified inverse-image open. It agrees with the original action on all G times Y by the morphism-level action identity, and therefore extends alpha near (gh,x). This proves both clauses without a new node restating either one.

The nearest blueprint ancestor is null in the inherited node chain and in tools/blueprint_refs.py ancestor. That field and the long inherited via chain are preserved. I filled the new node's from.place with the precise rational-domain operation it supports. Whole-blueprint searches for rational action, rational map, maximal domain, domain of definition and 0A1Y found no equivalent statement. Generic product-projection openness and reduced-product facts are declared tool uses across units; neither changes the inherited unit route. The item is not the key statement of its inherited unit, so no unit record was changed.

## Not duplicates

lem-sfb-rational-map-maximal-representative vs lem-sfb-weil-extension-to-abelian-variety: the existing node with 0A1Y mentioned in its proof asserts extension to all of a smooth source for an abelian target; the new node assumes only a reduced source and separated target and constructs the morphism on its maximal open, which need not be the whole source.

lem-sfb-rational-map-maximal-representative vs lem-sfb-relative-rational-flat-regularity: the existing statement concerns S-rational maps between smooth finite-type S-schemes over a Noetherian S, with flat pullback of domains. X in this item is only integral and may be singular, so that statement cannot be applied. The new Mathlib leaf is the absolute reduced-source result with no smoothness or Noetherian assumption.

lem-sfb-rational-map-maximal-representative vs lem-sfb-group-difference-diagonal-domain: the existing statement is a diagonal-domain comparison for a difference map into a smooth group, with a smooth integral source. It does not state the generic reduced-source, separated-target maximal-representative result.

lem-sfb-rational-map-maximal-representative vs lem-chow-agree-on-dense-open: the existing statement only equates two already-defined morphisms given a scheme-theoretically dense open. It does not supply a morphism on the union of all rational representatives. The new leaf includes that construction and its restriction property, and applies to arbitrary reduced sources without an additional scheme-theoretic-density premise.

## Review by Q85

I checked B-E against the actual statements and source text. For the item I read Milne 2013, Definition 4.2 and Lemma 4.3 online and the local iAG2017 Proposition 8.25. For the sole new node I read Stacks morphisms.tex, Tag 0A1Y, label lemma-rational-map-from-reduced-to-separated, including the proof by closed equalizers and gluing, and pinned Mathlib RationalMap.lean lines 327-337 and 570-644. Those sources prove precisely the reduced-source and separated-target statement; no smoothness, normality or properness was smuggled in. The new node is a Mathlib leaf, with no proof sketch in its statement and a file/line match whose how field names the declarations for every clause. Its searches are the real msearch commands preserved in searches.jsonl: semantic results identify toPartialMap and ext_of_isDominant, Loogle gives the actual current maximal-partial-map API, and grep gives the verified source lines. There was no service failure to mislabel as absence.

For step 1 I opened lem-wf-affine-product-reduced and read its current blueprint statement and proof under literature/blueprint/latest/blueprint/sec-algebraic-groups-lie-algebras/sk-i-cartier/. It explicitly states reducedness of A tensor B for reduced finitely generated algebras over an algebraically closed field, precisely the affine product charts here. Covering by these charts is enough for reducedness of G times X; I do not assume X smooth or claim a product-integrality theorem from this node. I also opened lem-sc-scheme-over-field-universally-open and Stacks morphisms.tex, label lemma-scheme-over-field-universally-open (0383). Its statement is explicitly about the second projection for any field and any schemes over it, so taking the factors G and X is valid. The short open-image argument proves density of G times Y. No unsupported Jacobson, rational-point-density, or smooth-implies-flat lemma is hidden in this step.

For step 2 the new maximal-representative statement gives a morphism on the union of representative domains, restricts to every representative, and represents the same rational map. The source G times X is reduced by step 1, and the target X is separated by hypothesis, so its two substantive hypotheses hold. Existence and uniqueness of the equivalence class from the original dense-open morphism are the definition, not an extra extension theorem. Step 2 also records that the whole G times Y lies in U, which is needed later.

For step 3 I checked the same leaf for agreement on intersections, not just existence of some representative. The pullback U_e of the open U is open and contains Y; X is integral, hence reduced. Thus the slice morphism and the everywhere identity are equivalent rational representatives on a dense common open and must agree on U_e. The step never infers a global regular action on X or even that e is defined at every x.

For step 4 I checked the same restriction-and-containment clauses. The slice U_h is an actual open inverse image, b_h an actual morphism, L a morphism formed using the fixed k-point h and group multiplication, and O its open inverse image of U. The hypothesis g acting on h acting on x puts (gh,x) in O. Invariance of Y ensures all G times Y lies in O; this is what makes O dense and F a valid representative. The equality on G times Y follows from the original morphism-level associativity and the group identity (u h^{-1})h=u, by restriction along the fixed k-point h. Thus no non-dominant composition of rational maps, no assertion about an undefined slice, and no claim that equality alone forces maximal-domain inclusion is used: inclusion and equality follow from the precise maximal-representative leaf. This is a direct construction from definitions, marked elementary, with the one nontrivial representative fact cited.

Edge cases: Y=X gives the original regular action immediately; G the trivial group gives restriction of the identity; the identity rational map has whole-domain maximal representative but step 3 only claims its value on the actual e-slice domain. Singular integral X is permitted throughout. At a boundary x where either successive action is undefined the implication says nothing. There is no division by a coordinate or assumption that a boundary point is smooth. The algebraically closed field hypothesis is used for reduced products. The new leaf also handles an empty source (empty maximal domain and unique empty morphism), and arbitrary reducible reduced sources, since equivalence uses dense opens and separatedness gives gluing. Dropping reducedness or separatedness is outside its statement.

I checked that the new generic lemma is neither a clause of the action-domain assertion nor a duplicate of the smooth relative rational-map theorem. All four proof steps are below 2000 characters and none hides a graph-closure lemma or a descent comparison. I corrected only the doubled statement escapes during this review. The files introduce no Lean declarations, hollow definitions, unrecorded searches, SGA sources, or proof dependence on the item itself.

## Unfinished work

None within this one-level split. The sole new dependency is a Mathlib leaf. Required remote dry-run and delivery results are recorded below after they run.
