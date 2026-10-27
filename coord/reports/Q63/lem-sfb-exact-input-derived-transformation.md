# Q63: lem-sfb-exact-input-derived-transformation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-exact-input-derived-transformation.json`: statement split, using existing DAG tools; no Mathlib match for the complete item.
- `citations.json`: fourteen step/node entries with verbatim quotations checked against the current cited statements.
- `searches.jsonl`: five searches made through the required msearch command (two LeanFinder phrasings, Loogle, LeanSearch and grep). Their actual results are appended to the item's existing search history.
- `report.md`: this report. `prepare.py` is sandbox-only preparation code, not a DAG delivery file.

No new nodes or new Mathlib leaves. The statement, statement dependencies, source, creation record and inherited blueprint provenance are preserved. The proof has seven steps, each shorter than 2000 characters. No unit record needs changing: this auxiliary item is not the key statement of its unit.

## Attachments

None. The exact blueprint tag has no hit in `lean/WeilConjectures/`. Concept searches there found bounded-below base-change constructions and separate unbounded K-injective infrastructure, not a project declaration giving the complete unbounded statement and all its clauses. In particular `CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusBaseChangeComp.lean` uses bounded-below categories and enough-injective hypotheses. Its sorry-free assembly is not the present statement. No compiler or Lake command was run.

## Literature

No WANTED document. Read the local Stacks `derived.tex`: Tag 070I (`lemma-K-injective`), Tag 070Y (`lemma-K-injective-defined`), Tag 070K (`lemma-enough-K-injectives-implies`), Tag 05SU (`lemma-derived-shift`), Tag 05SE (`proposition-derived-functor`), and Tag 015F (`lemma-right-derived-exact-functor`). The source gives the derivation infrastructure; the exact-input comparison and explicit normalization are this worker's assembly, so `proof_origin.by` is `agent`.

Read the current blueprint in `literature/blueprint/latest/`, especially `sec-six-functors-basics/sk-prop-sf-comp-coherence/_section.md` and the statement and proof of `det-sf-comp-coherence-cocycle`. The relevant ancestor paragraph is “Refinement isomorphisms”; this item is the generic exact-input calculus used down the already recorded closed-restriction chain. No geometric route is replaced and no SGA source is used.

## Problems in the input and unfinished work

No statement correction or dispute was needed. The statement explicitly allows $EI$ to fail to be K-injective, so resolving $EI$ a second time is essential. The given Stacks tags do not verbatim state the entire item; the source already notes that limitation, and the delivery retains it. No new unresolved sublemma is needed because the necessary independent general facts already have DAG nodes. No Lean is written, and no claim of a completed Lean proof is made.

The existing `lem-sp-kinjective-computes` is deliberately not used: its statement assumes a left exact functor, Grothendieck categories, and bounded-below input. Likewise `lem-weil-pbc-derived-square-shift-on-kinjectives` assumes preservation of K-injectives by the input functor. Neither statement suffices here. `lem-pc-right-derived-functor-triangulated` was also not used because its formulation assumes K-injective resolutions in the target category as well; our $\mathcal C$ has no such hypothesis.

## Mathlib searches and Not duplicates

The required searches were run and their hits read. Loogle's `Functor.rightDerivedDesc` and the source of `rightDerived_fac`/`rightDerived_ext` (`Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean:77–98`) implement the universal descent part. `LocalizerMorphism.rightDerivedFunctorComparison` (`Localization/DerivabilityStructure/PointwiseRightDerived.lean:64–75`) treats a right derived functor of the composite, rather than identifying the full present transformation with its two-resolution and shift formulas. The first LeanFinder query also returned `InjectiveResolution.rightDerived_app_eq` and ordinary objectwise nonnegative derived functors, whose domains differ. The second phrasing returned localization shift infrastructure; it did not supply the complete item as a leaf. These findings are positive ingredients, not grounds to declare the whole statement a Mathlib leaf.

Whole-DAG searches by tags and by K-injective/derived/shift terminology located the existing infrastructure cited below. `tools/blueprint_refs.py ancestor` gave `det-sf-comp-coherence-cocycle`; whole-blueprint searches for `K-injective`, `exact functor`, `derived transformation`, `exact-input`, `second resolution`, and `right-derived transformation` found no blueprint statement of the entire item. No new node was created, so there are no new/existing duplicate pairs to distinguish. The existing generic lemmas are reused rather than specialized into new nodes.

## Review by Q63

I checked the statement and proof against delivery-errors B–E with the cited node statements open. All objects in the unchanged statement are introduced, K-injectivity and exactness are specified, and each named notion has its definition dependency. There are no new statement-only nodes requiring sources or searches. TeX is stored with single mathematical backslashes after JSON decoding. The cited tags were checked in the local Stacks source, and no statement takes a tag as its definition.

Step 1 uses the statement of `lem-weil-pbc-exact-functor-derived-factorization`: it explicitly gives preservation of quasi-isomorphisms, the localization factorization, its compatibility with integer shifts, and triangulatedness. The item defines exactness by kernels and cokernels; I wrote out why additivity supplies the finite biproducts needed to meet the lemma's finite-limit/finite-colimit convention. It is applied only to $E$, never to the potentially nonexact $F,G$.

Step 2 uses `lem-trf-additive-homotopy-triangulated` for termwise functors with signed shifts and cone triangles, and `def-weil-abstract-derived-category` for the triangulated localization. The statement of `lem-weil-pbc-kinjective-total-derived` gives precisely the universal unit and K-injective computation for an exact functor out of a homotopy category, so it applies to $Q_{\mathcal C}F$ and $Q_{\mathcal C}G$ even when $F,G$ are merely additive. `lem-sf-kinjective-replacement-triangulated` supplies the triangulated equivalence, its inverse and coherent shifts, in each of $\mathcal A,\mathcal B$. Composing gives the canonical triangulated structures used by the item. The universal pair and its unit-compatible uniqueness are exactly the statement of `def-sfb-right-derived-functor`; no fact was taken from that node's proof. I checked that resolutions are needed only in $\mathcal A,\mathcal B$, not $\mathcal C$. The two non-Mathlib generic statements from other units are declared as tool uses in `split_report`; they supply infrastructure without changing the compactification route.

Step 3 is substitution into the explicit natural-transformation bijection in `def-sfb-right-derived-functor`. I checked the directions: its target functor is $T=RG\,D(E)$ and the chain-level map is $\eta^G_{EK}Q(\beta_K)$. No assertion that $R(GE)=RG\,D(E)$ is used. The differential and naturality equations explain the passage of $\beta$ to complexes. This step is elementary relative to that stated bijection.

Step 4 uses only the computation-unit isomorphisms stated in that same node and the facts already established in steps 1 and 3. The definitions of $m_F,m_G$ have the correct orientation. I expanded all three naturality equalities and the cancellation giving $Q(Gj)Q(\beta_I)$; in particular I never invert $\eta^G_{EI}$, which need not be invertible. This is the elementary calculation that carries the component clause, rather than a new node restating it.

Step 5 uses `lem-weil-pbc-kinjective-hom-derived` exactly for lifting morphisms into K-injectives and for quasi-isomorphisms between K-injectives being homotopy equivalences. It needs no K-injectivity of $EI$: the second lift has K-injective target $H'$. The equality $vj\simeq j'E(u)$ follows by the injectivity of the Hom map with target $H'$. Applying additive functors to homotopy classes is supplied by the statement of `lem-trf-additive-homotopy-triangulated`, and the displayed equation then proves the compatibility under both changes of resolution. No abstract “transport” replaces this check.

Step 6 uses both clauses of `lem-weil-pbc-kinjective-shift`, for $s[r]$ and $j[r]$. It is legitimate to shift $H$ and use it to resolve $E(I[r])$ because step 1 identifies $E(I[r])$ with $(EI)[r]$. I checked the explicit degree-$a$ formula and differential sign $(-1)^r$ on both routes, for positive, zero and negative integers. The canonical shift comparisons were fixed using the triangulated K-injective presentation in step 2. Localization is essentially surjective by its stated model in `def-weil-abstract-derived-category`, so the equality on $QK$ gives it on every derived object by naturality.

Step 7 uses the definition of a triangle morphism in `def-weil-triangulated-category`. The first two squares are naturality, and the written equation for $z:Z\to X[1]$ combines naturality with the $r=1$ equality of step 6. The shifted connecting arrows have the required orientation $s_{1,X}\circ RF(z)$. Thus the concluding claim includes the connecting arrow, rather than only the first two squares.

For small cases I checked $E=1$, $F=G$, $\beta=1$ (the unit equation forces the identity); $\beta=0$ (the same bijection forces the zero transformation); $E=0$ and the zero complex (the formula is zero since additive functors send zero to zero); and $r=0,-1$ (no positive-shift restriction is concealed). I checked that no cited statement reaches the item through statement or proof dependencies, and that `proof_deps` is exactly the union of the step citations. Every non-elementary fact is a cited existing statement; the calculations and the final triangle square are explicit assembly. No step exceeds 2000 characters. The B–E audit found no remaining missing hypothesis, relabelled clause, unsupported citation, or circular dependency.

## Validation and delivery

The required server dry run completed successfully: `OK (not pushed)` at `e3bab9eb1c5`, with server preflight passed. The final payload includes the strengthened step-5 quotation of uniqueness of the universal pair; it is rerun through the same dry run before direct delivery. No local checker, compiler, Lake, repository write or git command was run.
