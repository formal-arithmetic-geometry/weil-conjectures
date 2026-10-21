# Q77: lem-pur-ringed-derived-pullback-linear

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-ringed-derived-pullback-linear.json`: item, split in five steps; no Mathlib match.
- `citations.json`: fifteen step/node entries with verbatim excerpts from the statements read.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log; `write_split.py` is sandbox-only preparation material.

No new nodes and no Mathlib leaves. Every argument after the existing comparison and resolution theorems is a short calculation; introducing a generic scalar-preservation node would merely move the proof into another node. All proof steps are shorter than 1000 characters.

## Attachments

None. Searched the current project by the blueprint tag and by ringed/scalar/linear pullback terminology. `AlgebraicGeometry.Etale.linear_leftDerivedUpperStar` in `SixFunctors/Etale/Derived/UpperLowerStar.lean:292` and the analogous pro-etale instance at `SixFunctors/ProEtale/FiniteCoefficient/Derived/ScalarExtension.lean:124` concern the exact fixed-coefficient inverse-image functor. They do not state the item for arbitrary structural coefficient maps. No upstream sorry declaration is treated as a finished proof.

## WANTED

None. The local Stacks sources and current blueprint suffice.

## Statement clarification: STATEMENT-DISPUTED

The imported text did not explicitly say that A and B are commutative. The cited ringed-topos definition permits the broader wording "sheaves of rings", whereas the tensor and K-flat derived-pullback nodes explicitly assume commutative ring sheaves. Without commutativity or a central-image assumption, the proposed Hom action need not even be module-linear. On the one-point site take A=B=M_2(k), u and c identities, R=k[t], and send t to e_11. The A-linear endomorphism f:A->A given by right multiplication by e_12 has (t f)(1)=e_12 but (t f)(e_21)=0, whereas e_21(t f)(1)=e_22. Thus t f is not A-linear. The scalar maps satisfy the imported compatibility hypothesis.

The repair adds the explicit words "where A and B are sheaves of commutative unital rings". This restores the source's intended scope, not a new proof route: Stacks `conventions.tex`, section-algebra, explicitly defines rings to be commutative with 1; `sites-modules.tex`, Tag 03D6 (definition-pushforward), defines tensor pullback in that convention, and the existing `lem-weil-pbc-ringed-topoi-derived-pullback` states exactly this scope. All original scalar, universe, unboundedness and no-flatness clauses remain. No target or definition was changed.

## Proof and searches

The item is a coefficient-linearity ingredient for the first sentence of `lem-weil-compact-support-representative-independence` in the current blueprint (`main-20261015`, `sec-six-functors-basics/sk-thm-sf-pf-field`): the integral compact-support functor is linear. Its immediate parent isolates the coefficient-reduction pullback before open extension. This split uses that route and retains the item's existing blueprint ancestry and place. Whole-blueprint searches for derived pullback, compatible central scalars, central scalar, and linear derived found no blueprint equivalent of this general ringed-topos scalar lemma. Whole-DAG searches found the already-existing derived-pullback and linear-derived-category tools; they are reused.

The six searches in `searches.jsonl` were run with msearch, using LeanFinder twice with different phrasings, Loogle, LeanSearch, and grep in the derived-functor and derived-category directories. All services answered. Read the returned sheaf pullback definition and its comparison with presheaf pullback/sheafification at Mathlib `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:40-113`. They are underived and do not assert the item. Read Mathlib `Algebra/Homology/DerivedCategory/ExactFunctor.lean:26-43,120-125`: `Functor.instLinearDerivedCategoryMapDerivedCategory` requires preservation of finite limits and finite colimits of the underived functor. Arbitrary coefficient change need not preserve kernels, so this is not a one-line specialization. Read `DerivedCategory/Linear.lean:24-43`; it supplies the induced linear structure and linear localization, already carried by the existing `lem-weil-linear-abelian-derived-category`. None of these results is a leaf for this item. The item's pre-existing searches were retained, and the actual new searches were appended with exact tool/query texts.

## Not duplicates

No new nodes were created; no new/existing same-tag pair arises.

## Review by Q77

I read Stacks `sites-cohomology.tex`, Tag 06YY (lemma-derived-base-change), including the proof that derives pullback from flat-term K-flat complexes. I also read Tag 06YS (lemma-K-flat-resolution), its statement and proof, and `sites-modules.tex`, Tag 03D6 (definition-pushforward), including the formula B tensor over inverse-image A with inverse-image M. For commutativity I checked `conventions.tex`, section-algebra. The scalar argument is my argument using these sources and the existing DAG interfaces, so `proof_origin.by` is `agent`; 06YY is not represented as explicitly stating linearity. No new-node source is needed and no forbidden SGA route is used.

For step 1 I read `def-weil-sheaf-of-modules-category` in full: restrictions are semilinear and morphisms are sectionwise module-linear. Commutativity makes multiplication by the scalar section a module morphism; the unital ring homomorphism identities give the Hom-module axioms. `def-weil-linear-category` says composition is bilinear, and I wrote out its sectionwise verification. This also makes the scalar maps chain maps, without a new theorem.

For step 2 I read the whole statements of `lem-weil-pbc-ringed-topoi-derived-pullback`, `def-weil-pbc-algebraic-inverse-image`, and `def-pur-sheaf-tensor-product`. The first states the precise pullback formula for an arbitrary geometric morphism, not just one induced by a site functor. The second explicitly transports module multiplication and specifies naturality on module morphisms; it supplies exactly what is used for inverse-image scalar maps. The third defines tensor as the sheafification of sectionwise tensors. The balancing calculation is written on pure tensors, then finite sums, then sheafification. The equality c(u^{-1}s_A(r))=s_B(r) is precisely the item's hypothesis and is used at the displayed substitution. No stalk argument or enough-points assumption is needed. This is an elementary defining-relation calculation, not an uncited comparison theorem.

For step 3 the statement of `lem-weil-linear-abelian-derived-category` supplies both the induced linear structure and R-linearity of Q on componentwise maps. The derived-pullback statement supplies an actual natural transformation on the homotopy category with invertible component on every flat-term K-flat complex. Naturality applies to the particular chain endomorphism mu_P(r); its direction is epsilon:F Q -> Q uStar. The formula has this direction, so cancellation is legitimate. Bilinearity from `def-weil-linear-category` permits moving r across epsilon without assuming that F is already linear. This avoids circularity and avoids asserting that arbitrary objectwise K-flat identifications determine maps.

For step 4 `lem-pc-kflat-resolution` explicitly supplies a quasi-isomorphism P->K in this direction, with K-flat P and flat terms, for every unbounded complex of module sheaves. Smallness is precisely the item's assumption. `def-weil-abstract-derived-category` makes Q invert quasi-isomorphisms and presents D as that localization; hence a and F(a) are isomorphisms. The scalar-conjugation identity uses only bilinearity and functoriality. I wrote out why the same calculation covers an equivalent realization of the derived category. No claim that a derived morphism lifts to a map of chosen resolutions, and no functorial resolution assertion, is used.

For step 5 I reread `def-weil-linear-functor`: additivity as well as preservation of scalar multiplication is required. The derived-pullback theorem states exactness, while the final sentence of `def-weil-triangulated-category` defines an exact functor as additive. Thus both clauses are present. The calculation r f = (r id_Y) composed with f proves scalar preservation for every derived morphism, not only localized chain maps. Generic tools outside the unit are declared in `split_report.tool_uses`; they supply the standard module and localization constructions, without replacing any six-operations unit step.

I checked small cases: the identity ringed morphism; zero complexes and morphisms; r=0,1; the zero target ring; noninjective scalar maps; and the nonflat one-point map Z->F_2. In the last example, a flat resolution of F_2 produces the expected two-term F_2 complex with zero differential after tensoring, and integer scalar multiplication reduces modulo 2 in both degrees. The argument uses the derived comparison and does not incorrectly identify derived pullback of an arbitrary complex with its underived pullback. The counterexample above checks the corrected commutativity omission explicitly.

Against B-E: the statement introduces its objects and its notions have definition-node citations; all cited statements were read; citations.json excerpts are verbatim and relevant to each use. No unsplit node has a hidden proof, no elementary lemma or item-clause node was created, and no new tag duplicate is possible. The five steps carry the scalar argument rather than restating the item as a dependency. The only non-elementary inputs are existing named nodes for the K-flat comparison, resolutions, and induced linear derived categories. Every such use is cited. All steps are below the long-step threshold. Statement ambiguity and its repair are explicitly reported above. Server dry-run results are recorded below after checking.

## Unfinished work

None in the stage-1 split. Existing dependency nodes retain their own proof obligations.
