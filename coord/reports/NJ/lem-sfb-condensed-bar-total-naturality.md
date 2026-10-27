## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-bar-total-naturality.json`: existing statement, now split into eleven steps; not an exact Mathlib match.
- No new nodes and no new Mathlib leaves.
- `citations.json`: 27 verbatim extracts, one for each proof-step citation.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact id, its blueprint tag, and condensed/bar terminology found no declaration stating the item. The landed `lean/Sheaf/CategoryTheory/CondensedEquivariantBarData.lean` was read, especially totalCochains, TotalAugmentation, resolutionComparison and Computation: it specifies the normalization and naturality that the consuming theorem must construct, rather than proving this item.

## Wanted

WANTED: an independent reference for internal condensed bar diagrams and their resolution naturality over an arbitrary commutative condensed ring, for lem-sfb-condensed-bar-total-naturality. The current blueprint paragraph motivates the input but does not contain its proof. The explicit calculation is therefore marked agent-written. No download or SGA source was used.

## Corrections and scope

The item's statement is unchanged. Its proof was empty; all proof dependencies are now the union of the actual step citations. No assumption that free condensed modules are projective, no exactness of internal Hom, and no comparison with abstract discrete group cohomology is introduced. The augmentation is a morphism here; its being an isomorphism is a separate result and is not assumed to prove naturality.

The blueprint ancestor utility returns None for this existing agent-created chain. Its null ancestor and inherited via list are retained, with the precise paragraph/old parent step recorded. Whole-blueprint searches for homotopy, injective resolution, signed total, bar cochains and condensed bar did not find a duplicate of the complete item. The unit and chapter records were read, as was current main-20261015 paragraph (3) of the direct-images proof. The historical unit record is filed under sec-six-functors while the inherited item is sec-six-functors-basics; neither fixed record was edited. This is the formal bar input to the existing open-direct-image route.

Generic off-unit tools are declared in split_report.tool_uses: the internal/section-module equivalence, closed sheaf tensor-Hom, homotopy uniqueness into injectives, K-injective computation, specified-resolution naturality, ordinary right-derived-functor convention, and signed finite total convention. They supply categorical tools; no geometric route step is replaced.

## Review by NJ

I read current main-20261015 direct-images paragraph (3), which reduces the open-immersion part to the coefficient comparison and does not itself supply an internal bar proof. I checked the actual statements of all cited nodes, and read the compatible bar definition and its Lean data interface to fix the meaning of the first face, internal evaluations, degree-zero augmentation, and normalized inverse-unit comparison. I read Stacks derived.tex at lemma-morphisms-lift (013P), lemma-morphisms-equal-up-to-homotopy (013S), and lemma-bounded-below-injectives-K-injective (070J). I read sites-modules.tex lemma-internal-hom-adjoint-tensor (03EO), and categories.tex lemma-adjoint-exact (0038). I also read the full blueprint proof of lem-sp-kinjective-computes. Those sources support the reused generic inputs; the item-specific signed calculation is written explicitly.

Step 1 uses the product-action statement with H trivial for Grothendieck abelianness and the additive invariants adjunction, the enough-injectives statement for its exact conclusion, the actual internal/section-module equivalence for applying the closed sheaf tensor-Hom statement, and the right-adjoint limit statement for left exactness. Its additivity assertion for internal functions is verified by their evaluation formula, rather than inferred from a definition of flatness or injectivity. All categories are those of the fixed small site and coefficient universe.

Step 2 uses the bar-data statement's explicit natural-family evaluations and its first/interior/last face formulas, together with the action-module statement's equivariant morphisms. The first face requires equivariance; the other faces require only postcomposition. The displayed formula includes p=0, when the middle sum is empty. Equality is tested on all generalized function evaluations, not just ordinary G-points.

Step 3 uses exactly the total definition's finite-diagonal differential and the bar-data degree-zero invariant inclusion. Equivariance makes the augmentation's horizontal differential g x minus x vanish. Chain commutation supplies the vertical equality. Identity and composition follow summand by summand.

Step 4 expands both possible components of dH+Hd. The horizontal coefficients are (-1)^p and (-1)^(p+1), so they cancel using the face computation for h. The vertical coefficients multiply to 1. At q=0, h^0 and its horizontal component are zero while h^1 d_I^0 remains. This checks the degree boundary that an unsigned formula would miss. Step 5 restricts h on fully fixed sections after arbitrary T to S and writes H b_I=b_J Gamma(h); its sign is 1 because augmentation has p=0. These are finite formula calculations from the cited definitions, not hidden external lemmas.

Step 6 applies the existing lift-existence statement in the abelian action category with nonnegative injective resolutions. Its strict augmentation equation is precisely what is required. For uniqueness, the cited node allows an arbitrary quasi-isomorphism alpha into the source of the two maps and a bounded-below injective target: alpha=a, target=J, and the two composites with a are equal. Thus it really gives an equivariant homotopy of the lifts. I checked these hypotheses individually against 013P and 013S; I did not use a definition of resolutions as a substitute for these theorems.

Step 7 uses the derived-category statement's factorization through the homotopy category to identify localized maps. Step 8 writes both inverse equations from the two identity lifts and applies the already established homotopy uniqueness. A composite lift actually lifts the composite; consequently uniqueness proves the composition and cocycle laws. No new node merely restating the resolution-independence clause is introduced.

Step 9 uses the separate hypotheses on U only where they are needed: exactness makes UI a resolution of UN, and preservation of injectives makes its terms injective. The cited K-injective computation statement explicitly includes the bounded-below-injectives assertion; both action and underlying module categories are Grothendieck by step 1. The ordinary right-derived definition explicitly says its unit is invertible on K-injectives. This provides the exact canonical comparisons used next, rather than an arbitrary cohomological isomorphism.

Step 10 uses the specified-resolution naturality statement for its actual inverse-unit normalization. I also wrote the inverse-unit naturality equation explicitly: QF(l)c_L=c_L' RF(v). It applies to Gamma_G on I,J and separately to each internal Hom F_p on UI,UJ. Step 11 substitutes that equation in the actual localized augmentation square. It proves the assertion in D(M_A) before any cohomology functor; it neither replaces a derived isomorphism by degreewise consequences nor assumes the total-augmentation quasi-isomorphism.

I checked delivery-errors B through E against these files. There are no new-node shape, duplicate, leaf, or statement-only issues. Every cited node was opened; every use has a verbatim statement extract in citations.json. The dependency searches found no path back to the item through the reused nontrivial tools. The proof's longest step is 931 characters, so no step crosses the long-step threshold. The item remains self-contained with its original hypotheses and definitions. Small cases checked were p=0, q=0, the trivial group, zero modules/ring, equal lifts, identity maps and composable changes of resolutions. For G trivial the formulas remain the unnormalized bar differential, so positive bar degrees are not incorrectly declared zero. In characteristic 2 the two horizontal terms still add to zero. In all degrees only finitely many total summands occur.

Mathlib searches were run with the mandated msearch.py and their actual records retained. The semantic hits include ordinary Rep bar complexes, signed mapBifunctor homotopies, and InjectiveResolution.descHomotopy/descCompHomotopy; their relevant declarations were read. They supply general ingredients, not a theorem for internal actions over a condensed ring with this augmentation normalization. The local grep hits in Condensed/Module.lean and Condensed/Basic.lean express restriction naturality only. The second semantic phrasing returns the generic resolution homotopies, already represented by the reused nodes. Thus no exact leaf was claimed.

## Not duplicates

No new nodes. Existing resolution and derived-comparison nodes were reused.

## Unfinished work

No mathematical clause of this item remains without a proof step. Downstream unsplit inputs remain owned by their respective items. Server dry run and delivery results are recorded below when available.
