# Stage-1 delivery: lem-sfb-ringed-bounded-below-descent-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-bounded-below-descent-criterion.json: item, statement unchanged, six-step split following Stacks 0D7U.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-unit-from-cohomology.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep. Stacks 0D7T.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-counit-from-cohomology.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep. Stacks 0D7S.
- citations.json contains the eight step/node pairs and verbatim statement quotations. searches.jsonl records the actual searches; search-results.json retains their complete output.

## Attachments

None. I searched the read-only WeilConjectures source for the exact blueprint tag, bounded-below descent, weak Serre equivalence, and 0D7S/0D7T. The available exact-functor, classical pro-etale, and isomorphism-pullback declarations do not state this general arbitrary-ringed-topos criterion. No sorry declaration was treated as a finished proof.

## WANTED

None. All mathematical sources needed are present in literature/stacks-project/.

## What was wrong

The item had no proof. Its statement agrees with Stacks 0D7U: exact module pullback is the flatness used there; the given derived unit is the precise acyclicity hypothesis; no local cohomological bound is required for the bounded-below result. No statement correction was needed.

The blueprint ancestry inherited from the parent has a null from.node. Running tools/blueprint_refs.py ancestor on this item returns None: the creation chain eventually reaches lem-sfb-admissible-direct-image, whose created.item is the historical module name Sheaf.SixFunctors.CtfStabilityDirectImages rather than a node. I retained the tool-computed null ancestor and complete existing route/place; each new node adds this item to via and names its exact supporting Stacks lemma. This is reported rather than silently changing another node or inventing an ancestor. I read the current latest blueprint unit and chapter alongside the imported unit record. This is a generic descent input below the recorded direct-image alteration argument, not a replacement for a unit step.

## Mathlib searches and duplicate search

Before creating nodes I searched the entire DAG for 0D7S, 0D7T, lemma-bounded-in-image and the mathematical unit/counit and bounded-below concepts; I also ran blueprint_refs.py searches for those tags, bounded in image, bounded below and acyclic. No blueprint node states either supporting criterion. I read the candidate exact-derived-adjunction-bounds node: its lower-bound and full-faithfulness implications do not detect a unit or counit from the separate cohomology sheaves. The classical-derived-counit node concerns a particular scheme comparison and additional classicalness data, not arbitrary ringed topoi.

The actual leanfinder and leansearch results gave exact-functor localization, bounded representatives, degree-zero right-derived comparisons, and unrelated flat-scheme statements; Loogle returned no relevant hit. I inspected Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean, Mathlib/CategoryTheory/Functor/Derived/PointwiseRightDerived.lean and Mathlib/CategoryTheory/Abelian/RightDerived.lean. None gives the bounded-below propagation statement. Both source-grep patterns were additionally run in Algebra/Homology to remove unrelated analytic uses of the words bounded and unit. All search records reproduce queries and outputs of msearch.py; there were no unavailable services in this run.

## Not duplicates

The new statements have distinct source tags 0D7T and 0D7S, absent from existing DAG sources. Neither mentions weak Serre classes, an equivalence on hearts, preservation of cohomology subcategories or the equivalence conclusion of the item. Each concerns one arbitrary bounded-below derived object and the behavior of the canonical transformation on its cohomology sheaves. Thus neither is a clause of the item renamed as a lemma. The heart acyclicity, counit triangle-identity argument, spectral sequence degeneration and final equivalence assembly stay in the item's proof.

## Tool uses

The existing cohomology-of-exact-functor result and standard t-structure are Mathlib leaves. The generic small-ringed-site K-injective/Grothendieck theorem, module adjunction, right-adjoint limit preservation and truncation spectral sequence are declared in split_report.tool_uses. They supply precisely the general homological algebra used by Stacks 0D7U. They do not replace the higher-level unit's direct-image argument.

## Unfinished work

The two new nodes are intentionally statement-only, to be split by their own workers. No other part of this item's natural-language proof is deferred.

## Review by Q42

I read sites-cohomology.tex from the formal descent lemmas 0D7Q/0D7R through 0D7S, 0D7T, 0D7U and the subsequent 0D7V. For the item the source first obtains the unit, then heart acyclicity, then preservation by the cohomology spectral sequence, then the upstairs/counit assertion. The submitted steps keep that order except that I derive the counit on a heart object alongside acyclicity so its canonical normalization is explicit. I checked both new statements directly against their own source lemmas: the source requires only flatness, bounded-below cohomology and invertibility on every cohomology sheaf. The nodes introduce all objects and use exact pullback in place of the same flatness condition. Their conclusions are derived isomorphisms, not just per-degree vector-space comparisons. Their future proof route is finite upper-truncation induction plus the lower-bound preservation of right derived direct image, exactly as in those source proofs; that hint is not smuggled into the statement-only files.

For step 1 I opened the exact-functor-complex-cohomology statement and checked that it supplies a natural cohomology isomorphism for every degree; this is enough to preserve both the lower bound and the chosen heart class. The new downstairs lemma applies because every cohomology object is in B, so the item's own hypothesis gives precisely its unit premise. Step 2 needs no external theorem: choose an inverse-image representative by essential surjectivity on the hearts, apply the assumed derived unit and the functor to the chosen isomorphism, and use the triangle identity followed by counit naturality. In particular this proves the actual canonical counit is invertible; merely choosing some isomorphism f*Rf*F ≅ F would not suffice.

For step 3 I read the three cited statements in full. The first expressly asserts that modules on a small ringed site are Grothendieck and have K-injective models. The second is the module adjunction for arbitrary ringed topoi, not just morphisms induced by site functors. The third states preservation of limits by a right adjoint. Products and kernels therefore give left exactness for the additive module pushforward. The smallness and commutativity assumptions match the item, including the common module universe. This explicit hypothesis verification avoids using the definition of a ringed morphism as if it stated all derived-functor results.

In step 4 I checked that the standard t-structure statement supplies the strictly bounded-below representative required by thm-sp-truncation-e2, even though the item only assumes cohomological boundedness. I opened all clauses of that spectral-sequence node: its E2 formula, vanishing range, finite separated exhaustive filtration and abutment are exactly what the step uses. Step 2 kills every positive column, so the one remaining graded piece identifies H^n(Rf*K) with H^0(Rf*H^nK). No infinite extension of objects in a weak Serre class is being inferred: the filtration in each fixed total degree is finite and has only one nonzero graded piece. Below a every piece is zero. This also avoids an unnecessary extra lemma for spectral-sequence degeneration.

Step 5 uses only the new upstairs statement, whose hypothesis step 2 verifies for every H^qK; I checked that the argument never assumes f* is globally conservative. Step 6 uses full-subcategory restriction and the two already established canonical natural isomorphisms. The definition of an equivalence is then satisfied by the given functors and their actual unit/counit, without a new categorical lemma.

I tested both new statements for K=0, a single sheaf in an arbitrary shifted degree, the identity morphism, the zero ring/topos module category, and complexes with an arbitrary lower bound and no upper bound. None requires a uniform local cohomological dimension. In the item the zero weak Serre subcategories cause no problem, and no closure under arbitrary subobjects or quotients is used. I also checked B--E: statements are self-contained TeX, sources give tags and labels, every non-elementary input is a named node with a verbatim quotation, new nodes have empty proof/dependencies and real recorded searches, and no dependency points back to the item. Each proof step is below 2000 characters. No SGA source, Lean edit, compiler, Lake invocation, local forbidden checker, or repository write was used.
