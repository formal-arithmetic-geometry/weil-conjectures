# Worker report: lem-sf-native-weil-localizing-brown-adjoints

## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-weil-localizing-brown-adjoints.json`: statement split into nine proof steps, reusing existing nodes; Mathlib verdict no match.
- `citations.json`: sixteen step/node entries, each checked as a verbatim substring of the cited statement.
- No new DAG nodes and no new Mathlib leaves. `searches.jsonl` records the actual searches; `write_split.py` is sandbox-only preparation material.

## Attachments

None. Searches in `lean/WeilConjectures/` by the exact blueprint tag and native Weil/localizing terminology produced no declaration of this statement. General Brown implementations in `CategoryTheory/` do not state the native coefficient/fixed-pair assertion and its hull equality. No declaration with a sorry was treated as an attachment.

## WANTED

None for this assembly. The proof uses existing DAG statements for the non-elementary inputs; no new source-dependent obligation is introduced.

## Corrections and provenance

The imported item had a statement but no proof. Its statement and statement dependencies are unchanged. The proof separates the definition-level hull argument from the existing native functor comparison and the existing solution-set Brown inputs. In particular it does not cite compact-generator Brown representability for generators for which compactness is not supplied.

The blueprint source read was `main-20261015/.../cor-coef-verdier-weil-equivariance.proof.md`, final exceptional-adjunction sentence, together with `sec-six-functors-basics/sk-prop-int-brown/sk-prop-int-brown-construction.proof.md`, its open/proper bullets and final paragraph. I also read `sk-thm-existence/det-existence-localizing.proof.md`: its compactness argument is not the input used here. The existing generic solution-set nodes state the version appropriate for this item. This assembly is marked agent-written.

`blueprint_refs.py ancestor` reports an inherited null `blueprint.from.node` on the item. The live parent `thm-sf-weil-compact-direct-image-right-adjoint` now names the imported anchor `lem-a1-local-boundary-duality`, and its proof steps 5--6 are the place this obligation serves. I retained the item's maintainer-owned ancestry fields and recorded that breadcrumb in `split_report.blueprint`. Whole-blueprint searches for localizing Brown, solution-set, and localizing Weil did not find an exact imported statement. The broad Weil search also confirmed that the stage-level equivariance statements use different categories; those are not exact attachments or duplicates.

## Mathlib search reading

The actual item searches are appended to `mathlib_searches` directly from the search command's log. LeanFinder was tried with a native-sheaf phrasing and a general set-generated triangulated phrasing; LeanSearch with a right-adjoint/solution-set phrasing, Loogle with `CategoryTheory.Functor.IsLeftAdjoint, CategoryTheory.Pretriangulated`, and grep with `[Bb]rown|[Ww]ell[Gg]enerated|[Ww]eil` in CategoryTheory. All services answered. The first semantic results were sheaf representability and condensed sheaf colimits; the second returned derived adjunction and exactness of existing adjoints. These do not assert existence of the requested adjoints or the Weil-hull identification. The LeanSearch solution-set hit `isRightAdjoint_of_preservesLimits_of_solutionSetCondition` is a limit-preserving adjoint-functor theorem, not the cohomological solution-set theorem on these hulls. I read its declaration in `Adjunction/AdjointFunctorTheorems.lean:82` and the candidate `Adjunction.isTriangulated_rightAdjoint` in `Triangulated/Adjunction.lean:60`; both require hypotheses or existing adjunction data not supplied by the item. Grep returned author-name matches only. Existing partial-adjoint assembly is already the DAG Mathlib leaf `lem-sfb-right-adjoint-from-objectwise-representability` and is cited rather than recreated.

## Not duplicates

No new nodes. Existing obligations reused include the native compact-support sums lemma, native induction/forgetting comparison, cyclic free resolution, set-generated solution-set theorem, solution-set representability theorem, and the objectwise-representability adjoint leaf.

## Review by Q13

I read delivery-errors B--E in full and checked the following actual mathematical uses against the node statements. I read the chapter and unit records: the unit gives no separate proof steps to replace, and the work implements the exceptional-adjunction input of the supplied parent. No SGA source is used.

1. The native induction-comparison statement explicitly gives both Grothendieck hearts, coproduct-preserving conservative forgetting, Frobenius preservation, triangulation and the natural derived comparison beta. I use these clauses only. Its hypotheses match the same coefficient sheaf, exact chosen compactification, and relative separatedness as this item; it expressly permits absolute nonseparatedness. I checked the Grothendieck derived-coproduct statement includes unbounded complexes and the empty family. The generic K-injective statement applies to both Grothendieck hearts, unlike the ringed-site-only resolution theorem. Derived local smallness then applies to both hearts; its actual project source `GrothendieckAbelian/HasDerivedCategory.lean:64` and surrounding construction was read. Thus the solution theorem uses the same Hom/coproduct universe, not an unnoticed enlarged index category.
2. Essential smallness is literally a clause of the locally-finite adic realization statement. The free-resolution statement gives the exact derived adjunction and the integer-sum formula. The two inverse-image classes used in this step are localizing because the functors preserve triangles and coproducts; minimality gives their inclusions. This is the explicit short argument, not a new lemma node. Frobenius preserves the constructible strata and local finite-free models, also for the inverse automorphism, so every integer summand is in the geometric hull.
3. The cyclic-resolution statement literally supplies the distinguished triangle with two copies of IUK, for an arbitrary unbounded derived K. Applying cone closure yields the reverse hull inclusion. I checked the native framework's definition of bounded constructible Weil cohomology: exact forgetting gives bounded constructible underlying cohomology, so every such complex is covered. No replacement by fixed pairs in the derived category occurs.
4. The existing compact-support sums statement uses exactly B_T of locally finite continuous functions, the actual sheaf functors, and localizing domains; it allows absolute nonseparatedness. Quasi-compact locally finite-type schemes here are finite type, and the compactification space is finite type by properness over the finite-type base. The native comparison is natural on derived morphisms, so after forgetting, the canonical coproduct comparison has exactly F of the underlying coprojections. Its invertibility follows from the geometric sums statement and is reflected by conservative forgetting. This proves the equivariant comparison, rather than assuming an ambient equivariant adjoint.
5. I read Stacks `derived.tex`, Tag 05QW, `lemma-projectors-have-images-triangulated`: countable coproducts imply split idempotents. The corresponding existing node requires only the inherited pretriangulated/shift structures and countable coproducts, all present in each full hull. No compactness is needed.
6. I read both clauses of `lem-weil-pbc-hom-out-of-triangle-exact` and Stacks Tag 0149, `lemma-representable-homological`. Applied to the image triangle and its rotations they give exactly the contravariant cohomological sequence. Restriction along coprojections gives the product bijection, by the coproduct universal property. This checks the actual functor H_M, for arbitrary M in the target hull.
7. The set-generated-derived-solution-set statement allows an arbitrary essentially small generating class in a Grothendieck derived category, and asserts exactly the direction z=H(a)(b_i) with a:Z->B_i. I verified both instantiations: S_X in D(A_X) and its small image I_X S_X in D(W_X), with the minimal hulls defined in the item. There is no compact-generator premise or separatedness premise in that generic statement.
8. The cohomological-solution-set-representability statement requires local smallness, coproducts, split idempotents, cohomologicality, the product property, and a small solution family. Steps 1 and 5--7 supply these hypotheses individually. Its conclusion is set-valued representability, which is exactly the hypothesis needed by the next node.
9. I read the entire objectwise-representability adjoint statement and Stacks Tag 0A8B, `categories.tex`, `lemma-adjoint-exists`: representability for every target object assembles an ordinary right adjoint natural in both variables. Thus representation by the right-adjoint value and existence of a functor on the stated hulls both follow.

All sixteen citations have verbatim statement quotes in `citations.json`. Off-unit generic tools are declared in `split_report.tool_uses` with their purposes. No new lemma restates a clause of this item; the actual inclusions and equivariant coproduct calculation are written in the proof. Every proof step has fewer than 2000 characters, so none hides a long subsidiary comparison. No new unsplit nodes, hollow definitions, or Lean code are produced.

Small-case checks: the empty scheme and zero generator class give zero hulls and zero representing objects, compatible with every step; the empty coproduct is preserved by the same conservative test. The identity morphism with identity compactification gives the identity functor and its identity right adjoint. For a point with trivial Frobenius, the free object is the integer Laurent sum and the displayed cyclic cone is precisely the stated free resolution; taking an object with constructible underlying cohomology requires no compactness of that free object. Arbitrary unbounded K in the hull comparison is allowed by the cyclic-resolution statement. Relative separatedness has not been replaced by absolute separatedness.

## Unfinished work

None in this one-level split. The previously existing unsplit native induction-comparison obligation remains an existing cited obligation, not a claim of a completed Lean proof. Server checks and direct delivery are the final validation.
