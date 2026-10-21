## Worker report

Files written:
- `dag/nodes/sec-six-functors/lem-sf-completed-coefficient-pullback-linearity.json`: statement item split into seven steps; no new nodes, no new Mathlib leaves.
- `citations.json`: fourteen verbatim statement quotations, one per cited node per step.
- This report. The search command maintains `searches.jsonl` in this sandbox.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint id and for completed coefficient pullback/linearity found no declaration stating every clause. Ordinary constant-coefficient pullback linearity in `SixFunctors/ProEtale/FiniteCoefficient/Derived/ScalarExtension.lean` does not state the inverse-limit scalar square or the intrinsic-completeness assertion.

WANTED: none.

The item had no proof or proof dependencies. Its statement is correct and was retained verbatim. Inherited Q20 Mathlib records were preserved, and five actual Q34 searches, including a second semantic phrasing, were appended from the search log. The search hits cover ordinary module pullback, its free-module comparison or unrelated scalar pullbacks; none gives this item in one specialization. The exact-linear-derived-functor fact is already an existing Mathlib leaf and was reused. No statement dispute or route error was found.

Unfinished work: none at this level. Existing unsplit dependency nodes remain their owners' work.

## Sources and existing-node searches

Read the chapter and unit records (`sec-six-functors`, `sk-rem-sf-pf-done`), the current blueprint `main-20261015/.../def-wf-tensor-product.md` in full, and the current DAG parent's expanded statement/proof. The blueprint itself supplies only the tensor-Frobenius shorthand; the scalar-square calculation here is agent-written, and `proof_origin.by` says so. Read Stacks `proetale.tex`, Tag 09A5 (`section-morphism`), `sites.tex`, Tag 0H7J (`example-constant-sheaf`), and `sites-modules.tex`, Tag 03D7 (`lemma-adjoint-pullback-pushforward-modules`). Also read Tag 03CR (`lemma-morphism-ringed-topoi-comes-from-morphism-ringed-sites`) for the presentation-equivalence context. Tag 03CR alone is not asserted to prove the exact-module-equivalence refinement: that is the explicit statement of the existing generic transport node used below. Read Mathlib `Algebra/Homology/DerivedCategory/ExactFunctor.lean`, lines 120-125, which supplies the existing exact-linear-derived-functor leaf.

Searched the whole DAG by coefficient/completion/linearity/adjunction notions and tags; read all statements used in the final proof. Ran blueprint search for `pullback linear`, `coefficient scalar`, and `complete pullback`, all with no matching imported blueprint node; `ancestor` identifies `def-wf-tensor-product`. There is no new node to justify against a shared-tag duplicate. The two main reusable results found were the exact ringed-presentation transport theorem and the existing automorphism-completion-unit comparison in this same tensor-Frobenius unit.

## Tool uses

`lem-weil-pbc-ringed-presentation-transport` is an off-unit generic tool: Step 5 takes only its assertion that the module adjunction for an equivalence of ringed topoi is an exact equivalence. It replaces no step of the tensor-Frobenius unit. This use is declared in `split_report.tool_uses`. The derived-linearity citation is an existing Mathlib leaf. No SGA route is used.

## Review by Q34

I checked the original statement against the actual coefficient construction, not an identification of constant and completed sheaves. The scheme is an automorphism, so the inverse-image limit comparison is an isomorphism, and naturality applies to every ring quotient map `A -> A/I^n`. The datum supplies a commutative Noetherian coefficient ring, additive-torsion residue ring, finite perfect quotients and the small-site universes; no completeness of the original ring A, constructibility, boundedness, principal ideal, or nonzerodivisor condition was added. No new node was created, so there is no new node with a separate source or untested hypothesis.

Step 1 uses the actual compatible-family limit and projections in `def-weil-pbc-adic-coefficient-datum` and both the limit-comparison and constant-map naturality clauses of `lem-weil-proetale-isomorphism-inverse-image`. These are explicitly in those statements. The proof writes the equality after each quotient projection; joint injectivity is immediate from the specified compatible-family model. This corrects the possible gap of claiming preservation of scalars merely from the existence of some coefficient isomorphism.

Step 2 uses `def-weil-proetale-inverse-image`, whose statement specifies the unit/counit adjunction and defines the constant structure map as the adjunct of the map fixing constant sections. I checked the types of the two scalar squares: both routes of the first start at the inverse image of the constant sheaf and end in the completed ring, and both routes of the second start at the constant sheaf and end in direct image of the completed ring. The unit-naturality equality in the proof gives the second square, and evaluating its actual maps gives the required equation over `u_e(U)`.

Step 3 uses the direct-image section formula in that same definition, the ring-action clause of `lem-weil-pbc-ringed-topoi-module-adjunction`, and bilinear composition in `def-weil-linear-category`. The adjoint square identifies the scalar acting on a direct-image section with the scalar on the original section over the base-changed object. The proof displays the sectionwise equality and addition formula; it uses no tensor comparison or hidden flatness assertion.

Step 4 uses only the natural Hom bijection stated by the module-adjunction node and the definition of a linear category. I checked the calculation for the specified left adjoint: `alpha(h)=unit;G(h)` is linear because G is now known linear. Naturality of its module unit gives `alpha(F(u))=u;unit`; comparison for a scalar multiple and for a sum, followed by injectivity, proves the two claims. In particular the proof does not assume left-adjoint linearity in proving linearity of this bijection.

Step 5 uses the inverse-image equivalence/limit comparison stated by `lem-weil-proetale-isomorphism-inverse-image` and the first exact-equivalence clause of `lem-weil-pbc-ringed-presentation-transport`. I checked that the ringed-equivalence hypothesis holds with the actual c_e from Step 1 and that the cited transport theorem asserts exactness of this module adjunction, rather than merely constructing ring objects. It applies on small sites and supplies preservation of finite limits and colimits.

Step 6 uses `lem-weil-linear-abelian-derived-category` for the induced Hom scalar structure and `lem-cbc-exact-linear-derived-functor` for additivity and scalar linearity of the termwise derived functors. Its exactness, additivity, ring-linearity and derived-universe hypotheses are all available from the preceding steps and datum. The Mathlib source read above states the linearity instance for that exact derived map. Thus the claim concerns all derived morphisms, without trying to represent every morphism by an unlocalized chain map.

Step 7 uses exactly the complete-subcategory preservation clause in `lem-sf-automorphism-completion-unit-comparison`, and the unit-based completeness definition in `def-weil-pbc-intrinsic-completion`. The former explicitly allows every finite generating tuple and every representative without boundedness. I checked it uses the same coefficient isomorphism and ordinary derived pullback as this item. Full-subcategory restriction then retains the Hom operations from Step 6, which gives both final displayed formulas. No proof internals of that comparison node were used.

For small cases I checked the identity automorphism (both squares become scalar-map identities), the zero coefficient ring and empty scheme (all section formulas still hold), `b=0,1`, zero morphisms and sums, and `I=0` with the empty generating tuple. The completion comparison explicitly permits the tuple chosen in the statement, and no division or cancellation by a scalar occurs. Every step is shorter than 2000 characters. Sections B-E were checked: no new statement-only node needed, no duplicate or clause moved to a new node, no unrecorded non-elementary appeal, no use of another node's proof, no new hypothesis, and no implicit replacement of the coefficient category. All named non-elementary tools are existing nodes and are quoted in citations.json.
