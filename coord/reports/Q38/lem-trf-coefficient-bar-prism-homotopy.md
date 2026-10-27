## Worker report

The module `Sheaf.CategoryTheory.CoefficientBarPrismHomotopy` states
`CategoryTheory.CoefficientBarPrism.exists_realization`, with one postponed proof.
All raw maps have actual data. `Realization` packages the precise simultaneous
existence assertion; nothing is selected from its inhabitation theorem. There is
no statement correction and no disputed mathematical clause.

Hypotheses and clauses, in the namespace `CategoryTheory.CoefficientBarPrism`:

| Node text | Lean rendering |
| --- | --- |
| Size convention; arbitrary small categories E,D | Explicit `universe u v r s d`; `{E D : Type u} [SmallCategory E] [SmallCategory D]`. The common universe is the chosen bound, not a cardinality restriction. Module objects have universe `max u v`; ring universes `r,s` and localization universe `d` are independent. No auto-bound implicits (`set_option autoImplicit false`). |
| R commutative | `{R : Type r} [CommRing R]`. The final semilinear statement also binds `{S : Type s} [CommRing S]`. |
| Module presheaves, equivalently modules for the identity-cover topology | The existing `PresheafBar.Presheaves.{u,v} E R`, definitionally `Eᵒᵖ ⥤ ModuleCat.{max u v} R`, is reused. It is precisely the presheaf description in the node; the sheaf and site dependency modules are publicly imported. |
| C = colimit over Eᵒᵖ | The existing `PresheafBar.C` / `CategoryTheory.Limits.colim` supplies this notation. It is contextual in this node: no conclusion mentions or identifies a derived colimit, and no such extra claim is introduced. |
| K^(-n) is the direct sum over chains, positive terms zero | Existing `PresheafBar.colimitTerm F n` and `colimitι`; `Realization.sourceTerm` and `targetTerm` are isomorphisms FROM these actual sums into `K.X (-n)` and `L.X (-n)`. `positive` asserts both positive terms are zero. These coordinates fix all subsequent maps. |
| Alternating differential; delete U_(n-j), compose internally, restrict only at last face | Existing `PresheafBar.colimitFace`, `deleteRight`, `colimitDifferential`, and `categoryBarDelete`. `sourceDifferential` and `targetDifferential` pin the cochain differentials to those maps. `K` and `L` are genuine `CochainComplex` objects, so d²=0 is part of their structure. |
| v,w and eta:v=>w | `(v w : E ⥤ D) (η : v ⟶ w)`. |
| F,G and natural t:F=>w^-1 G | `(F : PresheafBar.Presheaves E R)`, `(G : PresheafBar.Presheaves D S)`, `(t : F ⟶ w.op ⋙ G ⋙ ModuleCat.restrictScalars φ)`. Taking S=R and phi=id gives exactly the same-ring case. |
| The natural coefficient map G(eta)t | `t ≫ Functor.whiskerRight (NatTrans.op η) G` in `Realization`; its type is the stated natural transformation to `v.op ⋙ G`. In the final assertion G in this expression is the restricted presheaf. |
| K(w,t), K(v,G(eta)t) have the displayed generator formulas and are chain maps | `reindex` is constructed by `DirectSum.toModule`, using `t.app (op c.right)` followed by the summand inclusion for `c ⋙ f`. `fw`, `fv` are cochain maps, normalized by `wFormula`, `vFormula`. |
| The chain defining p_r | `vertex` uses v up to and including position r and w afterwards; `Fin.predAbove` duplicates vertex r. `edge` uses v and w on their respective arrows, and eta at the crossing (the adjacent duplicate arrow is identity before applying w). `chain` uses Mathlib's `mkOfObjOfMapSucc`. Thus c is the chain U_n -> ... -> U_0, and r counts FROM THE LEFT as in the node. |
| p_r sends the coefficient to t_(U_0)x | Actual `insertion`, defined by `DirectSum.toModule` and the actual prism-chain generator. `coefficient` transports along the final identity arrow at wU_0; it is only the dependent-type identification of that endpoint. It neither applies eta nor an extra restriction before the face. |
| H_n = sum (-1)^r p_r | Actual `signed`, an integer-scalar sum over `Fin (n+1)`; no cardinality hypothesis on the set of chains. |
| d_j p_r = p_(r-1) d_j for j<r | `before`, writing the original degree as n+1 and r as `a.succ`. Its hypothesis is `j.val ≤ a.val`, i.e. j<r. The equality includes j=a (the face immediately before the crossing). |
| d_j p_r = p_r d_(j-1) for j>r+1 | `after`, writing the original degree as n+1, r=`a.castSucc`, and the prism face as `j.succ`. Hypothesis `a.val < j.val` is exactly j_prism>r+1. The terminal coefficient face is included. |
| d_(r+1) p_r = d_(r+1) p_(r+1), r<n | `junction`, with both insertion indices `a.castSucc` and `a.succ`, and the common face `a.castSucc.succ`. |
| d_0 p_0 = K(w,t) | `first`. |
| d_(n+1) p_n = K(v,G(eta)t) | `last`; the right side includes the actual contravariant coefficient map, not the original coefficient. |
| dH+Hd equals K(w,t)-K(v,G(eta)t) | `equation` in strictly negative cochain degrees and `degreeZero` in degree zero. Composition is written in Lean's left-to-right convention. |
| H_(-1)=0 and whole-complex chain homotopy | `homotopy : Homotopy fw fv`, normalized in every nonpositive degree by `homotopyFormula`, and `augmentedZero : homotopy.hom 1 0 = 0`. All other positive-source terms are zero by `positive`. Mathlib's homotopy convention is fw=dH+Hd+fv, the stated sign. |
| Degree-zero coefficient-sensitive formula | `degreeZeroGenerator`, quantified over every U and x, explicitly subtracts `(vU,G.map (eta.app U).op (t_U x))` from `(wU,t_U x)`. |
| Equal maps in D(R) | `derivedEquality : DerivedCategory.Q.map fw = DerivedCategory.Q.map fv`; the localization structure is bound explicitly with `[HasDerivedCategory.{d} (ModuleCat.{max u v} R)]`. |
| Ring map R->S and semilinear t, after scalar restriction | The final theorem applies the ENTIRE `Realization`, including every face and formula, to `G ⋙ ModuleCat.restrictScalars φ`. Thus no flatness, injectivity of phi, or restriction-preserves-projectives assumption is present. Restricted S-module direct sums have the same finitely supported tuples and actions as the displayed R-module sums. |
| Identities, empty categories, no finiteness assumption | There is no `Nonempty`, `Fintype`, `Finite`, or nondegeneracy hypothesis on E or D; `ComposableArrows` permits every identity arrow. |

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`. The node itself chooses the equivalent ordinary functor-category description on the bottom topology; no second sheaf definition is made.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `CategoryTheory.Precoverage.IsSiteForCoverings`. The identity-cover topology and sheaf description remain the recorded convention.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; the full signatures and size conventions were read.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `Cocone`, `IsColimit`; ordinary colimit is contextual here, not an extra theorem requirement.
- `Sheaf.CategoryTheory.DerivedColimitBar`, owned by `def-trf-derived-colimit-bar-system`: `categoryBarDelete` (and the recorded face-coefficient convention). This landed definition node is added to stmt_deps. Its `CategoryColimitBarSystem.homotopy` is NOT used to prove or assume this result.
- `Sheaf.CategoryTheory.PresheafBarResolution`, owned by the new existing-definition node `def-trf-presheaf-bar-complex`: `PresheafBar.Presheaves`, `colimitTerm`, `colimitι`, `deleteRight`, `colimitFace`, and `colimitDifferential`. This definition node replaces the resolution theorem node in stmt_deps, as requested by the H2 return. Neither `Resolution` nor `exists_resolution` is used.
- Mathlib `ComposableArrows.mkOfObjOfMapSucc`, `Fin.predAboveOrderHom`, `DirectSum.toModule`, and `ModuleCat.restrictScalars` give the actual helper data; their source signatures were read before use.

Only helpers belonging to this prism assertion are introduced in Lean. The new
definition-ownership node below registers the already published raw bar constructions. Every new declaration is recorded in
`lean.declarations`. All statement dependency modules are direct public imports.
`def-weil-size-convention` has no Lean module by design, and is rendered by the
explicit universe binders.

Source read: `literature/stacks-project/sites-cohomology.tex`, Example
`example-morphism-categories` (08PH), lines 10117 onward, and the complete ten-step
DAG expansion. The source supplies the coefficient generator map; the node
explicitly identifies its extra prism identities as an agent expansion. The item
is auxiliary (`blueprint.is=null`), not a blueprint unit's statement. No older
blueprint snapshot was used.

Edge cases checked before and after writing: at n=0 the prism chain is exactly
vU --eta_U--> wU, its first face leaves t_U x and its last face applies G(eta_U).
At n=1, r=0 and r=1, the common junction composites agree by eta naturality;
the before identity must include j=0 for r=1 (an initial draft excluded this
boundary, corrected before delivery). The after identity includes the last
coefficient face when r<n. Identity eta and repeated identity arrows are allowed;
no normalized-nerve quotient is taken. With empty E, each chain-indexed source
sum is zero. If D is empty, the functor hypotheses force E empty. The zero ring
and zero presheaves give zero maps, without a nontriviality assumption. Every
sum defining H has exactly n+1 terms even for infinite categories. No arbitrary
map is substituted for a canonical coefficient restriction.

Searches for an existing statement (all msearch calls executed for this item):

- LeanFinder: `A natural transformation of functors gives a chain homotopy on the category bar complex with contravariant module coefficients` — eight results, led by Dold-Kan `natTransHσ`, `natTransPInfty`, `natTransP`, `natTransQ`; none constructs this coefficient prism or states its five identities.
- Loogle: `CategoryTheory.SimplicialObject.Homotopy` — twelve hits, including `Homotopy`, `h`, `h_last_comp_δ_last`, and `h_zero_comp_δ_zero`; these require supplied simplicial homotopy data and do not define these module-coefficient insertions. Read the record's endpoint conventions; they do not remove the need for the stated formulas.
- Mathlib grep: `barComplex|simplicialReplacement|prism|SimplicialReplacement` — thirteen results for representation-theoretic group bar complexes, not arbitrary categories with contravariant module coefficients.
- LeanSearch: `category bar complex direct sum over composable arrows with presheaf module coefficients` — eight results including generic composable arrows, presheaf-module maps and preadditive sums; no matching prism theorem.
- Project rg on `lean/WeilConjectures` and `lean/Sheaf` for `barComplex|simplicialReplacement|prism|SimplicialReplacement|coefficientBar` — found the downstream `DerivedColimitBar` assertion and the landed `PresheafBarResolution` direct sums, which are reused. Strict-poset and profinite-function prisms have different objects and coefficient directions. A search for the exact item id in `lean/WeilConjectures` found no declaration. DAG search found the already landed `def-trf-derived-colimit-bar-system`, so no duplicate node was created.

Import-cycle advisory for subsequent proof-import maintenance: do not add the new
module as a proof import of `Sheaf.CategoryTheory.DerivedColimitBar`; its shared
definitions are already public imports of `PresheafBarResolution`. The DAG has
separate definition ownership and no dependency cycle; module-level proof imports
must use the rule-7 cycle exception, as already noted by the Q83 review.

## Repair of returned head 54e66eb84b94

H2 is repaired by adding `def-trf-presheaf-bar-complex`, with `existing: true`
on the unchanged `Sheaf.CategoryTheory.PresheafBarResolution` module. It lists
all 25 raw definitions and abbreviations preceding `Resolution`. The prism
item's `stmt_deps` replaces `lem-trf-augmented-presheaf-bar-resolution` by this
new definition node, retaining `def-trf-derived-colimit-bar-system`. The new
node's definition dependencies include that bar-system definition node, for
`categoryBarDelete`, and the size, sheaf, site and ordinary-colimit nodes.
It has no statement or proof dependency on the resolution theorem.

The retained item node was compared with the current shared node: only its
`lean` and the two documented definition dependencies differ. All mathematical
fields are preserved. The prism Lean module is unchanged from the returned
head. The current server source of `PresheafBarResolution` was read using
`scompile.py --source`; its raw definitions have the same signatures and
formulas as the local published source. No live file was modified. Delivery
wrappers prepare the new commit on the current server branch.

## New nodes

`def-trf-presheaf-bar-complex` defines the explicit raw presheaf and category
bar terms and linear maps of Stacks 08PF--08PG, with the incoming-arrow,
augmentation, insertion and comparison expansion already published for the
presheaf-resolution theorem. It does not assert inhabitation of `Resolution`.
The primary declaration is `CategoryTheory.PresheafBar.colimitTerm`; the
`lean.declarations` list records the 25 existing raw definitions, and excludes
both `Resolution` and `exists_resolution`. There is no new module and no copied
construction. This is the definition-ownership repair required by H2, following
Q44's `def-trf-derived-colimit-bar-system` precedent.

The new node matches the existing declarations clause by clause:

| Clause | Existing declaration in `CategoryTheory.PresheafBar` |
| --- | --- |
| Small E, commutative R, independent size bound, coefficient presheaves | `Presheaves`, with the existing explicit universes u,v,r |
| L_U(M)(V), summand inclusions, restriction and coefficient maps | `freeTerm`, `freeι`, `freeRestriction`, `freeMap` |
| B_n(F)(V), K_n(F), their inclusions and L-summand inclusion | `term`, `colimitTerm`, `ι`, `colimitι`, `summandMap` |
| Incoming-arrow restriction and natural coefficient maps | `restriction`, `termMap`, `colimitTermMap` |
| Left and right connecting arrows from chain deletion | `deleteLeft`, `deleteRight`, using `categoryBarDelete` from the existing bar-system definition |
| Evaluated and category-bar faces, including coefficient restriction | `face`, `colimitFace` |
| Alternating sums, with n+2 faces from degree n+1 to n | `differential`, `colimitDifferential` |
| Degree-zero augmentation and two evaluated insertions | `augmentation`, `contraction`, `augmentedContraction` |
| Forget incoming arrow, colimit functor, normalized augmentation into colimit | `comparison`, `C`, `colimitAugmentation` |

Searches for this new definition owner, all made for this repair:

- LeanSearch: `presheaf bar complex direct sum over composable arrows contravariant module coefficients` returned generic `PresheafOfModules` declarations and `Rep.barComplex`; the group-representation construction is not the category-with-contravariant-coefficients formula.
- Loogle: the unqualified `ComposableArrows` query was rejected; the qualified retry `CategoryTheory.ComposableArrows` returned 12 indexing declarations, including `left`, `right`, `mk₀`, `mk₁` and `arrowEquiv`, not these bar terms or faces.
- Mathlib grep: `PresheafBar|colimitTerm|simplicialReplacement` in `CategoryTheory` returned no hits.
- Project grep with the same pattern in `lean/WeilConjectures` and `lean/Sheaf` found no upstream match and the existing `PresheafBarResolution` raw constructions, which are reused.
- DAG grep for `presheaf-bar-complex|PresheafBar` found only the resolution theorem node, not a definition owner. Both `tools/blueprint_refs.py search presheaf-bar-complex` and the search for `presheaf bar` returned zero blueprint matches. `ancestor` returned `lem-trf-local-term-locality`, used in the new node's blueprint record.

The exact msearch result records are retained in the new node's
`mathlib_searches`. The new node's source was reread at
`example-category-to-point` and `example-left-derived-colimits` in
`literature/stacks-project/sites-cohomology.tex`. The stated raw maps use
real direct-sum constructions and select no data from a postponed theorem.

## Second reading by Q38

Final self-check of the retained Lean and both node records, performed by this
worker under the dispatched instruction not to start other agents. The H2
mismatch was the theorem-node ownership of raw definitions; replacing that
edge and adding the exact existing-definition record repairs it. The primary
signature in the new node is copied verbatim from `def colimitTerm` to `:=`.
Every listed declaration is a `def` or `abbrev` before `Resolution`, and all
five raw definitions identified by the return are covered. The new node's
statement-dependency ids are exactly its bracket citations; all are definition
nodes. Its source, ancestor, via path, chapter and unit were checked against
the item. No new theorem or resolution assumption is introduced.

For the unchanged prism statement, the raw sum terms are normalized by
`sourceTerm`/`targetTerm`; both alternating differentials and zero positive
terms are fixed. `before` includes j=r-1, `after` includes the coefficient
face, and `junction` compares the two consecutive insertion positions. `first`
and `last` have the required w and v endpoints, with G(eta) at the latter.
`equation` and `degreeZero` have the required w-minus-v sign, and
`degreeZeroGenerator` explicitly retains the coefficient restriction.
`homotopyFormula` has degree -1, `augmentedZero` gives H_(-1)=0, and
`derivedEquality` is in the derived category of restricted R-modules.
The final theorem applies every clause to `G ⋙ ModuleCat.restrictScalars φ`.
The universes remain independent and the empty-category, zero-module,
identity-arrow and n=0 cases remain admitted. No Lean changes were needed.

Validation: `scompile.py Q38 lem-trf-coefficient-bar-prism-homotopy` compiled
the unchanged prism module cleanly in sandbox mode (19.7 s) and its actual
library mode (8.2 s). The repaired packet then passed `deliver2.py --no-push`:
`OK (dry run): commit 12495abdabd passes the preflight and compiles; nothing pushed`.
This validates the new existing-definition record and both node records as well
as the final imports; the earlier server-storage failure is resolved. The
subsequent delivery recompiles and checks this final report update.
