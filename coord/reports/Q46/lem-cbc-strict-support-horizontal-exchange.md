## Worker report

The module `Sheaf.AlgebraicGeometry.StrictSupportHorizontalExchange` states
`AlgebraicGeometry.ProEtale.StrictTower.supportExchange_id` and
`AlgebraicGeometry.ProEtale.StrictTower.supportExchange_comp`, both with `sorry` proofs.
It reuses the existing `compositionF` and `compositionE` without defining either again.
The landed definition node `def-cbc-strict-tower-composition-maps` is added to stmt_deps
as permitted by the standing stage-2 brief. No new node, dependency repair or statement
correction is needed. No disputed statement was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative ring is `B : Type (u + 1)` with `[CommRing B]`, using precisely
  the coefficient universe of the dependency. The small pro-etale site keeps its
  object universe u+1 and morphism universe u. There is no finiteness assumption on B.
- `Derived B X` is the dependency's unbounded derived category of strict towers of
  module sheaves over its actual constant ring sheaf. It is not a tower of separate
  derived objects. There are no finite-origin, boundedness or completeness premises.
- `c : Compactification f` supplies `X`, `V = c.Z`, `j = c.i`, `p = c.g`, the
  factorization `c.comm`, and properness/openness instances. `[QuasiCompact c.i]`
  is exactly the node's extra quasi-compact-open condition. Separatedness and local
  finite type of f follow from its supplied compactification; its quasi-compactness
  follows from quasi-compactness of c.i and properness of c.g. Thus the stated
  separated finite-type situation is represented without adding hypotheses.
- `c₁ : Compactification f₁` and `c₂ : Compactification f₂` are the supplied
  base-changed compactifications. Arbitrary base maps `g` and `h`, ambient maps
  `a` and `b`, and open-side maps `gX` and `hX` form the cartesian grid given by
  `sp₁`, `sp₂`, `sj₁`, `sj₂`. Cartesian presentations include the literal
  `Compactification.baseChange` constructions, and permit their canonical
  identifications without forcing chosen pullbacks to be definitionally equal.
  The outer squares are `sp₂.paste_horiz sp₁` and `sj₂.paste_horiz sj₁`.
  There is no condition such as properness or flatness on g or h.
- `compositionF B c` is definitionally `J B c.i ⋙ R B c.g`, the required F_c.
  `compositionE B c c₁ gX g a sj₁.w sp₁.w sj₁` is exactly the existing
  `whiskerLeft (J B c.i) (exchange B a c₁.g c.g g sp₁.w)` followed by
  `whiskerRight (beta B gX c₁.i c.i a sj₁.w sj₁).hom (R B c₁.g)`.
  This renders the stipulated formula e=(R beta)(E J), with Lean's diagrammatic
  order. The existing exchange is `mateEquiv (adj B c.g) (adj B c₁.g)` on
  `squareG.hom`; beta is exactly the inverse of the open-unit transpose betaInv.
  No arbitrary transformation or isomorphism has been substituted.
- Naturality in every derived strict tower M is carried by the existing type
  `compositionE : compositionF B c ⋙ G B g ⟶ G B gX ⋙ compositionF B c₁`.
  This is a natural transformation, constructed by whiskering and composition.
- `supportExchange_id` states that e for identity base change, followed by
  `whiskerRight (gId B X).hom (compositionF B c)`, equals
  `whiskerLeft (compositionF B c) (gId B Y).hom`. Since these are the actual
  normalized identity isomorphisms, this is exactly identity after canonical
  comparisons. The identity cartesian presentations use `IsPullback.of_id_fst`.
- The first conjunct of `supportExchange_comp` is the node's first displayed
  horizontal equality. The initial factor `whiskerLeft F_c (gComp B h g).hom`
  is c_(g,h)^{-1} F_c: gComp goes from pullback along h≫g to G_g followed by G_h.
  The middle factors are `whiskerRight e_g (G B h)` and
  `whiskerLeft (G B gX) e_h`. The final factor
  `whiskerRight (gComp B hX gX).inv F_c₂` is F_c₂ c_(g',h').
- The second conjunct is the specified beta equality, using the same beta as the
  existing definition of compositionE. Its factors are ambient gComp.hom,
  whiskered beta for the first square, beta for the second square at G_gX,
  and finally open extension of gComp.inv on the open-side maps.
- Both equations are equalities of natural transformations on the actual derived
  strict-tower categories, before evaluation. No evaluation functor or faithfulness
  assertion appears, and no invertibility of proper exchange is asserted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `Derived`, `G`, `R`,
  `adj`, `gComp`, `gId`, and the definitions of constant coefficients and strict towers.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `J`, `jAdj`, and their
  termwise/derived construction.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`: `beta_id`, `beta_comp`
  and the recorded calculus. Its public arrow module provides `squareG`,
  `exchange`, `betaInvApp`, `betaInv` and `beta`, whose definitions were read.
- `Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps`: `compositionF` and
  `compositionE`. Their node is already landed and carries exactly the two-factor
  functor and exchange needed here. This is why it is added to stmt_deps.
- `Sheaf.Paper.ProjectionCompactification`: read `proEtaleRingCompactSupportImage`.
  It acts on modules on a single ringed site; the required strict-tower functor is
  the existing compositionF instead. The supplied Compactification data are shared.
- `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange`,
  `ofIsPullback` and their cartesian open/proper-square properties.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` for the normalized proper
  square mate and `mateEquiv_vcomp`, `mateEquiv_hcomp`, `conjugateEquiv_id` for
  the proof plan and the two recorded Mathlib dependency nodes.
- `Sheaf.AlgebraicGeometry.StrictTowerPullbackSquarePasting`: `squareG_pasting_inv`,
  imported as the remaining stated proof dependency.

Sources read: Stacks sites-cohomology.tex, remark-base-change (07A7) and
remark-compose-base-change-horizontal (0E47), including their displayed maps;
main-20261015 blueprint sec-six-functors-basics/sk-thm-sf-pf-adic/
thm-cbc-complete-proetale.proof.md, final coherence sentence; the item's four
accepted proof steps. The theorem docstrings give that proof plan: pullback-square
pasting, mate pasting, beta pasting, cancellation, naturality and identity.

Edge cases checked: g or h identity; j identity (reducing to proper mate pasting);
p identity; zero or infinite B; empty schemes; arbitrary unbounded tower objects.
All are permitted. The identity statement uses actual gId comparisons instead of
assuming chosen identity pullbacks are judgmentally identical to their source.
Quasi-compactness of intermediate opens follows from their cartesian squares.

Searches run using msearch.py, Q46 and this item:

- leanfinder: "The composite of proper exchange and open extension by zero base
  change satisfies horizontal pasting on derived strict towers". Eight hits on
  algebraic base change, extendScalars and tensor-product associativity; no match.
- loogle: `CategoryTheory.mateEquiv_vcomp, CategoryTheory.NatTrans`. No hits.
  The generic mateEquiv_vcomp is nevertheless reused from its recorded Mathlib node.
- grep: `supportExchange|compactSupport.*exchange|strict.*horizontal`. No hits.
- Earlier sandbox search log: leansearch "Horizontal composition of compact support
  base change maps for unbounded derived strict towers of module sheaves" returned
  NatTrans.hcomp, bicategorical square composition and unrelated base-change results;
  no exact match. Earlier leanfinder and loogle queries also found only generic maps.
- Direct rg in lean/WeilConjectures and lean/Sheaf, plus dag/lean_names_upstream.json:
  supportExchange, compactSupportExchange, strictSupport and the item id found no
  existing full law. A broader search for J followed by R found compositionF and
  compositionE in StrictTowerCompositionMaps. Their definitions and owning node were
  then read in full; they replace the inherited sandbox's duplicate supportImage and
  supportExchange definitions. Existing beta_comp is used for its proof plan.

The added landed definition dependency was checked by traversing stmt_deps and
proof_deps: it has no path back to this item. All definitions are reused, and the only
new declarations are the two named theorem statements with sorry-only proofs.
Validation results are recorded below after running the prescribed wrappers.

## Second reading by Q46

This is the author's separate second pass; no independent agent is claimed, because
this dispatched assignment forbids spawning agents and assigns independent review to
the maintainer. I reread the item, the added definition node and the full module.
The inherited draft duplicated compositionF/compositionE under new names. I removed
those definitions and changed both signatures to the exact existing constructions.
I checked the endpoints and ordering of all four horizontal factors in both equations:
gComp.hom is the inverse of the node's c, and final gComp.inv is c. The two pasted
cartesian proofs have outer maps h≫g, b≫a and hX≫gX. The identity equation has the
same endpoints after the two gId comparisons. The ring, schemes, compactifications,
quasi-compactness and cartesian hypotheses match the node, and no object restriction
or finite-level faithfulness premise is introduced. The resulting statement needs
no mathematical correction. All theorem proofs remain sorry, with complete proof
plans in their source/blueprint docstrings.

Validation: the prescribed scompile.py completed successfully for both the sandbox
and library-form module, without errors or warnings. `autoImplicit false` is enabled;
all universes and variables are explicitly bound. The delivery dry run and delivery
also perform their own required preflight and compilation.
