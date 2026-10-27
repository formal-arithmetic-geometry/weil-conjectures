## Worker report

The module `Sheaf.Paper.TwoOpenTensorChainNormalization` states the two-open
normalization lemma in the published fixed-scalar ordinary unbounded derived
categories. It supplies seven real helper definitions and two sorry-only theorem
statements, all owned by this node. The node changes only in `lean`. No new node,
dependency repair, or statement correction is needed.

The source is the agent-formulated open-extension calculation retained verbatim
in the node's seven proof steps, serving the symmetry reduction in blueprint
main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md. That blueprint proof was opened and read.
Stacks Tag 0GL1 (`sites-cohomology.tex`, lemma-j-shriek-and-tensor, line 4578)
provides the underlying unbounded derived projection formula; Tag 0E8I
(`sites-modules.tex`, same label, line 4051) provides its module version.
Both source passages and their proofs were read. This node is an explicit agent
calculation, not a claim that those sources literally state both chains.

Hypothesis and clause correspondence:

- The finite datum k,A=A_(E,n), including n>=1, is the binder
  `P : PurityFiniteSetting.{u}` and `P.Coefficient`. This uses the published
  standard ULift of the genuine quotient P.Ring, not a new coefficient ring.
  Its finiteness is the existing `settingCoefficientFinite P` instance.
- Separated finite-type k-schemes are `T S : Over (Spec (.of P.field.k))`
  in the rho statement and `W V Y` over that same base in the chain statement.
  Each carries `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its
  structure map; the last two are precisely finite type.
- The opens are `i : T ⟶ S`, or `w : W ⟶ V`, `v : V ⟶ Y`, with
  `IsOpenImmersion` on their underlying maps. The composite u is literally
  `w.left ≫ v.left`; Lean composition is left-to-right, so this is v after w.
- D_A is the existing `FiniteD P.Coefficient` = DerivedCategory of pro-etale
  sheaves valued in ModuleCat. K,L,F,H,Q have exactly the ambient schemes
  of the node. No boundedness, constructibility or Tor-amplitude predicate occurs.
- Delta is the given isomorphism
  `(pull P.Coefficient v.left).obj H ≅ (finiteShriek P.Coefficient w.left).obj Q`.
  It is not chosen or replaced by an identity or an arbitrary new comparison.
- Rho is the existing `FiniteOpenProduct.rho`, whose body is precisely sigma,
  gamma, then extension of sigma, in the stated order. It is not redefined.
  `twoOpenRhoNormalization` gives its IsIso assertion and its actual restricted
  arrow. The right side is mu, then identity tensor inverse eta, then eta on
  the target tensor. Thus the restriction becomes the identity under the stated
  comparisons, with the signed braidings retained by the existing definition.
- `twoOpenUnitIso` packages the actual unit with its inverse using the existing
  `Adjunction.isIso_mapDerivedCategoryAdjunction_unit` instance. Its data is
  `asIso` of that unit. It uses no sorry, choice of a map, or extra hypothesis.
- The compositor c is the existing `comp A w v`, defined by the composite
  adjunction, transport along pullComp, then leftAdjointUniq. The first conjunct
  of `twoOpenTensorChainNormalization` is its unit equation for every L. It
  inserts `(pullComp ...).inv` explicitly between the iterated restriction
  and the single restriction; the node suppresses this comparison with the
  words 'under Lu* congruent Lw* Lv*'.
- `twoOpenLeftChain` is exactly e_L: gamma-v, v-shriek of (1 tensor delta),
  v-shriek of rho-w, then c on (w-star F tensor Q). The two v-shriek maps may
  equivalently be combined by functoriality, but neither factor is omitted.
- `twoOpenRightChain` is exactly e_R: rho-v, v-shriek of (delta tensor 1),
  v-shriek of gamma-w, then c on (Q tensor w-star F). This keeps the other
  tensor order throughout.
- T is written `(pull A w).obj F`. `twoOpenFirstRestriction` is a: the
  pullComp component followed by w-star of inverse eta-v. Its target is T.
- `twoOpenDeltaRestriction` is d: w-star delta followed by inverse eta-w.
  It has the iterated restriction as source, exactly as in the node.
- `twoOpenLeftRestriction` and `twoOpenRightRestriction` are r_L and r_R.
  Both start with tensorPullIso.hom and then tensorMap of (a,d) or (d,a).
  The d coordinate includes pullComp.hom to transport the single restriction
  of H to the iterated restriction. These are exactly the suppressed
  composition identifications in the node, not additional comparisons.
- The two IsIso conjuncts assert invertibility of the actual e_L and e_R.
  The final two conjuncts are the actual equalities
  `pull(u).map e_L = r_L ≫ eta` and `pull(u).map e_R = r_R ≫ eta`, with
  their respective target tensor orders. They are equations of morphisms in
  the ordinary derived category, not merely cohomology isomorphisms.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, their ring structures, and the fields fixing k,E,n.
- `Sheaf.Paper.FiniteOpenProductSwap`: namespace
  `WeilConjectures.FiniteOpenProduct`, declarations `tensor`, `tensorMap`,
  `tensorIsoMap`, `pull`, `pullComp`, `tensorPullIso`, `adj`, `comp`, `gamma`,
  `rho`, `sigma`, `proetSigma`, and `settingCoefficientFinite`. The defining
  signatures, bodies and docstrings were read. This is the recorded module
  of def-sf-finite-open-tensor-operations.
- `Sheaf.SixFunctors.OpenTensorNormalization`: the recorded
  `SheafOfModules.openTensorNormalization`, with `exists_normalized` and
  `finite_compatibility`; its public data module gives `FiniteD`, `finiteShriek`.
  The normalization theorem's full signature and docstring were read.
- `Sheaf.Paper.DerivedPullbackTensorIso`: the full signature and proof docstring
  of `WeilConjectures.derivedPullbackTensorIso`, especially its finite unbounded
  clause and its composition/signed-braiding compatibility. In this node's
  fixed-scalar presentation mu is the existing `tensorPullIso` from the
  recorded operations dependency, already using the exact/K-flat identification.
- Mathlib `CategoryTheory.Adjunction.comp`, `comp_unit_app`, `comp_counit_app`,
  and `comp_homEquiv` in CategoryTheory/Adjunction/Basic.lean, as recorded by
  def-weil-pbc-composite-adjunction. Its identity-adjunction clause is unused
  by this node. The file is a plain proof import.
- The existing generic derived-unit instance above is in
  `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`; it is already
  reexported through the canonical open operations.

Edge cases checked before drafting: identity opens retain an arbitrary delta
(e.g. multiplication by a unit), so neither r map can be replaced by identity.
The definitions retain that factor. Empty opens and zero complexes are allowed:
there is no nonempty or nonzero binder, and the same units and comparisons apply.
For odd degrees the two signed swaps in rho cancel by (-1)^(pq+qp)=1; in
characteristic 2 both signs are already 1. Arbitrarily unbounded complexes are
admitted literally by FiniteD, with no t-structure restriction. The small-site
universe u and coefficient/module universe u+1 are the published ones and are
not equated. The positive-level datum includes n=1. There is no assertion
requiring a coefficient ring at level zero.

Searches for an existing statement (2026-10-22):

- msearch leanfinder: 'Two composable open immersions extension by zero derived
  tensor chains unit normalization in both tensor orders'. Eight hits concerned
  homological-complex tensor units; none states these chains.
- msearch loogle: `CategoryTheory.Adjunction.leftAdjointUniq`. Twelve generic
  adjunction uniqueness hits, including unit_leftAdjointUniq_hom_app; useful
  background for the compositor clause, no match to the entire node.
- msearch grep: `twoOpenTensor|two_open_tensor|tensorChainNormalization|extensionByZero`.
  Zero Mathlib hits.
- msearch leansearch: 'Unit normalized extension by zero derived tensor chains
  for two composable open immersions'. Eight hits included scheme module
  restrictFunctorComp and immersion composition; no match to these pro-etale
  derived tensor chain equations.
- rg in both lean/WeilConjectures and lean/Sheaf:
  `twoOpenTensor|two_open_tensor|tensorChainNormalization|lem-pur-two-open-tensor-chain-normalization`.
  No declaration or blueprint tag already states this node.
- Read the existing operations module and searched the pro-etale open-adjunction
  files for the actual unit-invertibility interface. Found the generic existing
  exact-derived-adjunction instance, so no replacement theorem was introduced.

No STATEMENT-DISPUTED flag or mathematical statement fault was found. A packaging
issue for later proof imports: the required operations node currently records
FiniteOpenProductSwap as its owning module, and that module's theorem node now
lists this item as a proof dependency. This delivery imports the recorded
operations as required; adding the reverse proof import to that existing module
would create an import cycle. The maintainer should omit that reverse import
under stages/2-statements.md rule 7 until operations are factored into their own
module. No existing source was edited by this worker.

Validation: scompile.py compiled the entire delivered module in both sandbox and
library modes against the live published server library with no errors or
unexpected warnings. The final required dry run and delivery are recorded below.

## Second reading by NW

A second pass by this same dispatcher worker compared the node and complete Lean
file side by side; no separate agent was started, per the brief. Independent
review remains the maintainer's review of the delivery. The checks were the
coefficient datum and all separated/finite-type binders, all complex domains,
delta's direction, each of the four e_L/e_R factors, a and d's inverse-unit
directions, both tensor orders in r_L/r_R, the compositor unit equation and its
pullComp inverse, and the directions and targets of both final restriction
equalities. The rho equation was separately checked to have mu before inverse
eta on the second coordinate and then target eta. Both theorem docstrings
retain the corresponding steps of the seven-step natural-language proof.
No mathematical mismatch was found. Explicit direct imports for all four
statement dependencies and the generic composite-adjunction proof dependency
were added before final validation. All universes and variables are explicitly
bound under `set_option autoImplicit false`. The only postponed proofs are
`twoOpenRhoNormalization` and `twoOpenTensorChainNormalization`, both this node's
own clauses; all helper definitions have real data.
