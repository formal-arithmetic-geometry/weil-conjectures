## Worker report

The module `Sheaf.Paper.RelativeProductInputDomains` states
`WeilConjectures.relative_product_input_domains` with `sorry`. The definitions in
`WeilConjectures.RelativeProductInputs` only construct the chosen fibre product,
its over-field projections, and lists/predicates spelling out this node's clauses.
They do not introduce new coefficient categories, operations, or choices of origins.
The node's statement, dependencies, and proof are unchanged.

The source read is the CURRENT
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`,
especially the displayed composite and the sentence about the finite-Tor second
argument of PF. The accepted node expands precisely these input-domain checks.
No change to the source/unit statement is proposed.

Hypothesis-by-hypothesis correspondence:

- `D : FiniteFieldDatum.{u}` contains the prime p, positive a, q=p^a, the finite
  field of q elements, and its algebraic closure k. `C : D.CoefficientDatum`
  contains prime ell distinct from p and the chosen algebraic closure of Q_ell.
- `E : Type u`, `Field E`, `Algebra (Padic C.l) E`, and
  `FiniteDimensional (Padic C.l) E` are the finite coefficient field. Its valuation
  ring and uniformizer are the recorded `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`; finite quotients use exactly
  `Padic.coefficientExtensionRing C.l E n`.
- `n : ℕ` and `hn : 1 ≤ n` retain all positive levels, including n=1.
- `S : SixFunctorDatum D C E n hn` is precisely the recorded six-functor datum.
  The conclusion has separate conjuncts for each of the four coefficient choices.
- `B : SixFunctorSpace D`, `IsSeparated B.obj.hom` give the separated finite-type
  base. `f : X ⟶ B`, `g : Y ⟶ B` are morphisms over k, each with IsSeparated,
  LocallyOfFiniteType and QuasiCompact on its underlying scheme morphism.
  The existing `SixFunctorSpace` bundles finite type. Bundling X,Y this way adds
  no mathematical restriction: composition of f or g with the finite-type base
  gives their finite-type structure maps, as in node proof Step 1.
- `cf,cg,cv,ch` are arbitrary compactifications for f,g,v,h, used to evaluate the
  recorded support operations. They are construction choices, not extra geometric
  assumptions; the stipulated separated finite-type maps into this finite-type
  field setting admit them. The assertion is for every such choice.
- Finite inputs K,L are ambient intrinsic pro-etale objects with exactly the
  `finiteTorConstructible` hypotheses on X,Y. Integral inputs are in the actual
  `sfIntegralConstructibleCategory`, with exactly the uniform finite-Tor
  hypotheses `finiteTorConstructibleIntegral`. Field inputs are arbitrary objects
  of the recorded rational/common-stage categories, since there Dctf=Dbc by
  definition. No finite-Tor hypothesis on a field object is discarded.

Clause-by-clause correspondence:

- `space f g` has underlying scheme `pullback f.hom.left g.hom.left` and structure
  map `pullback.fst ... ≫ X.obj.hom`. `left` and `right` are the actual fst/snd
  with over-field commutativity, not arbitrary maps. The composite h is `left f g ≫ f`;
  it equals v followed by g by the actual pullback condition.
- The first six conjuncts assert the separated finite-type structure morphisms
  of X,Y,T, and the separated finite-type maps u,v,h. Finite type is consistently
  LocallyOfFiniteType together with QuasiCompact.
- `objects` enumerates the same 22 positions at every stage. Its local names
  are P=pu K, V=pv L, Q=sf K, R=sv P, G=pg Q, H=tt P V. Positions are:

| Positions | Scheme | Objects in the node |
| --- | --- | --- |
| 1,2 | X,Y | K,L, retained for the original-input witness assertion |
| 3,4,5 | T | P, Lv*L, H |
| 6 | B | Q=Rf!K |
| 7,8 | Y | Rv!P, Lg*Q |
| 9,10,11 | Y | Rv!P tensor L, Lg*Q tensor L, L tensor Lg*Q |
| 12,13,14 | B | Rh!P, Rh!Lv*L, Rh!H |
| 15,16 | B | Rg!Rv!P, Rg!Lg*Q |
| 17,18,19 | B | the Rg! images of positions 9,10,11 |
| 20 | B | Rg!L |
| 21,22 | B | Rg!L tensor Q, Q tensor Rg!L |

- `finiteObjects` instantiates this list with the existing ambient intrinsic
  derived pullbacks, tensors and support candidates. The finite conjunct asserts
  `finiteTorConstructible` AND `finiteWitness` for every list member. Membership
  is not assumed in order to construct the list, so this is a preservation result.
- `stageObjects` uses exactly a supplied `SixFunctorPushStage` and tensor, with
  no substitute operation. Its integral instance uses `S.higher.integral` and
  `S.higher.integralTensor`, hence the completed operations. For each list member
  the integral conjunct asserts the uniform finite-Tor predicate and
  `integralWitness`, i.e. a finite witness of every reduction m+1.
- The projection second arguments are positions 2 (L on Y) and 6 (Q on B).
  Their finite-Tor assertions give exactly the domains of PF_(v,P,L) and
  PF_(g,L,Q); no invertibility of either component is asserted here.
- `finiteWitness` explicitly quantifies a bounded-below fixed-module pro-etale
  object F, a `FixedEtaleOriginWitness` W for it, an isomorphism of F with the
  specified inverse coefficient realization of the intrinsic object, and bounded
  constructibility of W.complex on the etale site. Thus the antecedent and its
  comparison isomorphism are retained, not obtained as data from a sorry existence
  proof. In particular positions 1 and 5 supply exactly the exchange and
  composition input domains at K,H, with the chosen compactifications available.
- `integralWitness` uses the recorded `scalarReductionDerivedExtension` on the
  completed integral object at every positive exponent. It requests no witness
  for the completed non-torsion object itself and no compatible choice across levels.
- The rational conjunct gives a SINGLE pair of integral representatives K₀,L₀;
  each member of their entire integral list has finite-Tor membership and all
  finite witnesses. `presented` compares that list, entry for entry, with the
  rational list via `sfRationalConstructibleLocalization`. The first two entries
  identify K₀,L₀ with the given K,L; the remaining entries identify all operations.
  Field Dctf membership is in the types of `stageObjects` themselves.
- The common-stage conjunct similarly chooses ONE finite coefficient field E₀
  and integral K₀,L₀ there. It uses the recorded coefficient-stage integral
  operations and compares the whole list via rationalization followed by the
  actual `GeneralAlgebraicallyClosedCoefficients.inclusion`. Thus it includes the
  case where K and L initially descend to different fields, enlarged to a common
  one; it does not reduce a rational/common-stage object to A_n.
- Universal quantification over f,g,K,L (and all construction choices) is the
  final assertion about every other such pair; no special product case is assumed.

Dependency declarations read and used:

| Node | Module and declaration |
| --- | --- |
| def-sf-datum | `Sheaf.Paper.SixFunctorDatum`, `WeilConjectures.SixFunctorDatum`, its inherited `SixFunctorOperationDatum` and normalized finite/higher/coefficient stages |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.condition` |
| def-weil-pbc-etale-origin-witness | `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`, `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness` (full retained pair) |
| def-weil-derived-complete-integral-detailed | `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`, `.sfIntegralConstructibleCategory` |
| def-weil-rationalization-karoubi | `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`, `.sfRationalConstructibleLocalization` |
| def-weil-algebraically-closed-coefficients | `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`, `.GeneralAlgebraicallyClosedCoefficients.inclusion` |
| def-weil-finite-tor-amplitude | `Sheaf.Paper.FiniteTorAmplitudeSites` reexports `finiteTorConstructible` and `finiteTorConstructibleIntegral` from `Sheaf.Paper.FiniteTorAmplitude` |
| def-exchange-projection | `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`; the inherited datum uses exactly its supplied domain/comparison construction |

All recorded proof-dependency modules with available Lean records are imported
plainly: FiniteTorStability, IntegralResidueTor, ProEtaleConstructibleOrigin,
CanonicalOriginCompactSupportComposition, CanonicalFiniteLevelCompactSupportBaseChange.
The three geometric Mathlib leaves are imported through FiniteType, Separated,
Proper. `lem-sf-package-coefficient-domain-realization` has no Lean record at the
read base; no module for that unstated proof prerequisite can be imported. It is
still named in the unchanged node and the postponed natural-language proof.

Edge cases checked before writing: empty X or Y (no nonempty assumption on any
scheme); zero inputs; n=1 (no predecessor discards it); identities f or g (no
nonidentity binder); all positive integral reductions m+1; rational inputs without
literal finite reductions; common-stage inputs over distinct fields. Coefficient
universes are exactly those of the recorded datum, and the small pro-etale site's
object/morphism universe distinction is preserved. No site-perfectness assumption
is imposed. No statement dispute or node correction was necessary.

Searches for an existing statement:

- `msearch.py ... leanfinder "Pullback tensor compact support finite Tor constructible complexes and etale origin for relative products"`: eight results on scheme pullback residue-field tensor products (e.g. `Scheme.Pullback.Triplet.Spec_map_tensor_isPullback`), no derived-domain theorem.
- `msearch.py ... loogle '"constructible", "pullback"'`: OK, 0 hits.
- `msearch.py ... grep 'relative.*[Pp]roduct|etaleOrigin|compactSupport' CategoryTheory`: OK, 0 hits.
- `rg` on Mathlib CategoryTheory for relative-product domain names: no match.
- `rg` on both live `lean/WeilConjectures` and `lean/Sheaf`, and on
  `dag/lean_names_upstream.json`, for `relative_product_input_domains` and
  `namespace RelativeProductInputs`: no match. `grep -rn` for the item id in
  `lean/WeilConjectures` also gave no match.
- Read `Sheaf.Paper.RelativeProductGeometricFactors`: it covers a finite-coefficient
  geometry/origin sub-result and composition/exchange invertibility, not the
  present four-stage input list. It is not an exact existing match. No notion
  needed a new DAG node or dependency-module repair.

Validation: each compile is through the prescribed `scompile.py`; the report is
updated with the final compiler/dry-run result below.

## Second reading by Q136

A second pass in this worker session reopened the node and the completed Lean
source and checked all positions of `objects` against the displayed node list.
The three ordered Y tensors and both final B tensors are distinct and retained;
all eight indicated T/Y images occur. The extra original K,L positions retain the
node's explicit original-input witnesses; Rg!L is required by the final tensors.
The field clauses compare entire lists formed from one pair of integral inputs,
rather than merely claiming individual antecedents for unrelated objects. The
finite witness includes bounded constructibility of the etale antecedent and uses
the dependency's actual retained-pair structure. The universe lift changes only
coefficient presentation. The finite-type bundling of X,Y was checked against
composition with the given finite-type B structure; it excludes no permitted pair.
No omitted conclusion or additional mathematical hypothesis was found.
This is the worker's second pass; the maintainer's independent delivery review
remains separate, as stipulated by the dispatcher brief. No other agent was started.

Final compile: `scompile.py Q136 lem-sf-relative-product-input-domains
.../lean/Sheaf/Paper/RelativeProductInputDomains.lean` passed in both modes:
sandbox 39.4 s (including wrapper overhead), library 7.2 s, no errors or warnings.
Elaboration repairs made the fibre-product structure proofs explicit, fixed the
object-list category family, and provided the common-field comparison's category
instances pointwise. `commonPassage` names exactly rationalization followed by the
recorded inclusion; no mathematical hypothesis, clause, operation or category changed.
