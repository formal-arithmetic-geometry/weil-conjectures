## Worker report

This delivery states `AlgebraicGeometry.ProEtale.sncRootLimit_normal_charts` in
`Sheaf.Paper.SNCRootLimitNormalCharts`. Its only theorem has proof `sorry`.
No definition is introduced, and the natural-language statement is unchanged.
The previous attempt's stage-1 already-split refusal does not apply to writing
this still-absent stage-2 statement. The current stage-1 proof and NP/L review
are preserved verbatim.

Hypothesis and conclusion correspondence:

- Prime p: `(p : ℕ) [Fact p.Prime]`.
- Characteristic-p field k: `(k : Type u) [Field k] [CharP k p]`.
- Regular separated finite-type k-scheme Y: `Y`, its structure morphism `y`,
  `[LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]`, and
  `hY : IsRegularScheme Y`. Finite type is locally finite type plus quasi-compact.
- The affine etale chart Spec A -> Y: commutative ring `A`, map `b`, and `[Etale b]`.
  No nontriviality, connectedness or domain hypothesis is imposed on A.
- The nonnegative branch count and its equations: `r : ℕ`, `t : Fin r → A`.
- A reduced strict normal crossings boundary: ideal sheaf `H` and
  `hH : IsStrictNormalCrossingsBoundary H`. This recorded definition includes
  Cartier invertibility, radicality, distinct integral regular components,
  regular intersections and the expected dimension formula.
- These are branch equations of that reduced divisor: `hproduct` identifies H
  with the principal ideal sheaf of the product, transported by `Scheme.ΓSpecIso`.
  `hbranches` identifies the zero loci V(t_i) with precisely its reduced
  irreducible component supports. Together these exclude multiplicities or
  omitted components; no arbitrary auxiliary divisor is substituted.
- Weakly etale A -> R: ring map `a` and `ha : a.WeaklyEtale`. This is the
  recorded upstream ring-map specialization of `Algebra.WeaklyEtale`, precisely
  flatness of the structure map and of tensor multiplication.
- The specified S: `tameRootAlgebra p (fun i ↦ a (t i))`, the existing polynomial
  quotient adjoining x_(i,n) with x_(i,n)^n = a(t_i) and
  x_(i,m)^(m/n) = x_(i,n) for positive prime-to-p orders with n dividing m.
  Its generators-and-relations presentation is exactly that of the displayed
  ring colimit: compatible homomorphisms from the finite stages are precisely
  assignments to these generators satisfying these equations. Thus no arbitrary
  root algebra or map is assumed. Reuse follows the item's existing consumer
  `RootTowerLisseMorphismExtension`, which uses this same construction.
- Every weakly etale S-algebra Q: arbitrary `(Q : Type w) [CommRing Q]`,
  its `[Algebra ... Q]`, and `[Algebra.WeaklyEtale ... Q]`.
- Normality: the first conjunct quantifies over every ideal q with `[q.IsPrime]`
  and asserts both `IsDomain (Localization.AtPrime q)` and
  `IsIntegrallyClosed (Localization.AtPrime q)`.
- Boundary regularity: the second conjunct is `Function.Injective` of
  multiplication on Q by the image of `∏ i, t i`, using exactly the maps
  A -> R -> tameRootAlgebra -> Q.
- Zero Q, zero A/empty chart, and r=0 are included: there is no Nontrivial or
  positive-r assumption. In the zero ring there are no prime ideals and every
  self-map is injective; for r=0 the product is 1 and the root algebra has no
  variables or relations, canonically R. No characteristic-zero case is added.

The explicit universes u,v,w bind every variable and permit differently sized
R and Q. No independent test-index universe, auto-implicit variable, local
notation, private definition, choice of a root, or hidden let is used.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`:
  locally Noetherian plus the existing stalkwise `IsRegular` class.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`,
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`: the full recorded predicate.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: publicly exposes
  `Algebra.WeaklyEtale` through `IndPrincipalZariski` and the upstream
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`. The ring-map predicate is
  `RingHom.WeaklyEtale`, defined using the map's canonical algebra structure.
- `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`; the root construction
  uses this very polynomial ring, without a second polynomial definition.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`:
  the universal-property notion of colimit, encoded by the root presentation.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  and `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`:
  exactly the dependency node's prescribed inline normal-ring form.
- Added one already-landed statement dependency,
  `def-sfb-strict-local-kummer-tame-module`, whose module
  `Sheaf.Paper.StrictLocalKummerTameModule` owns `TameRootOrder`,
  `tameRootRelations`, and `tameRootAlgebra`. This adds no new notion or node.

The imports also retain all recorded proof interfaces: regular-ring normality,
weakly etale base change, tensor pushout maps, ind-etale refinement, etale
normality, filtered-colimit normality, flat maps, monic quotient power basis,
filtered-colimit element representatives, regular-local domains, Krull dimension,
and maximal-localization ideal membership. The proof-only nodes
`lem-sfb-snc-finite-root-regular-ring` and
`lem-sfb-faithfully-flat-normal-ring-descent` currently have no Lean declaration;
there is no module to import for them. They are not needed to type the statement.
The full nine-step DAG proof is in the theorem docstring, including these nodes.

Searches for an existing statement:

- msearch.py leanfinder, query: Local rings of weakly etale algebras over a normal
  infinite simultaneous parameter root tower are integrally closed domains.
  Eight results: RingHom.Etale.ofLocalizationSpan,
  RingHom.Etale.ofLocalizationSpanTarget, Algebra.IsEtaleAt,
  Algebra.instIsStandardEtaleRing, Algebra.IsStandardEtale,
  StandardEtalePair.instEtaleRing, Algebra.FormallyEtale.localization_base,
  StandardEtalePair.instFormallyEtaleRing. None states this theorem.
- msearch.py loogle, query: Algebra.WeaklyEtale, IsIntegrallyClosed. Zero hits.
- msearch.py grep, query:
  (WeaklyEtale|IndEtale).*(IsIntegrallyClosed|[Nn]ormal)|(IsIntegrallyClosed|[Nn]ormal).*(WeaklyEtale|IndEtale).
  Zero hits.
- msearch.py leansearch, query: Normality of affine weakly etale charts over a
  filtered colimit of regular Kummer root algebras with regular boundary equation.
  Eight hits concerning scheme normalization and formal etaleness; no match.
- rg of the item id in WeilConjectures: no hits; rg in Sheaf finds only the
  downstream consumer's proof docstring. Name/concept searches for root towers,
  simultaneous roots and SNC in both libraries find the existing
  `tameRootAlgebra` and one-parameter Kummer towers, but no asserted normal-chart
  theorem. The existing full-root construction is reused rather than duplicated.

Source checks: read ILO IX Proposition 2.1 and its proof on printed pp.133--134,
which give the simultaneous finite-root normal form; read Stacks algebra.tex
lemma-colimit-normal-ring (037D) and lemma-descent-normal (033G); read current
blueprint direct-images paragraph (3). The inherited node explicitly identifies
this as an agent assembly of those results and requests an exact combined
infinite-chart reference. This delivery preserves that source limitation and
makes no claim that ILO alone states the full infinite version.

Validation: scompile.py compiled this module against the live published library
successfully, both its sandbox and library-module checks, with no unexpected
warning. Edge cases were inspected before writing: empty branch tuple, zero
chart, zero Q, first root order n=1, arbitrary non-domain Q, and independent
coefficient universes. No statement correction or new definition is needed.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
