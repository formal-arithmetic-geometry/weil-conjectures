## Worker report

Stage 2 states `lem-weil-frobenius-finite-exchange-inverse` in
`Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse`. The sole postponed theorem is
`WeilConjectures.FrobeniusExchange.frobenius_finite_exchange_inverse`, with proof
`sorry` and the complete four-step DAG proof in its docstring. The node is unchanged
outside `lean`. No new nodes or dependency repairs are needed.

The earlier worker's reported stage-1 live-wins obstruction does not apply to this
stage-2 assignment: Q103's passing `reviewed` record is a split review; the current
node has no `lean` or `reviewed_lean`. No re-splitting is performed. No preserved
stage-2 report or Lean file was present in the prescribed NN sandbox.

The two auxiliary definitions contain real data. `frobeniusFiniteOpenExchange` is
exactly `constantOpenSquareExchange`, with the already proved base-change open
immersion property supplied. `frobeniusFiniteComparison` is exactly
`intrinsicCompactificationComparison`, supplying the inherited finite-type,
quasi-compactness and separatedness instances explicitly. They introduce no new
notion and do not choose arbitrary maps or witnesses.

Hypothesis and clause correspondence:

- The finite-field datum p,a,q,k0,k is `D : FiniteFieldDatum.{u}`. Its fields carry
  primality, positive exponent, cardinality, the finite base field and its fixed
  algebraic closure. `l : Nat`, `[Fact l.Prime]`, and `hl : l != D.p` supply the
  second prime and the excluded characteristic.
- The coefficient extension is `(E : Type u) [Field E] [Algebra Q_[l] E]
  [FiniteDimensional Q_[l] E]`; the actual Lean notation is `ℚ_[l]`.
  The ring R, chosen uniformizer and level quotient are the dependency's
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `Padic.coefficientExtensionRing l E n`. The level is `(n : Nat) (hn : 1 <= n)`
  (Lean uses `ℕ` and `≤`). Finiteness is supplied by
  `Padic.finite_coefficientExtensionRing l E n hn`, never assumed as extra data.
- The two finite-type k0-schemes are `X₀ Y₀ : Over (Spec (.of D.k₀))` with
  `LocallyOfFiniteType` and `QuasiCompact` on their structure maps. Their morphism
  is `f₀ : X₀ ⟶ Y₀`; `[IsSeparated f₀.left]`, `[LocallyOfFiniteType f₀.left]`,
  `[QuasiCompact f₀.left]` render exactly separated finite type.
- The actual geometric fibers are `(D.geometricFiber X₀).left` and the analogous
  Y object. `fiberMap D f₀` is the base-changed morphism, and `galois D X₀`,
  `galois D Y₀` and the compactification middle model's `galois` are precisely
  the geometric field-Frobenius scheme maps. No k-linearity instance is requested.
- The supplied compactification is `c₀ : Compactification f₀.left`; its base change
  is the recorded `geometricCompactification D f₀ c₀`. The fields give its open
  part, proper part and factorization, with no properness assumption on f₀.
- The objects range over `proEtaleDerivedCategory` with the finite quotient ring,
  hence the full unbounded derived category of modules over the constant ring
  sheaf on the small pro-etale site. The site's object/morphism universes remain
  u+1/u; no universe equality or bounded/constructible restriction is introduced.
- `directIso.hom = frobeniusDirectFinite D l E n hn f₀` asserts invertibility of
  exactly the specified unit-compositor-counit mate. A functor isomorphism gives
  the assertion at every K and naturality, rather than merely unrelated
  component isomorphisms. Its endpoints are inferred from this literal equality.
- `properIso.hom = frobeniusDirectFinite ... (zlCompactificationProper ...)`
  provides the same mate for p. This implied intermediate isomorphism lets the
  formula name its inverse without adding a hypothesis about invertibility.
- `compactIso.hom = frobeniusCompactFinite D f₀ c₀ l E n hn` fixes the other
  natural isomorphism's forward map to item 2 of the recorded exchange definition,
  literally the proper mate followed by proper image of b.
- The quantified equality for `compactIso.inv.app K` is
  `Rp.map (b.inv.app K) ≫ properIso.inv.app (j_!.obj K)`.
  Lean's `≫` composes left to right; this is exactly
  FrEx_p,* inverse composed with Rp*(b inverse), as in the displayed node formula.
  The j_! here is the recorded `sfIntrinsicDerivedOpen`, not another construction.
- `O : CompactOriginCategory ... X` is the existing retained triple K,L,alpha
  used by the recorded Frobenius exchange and compactification comparison.
  L is a `DerivedCategory.Plus` etale object and alpha is the specified comparison
  isomorphism to K. This is the canonical intrinsic-coordinate presentation of
  the pair described by `def-weil-pbc-etale-origin-witness`; its recorded
  `FixedEtaleOriginWitness` is publicly imported as well. No antecedent is picked
  from a mere existence proposition. The fixed-module and intrinsic presentations
  are related by the dependency's explicit realization equivalence.
- Every `d : Compactification (fiberMap D f₀)` is allowed. The canonical C_d,c is
  `frobeniusFiniteComparison ... d (geometricCompactification ...)`, literally
  the published normalized `intrinsicCompactificationComparison`.
  `pulledCompactOrigin ... (galois D X₀) O` retains the exact pullback of L and
  the specified comparison isomorphism; it supplies the second comparison domain.
- `transportedIso.hom` is exactly `LgY.map C.hom ≫ FrEx_c.app K ≫ C.inv.app O_g`.
  `transportedIso.inv` is `C.hom.app O_g ≫ compactIso.inv.app K ≫ LgY.map C.inv`.
  Thus it asserts both invertibility and precisely the node's inverse formula.
- The choice c₀ remains a theorem parameter. There is no equality comparing the
  exchanges from two choices c₀. Neither X₀ nor Y₀ is assumed separated over k0.

Dependency declarations read and reused (all names fully qualified by the indicated
namespace; their recorded source modules were opened):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`, and its coefficient conventions.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the quotient and uniformizer are the
  recorded constructions reexported there.
- `def-weil-scheme-morphism-properties` is a convention collection, not a separate
  definition. Its Mathlib properties are `AlgebraicGeometry.LocallyOfFiniteType`,
  `QuasiCompact` and `IsSeparated`, whose full definitions were inspected.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, `galoisMap`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; the recorded intrinsic implementation is the existing
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`
  identifies the finite operation; the exchanges already use its canonical
  tensor-normalized `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`.
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.sfFiniteDerivedDirectImage`
  uses the same canonical `proEtaleConstantDerivedDirectImage` used here.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` and
  `sfIntrinsicModuleEquivalence`; its exact derived version is `sfIntrinsicDerivedOpen`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and `category`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`, the actual Rp_*j_! functor.
- `Sheaf.Paper.FrobeniusGeometricExchange`:
  `WeilConjectures.FrobeniusExchange.geometricCompactification`,
  `geometricCompactification_properties`, `fiber_finiteType`, `fiberMap_properties`,
  `frobeniusCompactFinite`. Its public import `Sheaf.Paper.FrobeniusSquareExchange`
  supplies `fiberMap`, `galois`, `frobeniusDirectFinite`, `CompactOriginCategory`,
  `pulledCompactOrigin`, `intrinsicCompactificationComparison`, and the normalization
  `intrinsicCompactificationComparison_refinement`. All these signatures and
  docstrings were read, including the underlying finiteCompact definition.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness` (the fixed-scalar retained pair).
- `Sheaf.Paper.CompactificationCoherence`:
  `AlgebraicGeometry.ProEtale.compactification_coherence`; the exchange module's
  canonical intrinsic comparison is its normalized coordinate transport.
- Proof inputs are imported explicitly: `Sheaf.SixFunctors.FrobeniusSquareCartesian`
  (`FiniteFieldDatum.frobenius_square_cartesian`),
  `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`,
  `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`
  (`Scheme.constantOpenSquareExchange`),
  `Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence`
  (`Scheme.finiteTorsionDerivedPullback_isEquivalence_of_isIso`),
  `Sheaf.CategoryTheory.MateIsoAlongEquivalences`
  (`CategoryTheory.isIso_mateEquiv_of_isEquivalence_of_fullyFaithful`), and
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.

Edge cases checked against the signature and constructions: n=1 is admitted; n=0
is excluded exactly as the node says; K=0, empty X₀ or Y₀, the identity f₀, j₀=id,
d=c, and unbounded K are admitted. The ambient assertion has no constructibility
or etale-origin condition. Only the compactification comparison uses a retained
bounded-below etale antecedent. Nonproper f₀ and nonseparated X₀/Y₀ remain admitted.
The horizontal Frobenii are scheme maps, so the absence of k-linearity is retained.
No mathematical statement fault or STATEMENT-DISPUTED issue was found.

Searches, 2026-10-22 (through the prescribed msearch.py wrapper):

- LeanFinder: "Finite coefficient geometric Frobenius direct image exchange and
  chosen compact support exchange are natural isomorphisms with inverse
  compactification transport". Eight returned results concern condensed locally
  constant sheaves and generic comparisons, with no matching statement.
- Loogle: "CategoryTheory.mateEquiv, CategoryTheory.IsIso". Zero hits.
- LeanSearch: "Geometric Frobenius exchange is a natural isomorphism on unbounded
  derived categories of finite coefficient pro etale module sheaves". Eight hits
  include generic exact-derived factorization, free sheaf/pullback comparisons,
  pushforward congruence and monoidal Frobenius maps, not this specified exchange.
- Mathlib grep: `[Ff]robenius.*[Ee]xchange|[Ee]xchange.*[Ff]robenius` under
  AlgebraicGeometry. Zero hits.
- Project/upstream rg: `frobenius.*[Ee]xchange|[Ee]xchange.*[Ff]robenius` and the
  exact node id in both `lean/WeilConjectures` and `lean/Sheaf`. The construction
  modules, a cohomological structure-map specialization, adic exchanges and a
  separate compact-support exchange appeared. None states the general ambient
  finite-coefficient theorem together with the chosen inverse and witnessed
  comparison transport. The exact node id had no existing declaration.
- Exact declaration-name rg in both source trees and dag/lean_names_upstream.json
  found no collision for the three delivered names.

Source grounding: read the current main-20261015 global-geometric-Frobenius
blueprint unit and Deligne Weil II, printed pp. 151--153, especially (1.1.10),
(1.1.11) and (1.1.14). The finite ambient exchange verification is correctly
identified as agent-written in the node and theorem docstring.

Validation: the final module compiled through scompile.py (as invoked by the delivery
wrapper) in both sandbox and named library-module modes without warnings or errors.
`deliver2.py NN lem-weil-frobenius-finite-exchange-inverse --no-push` returned
`OK (dry run): commit f7296323462 passes the preflight and compiles; nothing pushed`.
The packet contains exactly the module, its node lean record, and this report.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
