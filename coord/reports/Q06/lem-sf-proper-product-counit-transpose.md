## Worker report

This delivery states `WeilConjectures.properProductCounitTranspose` in
`Sheaf.Paper.ProperProductCounitTranspose`. Its sole theorem proof is `sorry`.
All 18 auxiliary declarations contain real construction data or abbreviate
explicit composites. There is no new axiom, independent existence choice,
new operation, additional assumed comparison, or change to the node statement.

The source read is the current blueprint's
`sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`,
final sentence. I also read both proof steps in the dispatched node. Ordinary
proper coordinates are explicitly required by the node: identify support with
direct image by the proper normalization before forming the displayed maps.
The finite clause uses the recorded intrinsic ambient realization; the three
higher clauses retain the operation datum's ordinary adjunctions. The coefficient
comparison and proper-normalization theorems identify these coordinates with
the specified support maps. No claim about an arbitrary exchange, projection,
symmetry or composition transformation is made.

Hypotheses and clauses, individually:

* The global primes, exponent a >= 1, finite field and its algebraic closure
  are `D : FiniteFieldDatum`; `C : D.CoefficientDatum` supplies the prime ell,
  its inequality with D.p, and the fixed algebraic closure of Q_ell.
  `E`, its `Field`, `Algebra (Padic C.l) E` and `FiniteDimensional` instances
  give the finite coefficient extension. Its recorded valuation ring,
  uniformizer and quotient are reused, not redefined. The finite exponent is
  `m + 1` for arbitrary `m : ℕ`, including exponent one.
* `S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m)` is the specified datum.
  All adjunctions in the higher clauses are fields of its operation datum.
  Finite operations are the actual intrinsic coefficient realization fixed by
  `finitePullback`, `finiteDirectImage`, `finiteDirectAdjunctionNormalization`
  and `finitePullCompositionNormalization` of that same datum.
* `X Y Z T : SixFunctorSpace D` are finite-type schemes over Spec D.k;
  `Z` denotes the node's B. The four structure-map `IsSeparated` instances
  render separated schemes. Arrows are over the same base. Properness of
  `f.hom.left`, `g.hom.left` renders proper f,g and implies their separated
  finite-type hypotheses. The separated, locally finite-type and quasi-compact
  instances for p,q render the standing separated finite-type morphism convention.
* `comm : p ≫ f = q ≫ g` fixes the composite t as `q ≫ g` with its equality
  to `p ≫ f`. `IsPullback p.hom.left q.hom.left f.hom.left g.hom.left` is
  precisely T = X times_B Y, allowing any presentation of that fiber product.
* The finite input binders use `finiteTorConstructibleCategory` and pass
  the underlying actual objects `K.obj`, `L.obj` to the ambient formula.
  The integral binders use `sfIntegralConstructibleCategory` with both
  `integralFiniteTorDomain` predicates. Rational and common-stage inputs are
  the whole constructible categories, as their recorded finite-Tor domain is top.
  These four conjuncts cover exactly the four choices of Lambda.
* In `ProperProductCalculus`, `fPush.obj K` and `gPush.obj L` are F and G;
  `tensorT.obj (pPull.obj K, qPull.obj L)` is D. Each constructor inserts
  the recorded tensor and pullback, rather than an arbitrarily supplied operation.
* `exchange` is the existing `mateEquiv` of the pullback-square comparison.
  Its transpose is the square comparison followed by `pPull.map` of the
  actual f-adjunction counit. This is def-exchange-projection's ordinary
  exchange, which the node says to use after proper normalization.
* `projectionQ` and `projectionG` write the component formula for the existing
  counit-defined projection: the adjunction hom equivalence applied to the
  canonical tensor-pullback comparison followed by counit tensor identity.
  These are component notation for the dependency's formula, not a new
  projection notion or an assumption of invertibility.
* `psi` is, in order, `swapB`, the g-projection, and `gPush.map swapY`,
  exactly Psi_g(F,L). Both swaps are the recorded signed derived braidings.
* `intermediate` tensors the actual exchange component with identity on L,
  then applies the q-projection. `product` applies Psi followed by g_* of
  this intermediate. `lambda` then applies the inverse direct-image composition
  comparison, the `rightAdjointUniq` determined by the pasted adjunction and
  the supplied `tComposition`. This is precisely alpha_(g,q) in ordinary
  proper coordinates, with target t_*D; it is not a free compositor.
* The first conjunct of `CounitIdentities` uses `(qAdj.homEquiv _ _).symm`
  on that entire intermediate composite. Its right side is mu_q followed
  by the square comparison and p^*epsilon_f in the first tensor factor,
  and identity on q^*L in the second. The isolated exchange-tensor map
  is never transposed with an ill-typed target.
* `twoCounit` first uses the supplied t^* = q^*g^* comparison, then
  `qPull.map muG`, then `muQ`, then the tensor of the square comparison
  followed by p^*epsilon_f and q^*epsilon_g. These are the canonical
  signed monoidal and composition coordinates of c_(f,g).
  The second conjunct is `(tAdj.homEquiv _ _).symm (lambda K L) = twoCounit K L`.
  Thus it uses the actual t-adjunction and includes the composition comparison.
* Integral constructors use `constructibleIntegralTensor`,
  `canonicalIntegralPullbackTensor` and `pullbackTensorIntegralBraiding`;
  these are completed, with finite-reduction normalization. Rational
  constructors use their rationalized counterparts; the common-stage
  constructors use `commonStageDerivedTensor`,
  `canonicalCommonStagePullbackTensor` and `pullbackTensorCommonBraiding`.
  Their coefficient cocycles and representative normalizations are inherited.
  `properProductTransportTensor` only conjugates these canonical maps by
  the operation datum's equalities with its actual pullback. It assumes no
  extra monoidality or compatibility hypothesis.

Dependency declarations read and used:

* `Sheaf.Paper.SixFunctorDatum`, `WeilConjectures.SixFunctorDatum`, its inherited
  `SixFunctorPushStage` adjunctions/compositors and the definition
  `sixFunctorDirectComposition`. The final lambda comparison has exactly this
  `rightAdjointUniq` formula. `SixFunctorOperationDatumStages` provides
  `SixFunctorSpace`, all actual-stage operations and their normalizations.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage.exchange`
  and `.projection`: read their signatures, docstrings and composite formulas.
  The ordinary exchange uses `Mathlib.CategoryTheory.Adjunction.Mates`'s
  `mateEquiv`; the projections display the same component formula as
  `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`'s
  `Adjunction.rightAdjointProjectionMap` and its transpose lemma.
* `Sheaf.Paper.SixFunctorDualNotation`: the recorded def-sf-pf interface explicitly
  reexports the above projection notation, `finiteExchangeProjection` and
  `SixFunctorExchangeData.projectionComponent`. No replacement dual or PF is added.
* `Sheaf.Paper.DerivedPullbackTensorIso`: `canonicalFinitePullbackTensor`,
  `canonicalIntegralPullbackTensor`, `canonicalRationalPullbackTensor`,
  `canonicalCommonStagePullbackTensor`, their composition and signed symmetry
  interfaces. The actual finite signed braiding is `pullbackTensorBraiding`
  on `finiteIntrinsicClosed` and `finiteIntrinsicTensorModels`; the higher
  braidings are `pullbackTensorIntegralBraiding`,
  `pullbackTensorRationalBraiding`, `pullbackTensorCommonBraiding`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction`; the actual finite derived pair and
  `sfIntrinsicDerivedPullbackComp` are inherited through the recorded imports.
* `Sheaf.Paper.FiniteTorStability`, `sfStabilityResidueInvertible`: a constructed
  inverse obtained by mapping the base-field unit into each residue field.
  `properProductResidueInvertible` inserts the existing over-scheme map;
  residue-field invertibility is not an additional theorem hypothesis.
* Stated proof dependencies are imported: `Sheaf.Paper.ExchangeFunctoriality`
  (`exchangeFunctoriality`), `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`
  (`mapDerivedUpperStarLowerStarAdjunction_comp_eq`), the pullback/tensor module,
  `Mathlib.CategoryTheory.Adjunction.Mates` (the mate-pasting lemmas), and
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (proper composition/base change).
  `fix-prop-projection-formula` has no Lean record on the read base, so has no
  module to import; the actual projection maps needed for this statement are
  already supplied by the three statement dependencies.

Edge cases checked before and after writing: m=0 gives exponent one; arbitrary
positive a is retained inside D; empty schemes, zero complexes, identity maps,
and disconnected fiber products are not excluded. No finite/nonempty point
hypothesis is added. The two signed swaps in Psi cancel with the Koszul signs
as in the source, rather than forgetting a sign. Equal finite coefficient
stages and arbitrary larger common fields remain covered by the inherited
identity/cocycle comparisons. There is no rational-to-finite reduction functor.
The category object and morphism universes are independent in the component
notation; the actual site universes remain exactly those of the dependencies.

Searches (recorded by msearch.py in searches.jsonl):

* LeanFinder: “For proper scheme morphisms the composite of projection formula
  and Cartesian base change is adjoint to the tensor product of the pulled
  back adjunction counits”: eight results, chiefly scheme-module adjunctions
  and pullback projections. No derived proper product transpose theorem.
* Loogle: `CategoryTheory.Adjunction, counit, tensor`: zero hits;
  `counit` unknown to that service. Earlier exact-name query
  `CategoryTheory.Adjunction.rightAdjointProjectionMap, CategoryTheory.mateEquiv`
  also returned zero with the first name unknown. The actual existing APIs
  were then read in their source modules as listed above.
* msearch grep in Mathlib/CategoryTheory:
  `projectionFormula|projection_formula|rightAdjointProjectionMap|counit.*tensor`:
  sixteen hits on generic monoidal adjunctions or unrelated counits, none the item.
* LeanSearch: “The transpose of a base change and projection formula product
  map is the tensor of adjunction counits”: eight linear algebra/base-change
  results, none matching this statement.
* rg in lean/WeilConjectures and lean/Sheaf for proper product, counit transpose,
  projection, and Kunneth found the existing projection and mate APIs, and
  related tensorProjectionAdjunct/CompositionProjectionMate statements, but
  no theorem with both of this node's equalities at all four actual coefficient
  stages. The node-id grep in WeilConjectures returned no declaration.
  Exact-name searches for ProperProductCalculus, properProductCounitTranspose,
  properProductFinite and properProductResidueInvertible in both roots and
  Mathlib returned no name collision.

Validation: scompile.py compiled the module in its sandbox and library paths
cleanly with no warnings; the 60-second per-file limit was retained. Elaboration
was repaired by using the scheme-hom equality explicitly in the finite square
transport and by binding the stage constructors' return types. The only
postponed proof is properProductCounitTranspose, with its complete two-step
source proof in the docstring. No new nodes, dependency repairs, disputed
statement or statement correction are needed. The maintainer supplies the
independent review; no second worker was started.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
