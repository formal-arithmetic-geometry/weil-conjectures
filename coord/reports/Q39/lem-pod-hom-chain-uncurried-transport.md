## Worker report

The module `Sheaf.Paper.PodHomChainUncurriedTransport` states
`WeilConjectures.PodHomChain.uncurried_transport`, with proof `sorry`.
It publicly imports `Sheaf.Paper.PodHomChainCounitFormula` and reuses that
module's `homX`, `projection`, and `sourceFunctor`. It does not redeclare or
rename either duplicate identified by the maintainer. All remaining helpers
are abbreviations for existing operations or the node's explicit q_N and p_N
composites, with actual data. The node's natural-language statement, original
statement dependencies, proof and proof dependencies are unchanged.

Each hypothesis has the following rendering.

- `D : FiniteFieldDatum`, `A : D.CoefficientDatum`, `E : Type u`, its field,
  algebra and finite-dimensional instances, and `n`, `hn : 1 ≤ n` specify
  the finite base field, geometric field, distinct coefficient prime, finite
  coefficient extension and positive quotient exponent.
- `six : SixFunctorOperationDatum D A E n hn` is the given operation datum.
  `s : PodCoefficientStage` ranges over finite, integral, rational and common
  algebraically closed coefficients. The stage definitions use the actual
  recorded categories and operations, including completed integral operations
  and common finite-field representatives for algebraically closed coefficients.
- `X Y : SixFunctorSpace D` are finite-type schemes over the geometric field.
  `f : X ⟶ Y` is a map over that field. Its `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact` instances express separated finite type.
- `c : Compactification f.hom.left` specifies the compactification used by
  the support functor and the canonical projection.
- `R : PodCtfAdjunctionData ... f c` is the supplied restricted-operation and
  closed-presentation data from `det-thm-sf-ctf-stability-adjunctions`.
  Its four domain proofs construct restrictions of the actual pullback, direct,
  support and exceptional functors by full inclusion. Its ordinary and exceptional
  adjunctions are the restrictions of the given operation adjunctions.
  Its tensor comparisons identify the chosen tensor presentations with the
  recorded actual coefficient tensors. No arbitrary projection map is supplied.
- `M`, `N`, and `T` belong to `(PodCoefficientStage.domain six s _).FullSubcategory`:
  the actual finite-Tor subcategories at finite/integral coefficients and the
  entire constructible categories at the field stages.
- `a : (tensorX six s f c R).obj M ⊣ homX six s f c R M` retains the source's
  free chosen left-factor tensor-Hom adjunction. Evaluation is its own counit;
  it is not silently replaced by another adjunction's evaluation.
- `t : T ⟶ directHomObject six s f c R M N` is exactly the test arrow t:T→A_N.

The objects and clauses match as follows.

- C is `R.support.obj M`; f!N is `R.exceptional.obj N`.
  `internalHomObject` is L_N, using the imported `homX`.
  `directHomObject` is A_N, the value of the imported `sourceFunctor`.
  B_N is the value of the imported `homY` at C and N; it is a named object
  of the setting, with no additional assertion in this transport lemma.
- `tensorX` and `tensorY` are only abbreviations for Mathlib's `curriedTensor`
  with the supplied monoidal structures. Their `.obj M` is tensorLeft M.
- P_T is the imported `projection six s f c R M T`. Its existing definition
  transports `rawProjectionIso` through R's specified tensor comparisons and
  full inclusion. The raw projection is the canonical compactification
  projection from the operation datum, not a freely chosen natural map.
- `q` is tensor(M, ordinary counit at L_N), followed by `a.counit.app (f!N)`.
- `p` is P_{A_N}, followed by `R.support.map q`, followed by the exceptional
  counit at N. The imported `pairing` fixes R's own chosen tensor adjunction;
  `p` here retains the free binder a required by this node.
- The first conjunct expands inverse ordinary `homEquiv` at t into
  `R.pull.map t ≫ R.ordinaryAdjunction.counit.app L_N`, giving u_t.
- The second conjunct expands inverse `a.homEquiv` at u_t into
  tensor(M,u_t) followed by a's evaluation, giving the first formula for v_t.
- The third conjunct identifies that same inverse transpose with
  tensor(M,pull.map t) followed by q_N, giving the second formula for v_t.
- The fourth conjunct expands inverse exceptional `homEquiv` at v_t into
  `R.support.map v_t ≫ R.exceptionalAdjunction.counit.app N`, giving z_t.
- The fifth conjunct precomposes that inverse exceptional transpose with P_T
  and equates it to tensor(C,t) followed by p_N, giving w_t.
- The sixth conjunct is the specified naturality square:
  `P_T ≫ R.support.map (tensor(M,R.pull.map t)) = tensor(C,t) ≫ P_{A_N}`.
  All composition is written in Lean's first-then-second order.

Dependency declarations used and read:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum` and its
  recorded finite-Tor domains and coefficient operations.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the finite intrinsic tensor/Hom,
  integral tensor/Hom, rational tensor/Hom and common-stage tensor/Hom,
  used through the existing `PodCoefficientStage.tensor` and `internalHom`.
- `Sheaf.Paper.PodCtfAdjunctions`, the recorded module of
  `det-thm-sf-ctf-stability-adjunctions`: `PodCoefficientStage.category`,
  `domain`, `operations`, `homPairs`, `internalHom`, `tensor`,
  `PodCtfAdjunctionData`, and its `pull`, `direct`, `support`, `exceptional`,
  `ordinaryAdjunction`, `exceptionalAdjunction`, `tensorAdjunctionX/Y`.
  Its full-subcategory and closed interfaces are the shared
  `sixFunctorDomainChange`, `sixFunctorDomainHom`, `SixFunctorClosedDomain`
  of `Sheaf.Paper.SixFunctorDatum`.
- `Sheaf.Paper.PodHomChainCounitFormula`: `homX`, `sourceFunctor`,
  `projection`, `projectionIso`, `rawProjectionIso`, and `rawProjection`.
  Only these definitions are used; `counit_formula` is not invoked. Importing
  the shared definitions, as requested by the return, introduces no Lean import
  cycle: that module does not import this one. No reverse DAG edge to the
  parent theorem is added.
- `Sheaf.Paper.CompactSupportProjectionFormula`: `compactSupportProjectionFormula`,
  used by the shared `rawProjectionIso`; its components are those of
  `def-exchange-projection` on the supplied four-stage domains.
- The ordinary/exceptional adjunction input `fix-prop-adjunctions` is realized
  by R's restrictions of the given operations. Its recorded upstream module
  `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` supplies the ambient
  signatures; this statement uses the already recorded restricted interface,
  rather than importing a duplicate ambient presentation.
- Mathlib `MonoidalCategory.curriedTensor`, `Adjunction.homEquiv`,
  `Adjunction.homEquiv_symm_apply`, and the three closed uncurrying laws in
  `CategoryTheory.Monoidal.Closed.Basic`. These already enter by the public
  import. The proof-only domain node `lem-pod-hom-chain-ctf-domains` still has
  no Lean record, so no module can be imported for it; the docstring names it.

Edge cases checked: t=id gives u=the ordinary counit, v=q, and w=p. t=0 gives
zero at every inverse transpose and in the projection square. The zero object,
empty schemes, identity f, proper f and n=1 remain covered. No smoothness,
nonemptiness, field-only restriction or equality of independent universes is
introduced. The theorem keeps an arbitrary supplied chosen left-factor
adjunction a. There is no STATEMENT-DISPUTED issue or source correction.

Searches for an existing declaration (2026-10-22):

- `msearch.py` LeanFinder: "The successive inverse adjunction and tensor Hom
  bijections and projection formula send a morphism to the composite with
  ordinary counit evaluation and exceptional counit". Eight hits, including
  rigid tensor Hom and evaluation laws; none states all four images and the
  specified projection square at these coefficient stages.
- `msearch.py` Loogle:
  `CategoryTheory.Adjunction.homEquiv_symm_apply, CategoryTheory.MonoidalClosed.uncurry_eq`.
  Zero hits for the combined query.
- `msearch.py` grep: `homEquiv_symm_apply|uncurry_eq`, `CategoryTheory/`.
  Twenty-five hits on individual inverse-adjunction and uncurrying identities,
  not the full four-arrow transport calculation.
- `msearch.py` LeanSearch: "Inverse ordinary adjunction followed by inverse
  tensor Hom adjunction followed by inverse exceptional adjunction and a
  projection formula natural transformation factors through precomposition".
  Eight hits, including generic adjunction composition and naturality of the
  inverse Hom bijection, not this complete statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `uncurriedTransport`, `homChainUncurried`, and counit/Hom-chain patterns.
  No declaration states this item. The existing internal-adjunction evaluation
  is finite-etale and identifies an exchange transpose; it does not give the
  four-stage intermediate identities and projection square here.


The preceding search log is retained from the saved packet. The repair's focused
`rg` search in current `lean/Sheaf` and `lean/WeilConjectures` found the existing
`PodHomChain` namespace only in `PodHomChainCounitFormula.lean`; its full source
and `PodCtfAdjunctions.lean` were read. Its `counit_formula` gives the final
curried composite and its naturality, rather than all intermediate uncurried
images and the explicit projection square requested by this node.

## Returned-delivery repair

Return L at immutable head `c75c63cbf0ac` identified duplicate declarations
`WeilConjectures.PodHomChain.homX` and
`WeilConjectures.PodHomChain.projection`, already defined in
`Sheaf.Paper.PodHomChainCounitFormula`.

Both local declarations have been removed and the existing module is publicly
imported. Every use now refers to the original declarations, with their exact
`PodCtfAdjunctionData` interface. The obsolete parallel `core`, `model` and
braiding definitions are removed too. The six conjuncts are retained in the
shared actual finite-Tor categories. The arbitrary adjunction a is retained;
no shared construction is renamed to hide a collision.

The saved packet was compared with current shared sources and the current node:
the current node has no Lean attachment and its original dependencies include
`det-thm-sf-ctf-stability-adjunctions`, whose recorded module is now
`PodCtfAdjunctions`. The earlier packet's two added dependencies
`fix-lem-tensor-adjunction` and `def-weil-exceptional-inverse-image` are no longer
needed and are removed from the packet; the final dependency list equals the
current node's original list. The only final node field changed is `lean`.
No new node, dependency override, or natural-language correction is delivered.

## Self-check

Read the source blueprint Step 1 and the displayed inverse-chain formulas
against the revised module. Each intermediate transpose, both formulas for
v_t, the w_t factorization and the naturality square remain explicit. The
chosen tensor-Hom adjunction remains free, so the imported parent's fixed
adjunction has not silently strengthened the input. The shared projection
has the required forward direction. The module declares neither returned
name. All helpers contain actual data, every variable and universe is bound,
and the only postponed theorem is the item itself.

`scompile.py` compiled the revised single module in sandbox mode (23.1 s)
and library-module mode (38.1 s), with no errors or non-sorry warnings.
The first required saved-packet dry run passed at `28c09ef1094`, but did not
find the maintainer's semantic duplicate; the source repair above was therefore
performed before the final dry run and push.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
