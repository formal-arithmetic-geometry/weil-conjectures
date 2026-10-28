## Worker report

Item: `lem-sf-projection-base-change-rational`; group NF; stage 2; 2026-10-28 UTC.

This delivery records the exact existing declaration
`WeilConjectures.sixFunctorProjection_baseChange_rational` in
`Sheaf.Paper.ProjectionFormulaCoherence`, lines 586–610. The module is already
in the live library, and `scompile.py --source Sheaf.Paper.ProjectionFormulaCoherence`
confirmed its current server source. Its signature was extracted verbatim and
compared byte for byte with the read checkout. Only the item's `lean` field changes;
`existing: true` avoids a second theorem or comparison construction. No Lean file
is delivered. The existing proof is `by sorry`, as appropriate to this stage;
this delivery does not claim it proved. There is no repair note for this item.
The example `CompactObject.lean` is currently withdrawn and contains no declarations.

### Hypotheses and objects

- The ambient `universe u` and explicit section binders `{D : FiniteFieldDatum.{u}}`
  and `{C : D.CoefficientDatum}` carry the global finite field, its algebraic closure,
  prime `C.l`, its primality and its difference from the characteristic, and the
  algebraically closed coefficient field. `{E : Type u} [Field E]`
  `[Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]` is the finite extension.
  The valuation ring and uniformizer are the canonical coefficient constructions
  used by the recorded integral/rational categories. `{n : ℕ} {hn : 1 ≤ n}` is
  exactly the positive level. These variables are explicitly bound in the existing
  module at lines 90–92; none is an auto-bound implicit.
- `(S : SixFunctorDatum D C E n hn)` supplies the six-functor datum including its
  inherited `SixFunctorOperationDatum`, operation normalizations, comparisons and
  coefficient data; no new framework or independently chosen functor is assumed.
- `∀ (Q : SixFunctorCompactifiedSquare D)` quantifies over the full supplied
  compactified square. Its `X,Y,X',Y',Z,Z' : SixFunctorSpace D` are finite-type
  schemes over `D.k`, defined by `LocallyOfFiniteType ∧ QuasiCompact` over that
  field. Its `square`, `properSquare`, `openSquare`, the three commutation
  equalities, two factorization equalities, and `open_i`, `open_i'`, `proper_p`,
  `proper_p'` encode precisely the Cartesian square, the original compactification
  and its Cartesian base change. `Q.compactification` and `Q.compactification'`
  recover these exact factors. They do not choose other compactifications.
- `[IsSeparated Q.f.hom.left]` is the sole separatedness binder. In particular
  no separatedness of `Q.g` or of a structure morphism appears.
- `(K : sfRationalConstructibleCategory C.l E Q.X.obj.left)` and the analogous
  `(L : ... Q.Y.obj.left)` quantify over arbitrary bounded constructible rational
  inputs. This category is raw `ScalarLocalization` of the recorded integral
  category at its uniformizer; it does not adjoin idempotents. There is no
  `integralFiniteTorDomain`, rational finite-Tor predicate, or other input condition.

### Every arrow and clause of the equality

Lean composition `a ≫ b` means first `a`, then `b`, opposite to the written
order in the node's mathematical composition symbol.

- `U_u` is `S.higher.rational.pull u`, `F` is
  `S.higher.rational.support Q.f Q.compactification`, and `F'` uses `Q.f'` and
  `Q.compactification'`. Tensor is the bifunctor `S.higher.rationalTensor` at
  the appropriate scheme, normalized to the actual rational derived tensor.
- `P_f(K,L)` is `(S.higher.rationalExchange Q).projectionComponent K L`.
  `SixFunctorExchangeData.projectionComponent` transports the supplied
  `stage.projection` solely by the recorded operation equalities. That projection
  is the proper counit-defined mate followed by the recorded open projection.
  On the right, `compactSupportProjectionSquare Q.f' Q.compactification'`
  retains the same base-changed compactification for the component `P_f'`.
- `e_M` is `sixFunctorProjectionExchange (S.higher.rationalExchange Q) M`.
  Its definition at lines 474–487 inserts the recorded source equality transport,
  `A.stage.compactExchange.app M`, and the recorded target equality transport.
  It introduces no fresh exchange or endpoint isomorphism.
- `μ_u(A,B)` is `(sixFunctorProjectionRationalMu S u A B).hom`. The definition
  at lines 555–573 conjugates `canonicalRationalPullbackTensor C.l E u.hom.left`
  by `S.higher.rationalPullback` and `rationalTensorNormalization`. The canonical
  rational comparison is the localized integral hom and inverse in the publicly
  reexported construction module, not an arbitrary monoidal comparison.
- `κ_L` is exactly `(S.higher.rational.pullComposition Q.g' Q.f).inv.app L`,
  then `eqToHom (congrArg (fun f ↦ (S.higher.rational.pull f).obj L) Q.squareComm)`,
  then `(S.higher.rational.pullComposition Q.f' Q.g).hom.app L`. The intermediate
  morphisms are `g' ≫ f` and `f' ≫ g`, so the equality transport has the stated
  direction. The enclosing right-tensor map is `1 ⊗ κ_L`.
- The left side is `U_g.map P_f ≫ e_(K tensor U_f L) ≫ F'.map (μ_g' ≫ (1 tensor κ))`.
  This is the node's first route, with its given projection followed by exchange
  and the exact target comparison.
- The right side is `μ_g ≫ (e_K tensor 1) ≫ P_f'`. The middle arrow is
  `((S.higher.rationalTensor Q.Y').map (sixFunctorProjectionExchange ... K)).app
  ((S.higher.rational.pull Q.g).obj L)`, so it acts on the first tensor factor.
- Both sides start at `U_g(FK tensor L)` and end at
  `F'(U_g' K tensor U_f' U_g L)`. The conclusion is an equality of these actual
  arrows, not existence of an isomorphism or equality after choosing new endpoints.
  The integral and common-stage conventions in the node explain the coefficient
  system; the asserted equation here is exclusively its rational specialization.

### Dependency declarations read and used

All six statement-dependency node statements and Lean records were read, together
with the full signatures and docstrings of their recorded declarations:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`, carrying A1–A6.
- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`,
  with the integral, rational and common-stage operations and normalizations.
  Its public `SixFunctorOperationDatumStages` supplies `SixFunctorSpace`,
  `SixFunctorCompactifiedSquare`, `SixFunctorExchangeData` and its
  `projectionComponent`, used in the displayed signature and its normalization.
- `Sheaf.Paper.ConstructibleProjectionMates`:
  `WeilConjectures.CompactSupportFiniteProjection.component` (the recorded primary
  finite-domain declaration), and, for the higher-stage assertion,
  `compactSupportProjectionSquare` and `compactSupportProjectionComponent`.
  The higher-stage theorem uses the already recorded `projectionComponent`
  interface, rather than incorrectly applying the finite-domain component.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, especially
  its `exchange`, `compactExchange`, and `projection` composites. This is the
  currently recorded supplied-domain interface, avoiding the legacy duplicate.
- `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `WeilConjectures.canonicalCommonStagePullbackTensor` and its public reexports
  from `CompletedPullbackTensorConstruction`, specifically
  `canonicalRationalPullbackTensor`. The recorded node explicitly assigns the
  finite/integral/rational construction declarations to that construction module;
  the current comparison module publicly reexports them. No dependency repair
  or private substitute is needed.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory`, the raw localization abbreviation.

The statement and proof at the current blueprint
`sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence{,.proof}.md`
were read. The existing theorem is exactly its rational displayed square as
specialized and normalized by the item's statement and source header. The
existing source docstring retains the proper/open/pasting argument and scalar
transport. For stage 3, the node's now finer four-step proof remains unchanged:
choose integral objects in raw localization; discharge the uniform second-input
Tor condition via `lem-coef-integral-residue-tor`; apply
`lem-sf-projection-base-change-integral`; use the recorded operation/primitive-map
comparisons and `lem-sf-pf-coefficient-realization-transport` to identify both
localized routes; cancel the same endpoint comparison. No faithfulness of
localization or finite reduction is used.

### Edge cases

The binders allow empty schemes, zero K or L, torsion integral representatives
that become zero rationally, the identity square, f proper (identity open factor),
and f an open immersion (identity proper factor). None adds a nonemptiness or
nonzero-object condition. The formula still uses the actual unit/compositor
normalizations in identity cases. Arbitrary nonseparated g and nonseparated
structure maps remain allowed by the definitions of the square and spaces.
`n = 1` is included; `n = 0` is excluded exactly as in the coefficient datum.
No characteristic or extra Tor case is silently excluded. No statement fault or
`STATEMENT-DISPUTED` issue was found.

### Searches

- `msearch.py ... leanfinder "rational l-adic compact support projection formula
  compatibility with Cartesian base change"`: eight unrelated Nobeling/profinite
  projection results; no exact match.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.Functor.Monoidal"`:
  twelve general monoidal adjunction results, not this geometric equation.
- `msearch.py ... grep "projection.*base.*change|base.*change.*projection" CategoryTheory`:
  zero Mathlib matches.
- `rg` in `lean/WeilConjectures` for the theorem and projection/base-change phrases,
  and `grep -rn` for the node id: no exact rational compact-support statement;
  general direct-image and geometric base-change results do not have these maps.
- `rg` in `lean/Sheaf` for the theorem found the exact declaration in
  `ProjectionFormulaCoherence.lean:586`, its documented source location. Reading
  the whole signature and `sixFunctorProjectionExchange`/`RationalMu` definitions
  establishes exact agreement, including κ and endpoint normalization. This is
  the existing declaration recorded by this delivery under brief-stage2 §1/§5.
- `rg` of `dag/lean_names_upstream.json` for this name found no upstream binding.
  `scompile.py --source` confirms the exact live Sheaf theorem, not a stale local
  declaration. No source file was modified and no new notion/node was needed.

## Second reading by NF

The assigned worker re-read the node, the exact server signature, the normalized
μ and exchange definitions, and the square fields after preparing the binding.
The checks are the hypothesis/arrow matching above. In particular the first
compositor is inverse, square transport is forward, the last compositor is
forward, and tensoring the exchange acts on the first factor. No mismatch was
found and no mathematical statement changed. This is the worker's source check;
the independent maintainer review is separate, as the dispatcher brief specifies.
No additional agents were started.

## Validation

The signature is byte-for-byte the existing source signature. The node copy was
checked to equal the repository node after removing only the new `lean` field.
There is no delivered Lean file to compile under the existing-declaration rule.
The prescribed deliver2 dry run and delivery run provide the server preflight.
