## Worker report

The module `Sheaf.Paper.SixFunctorDualNotation` completes the coefficient-dual notation
of def-sf-pf on the recorded six-functor datum. It defines no new category, internal Hom,
dualizing object, Verdier dual, tensor, projection arrow, or axiom. Those notions already
have usable declarations in the three recorded dependencies; the module publicly imports
them and documents their exact expressions. The new generic helper is just partial
application of `sixFunctorDomainHom` to its coefficient tensor unit. Four specializations
use `SixFunctorDatum.finiteClosed`, `.integralClosed`, `.rationalClosed`, and `.commonClosed`.
These are real functors, including contravariance on arrows. There are no theorems,
`sorry`s, auxiliary DAG nodes, dependency repairs, or statement corrections in this delivery.

Read the node's full statement and blueprint_update, and the current source
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-exchanges/def-sf-pf.md`
and its `_section.md`. The current source has the same three defining formulas. The node's
longer statement clarifies the supplied domains and the forward references. None needs changing.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| In the six-functor datum | `S : SixFunctorDatum D C E n hn`, with explicitly bound `D : FiniteFieldDatum.{u}`, `C : D.CoefficientDatum`, `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`, `n : ℕ`, `hn : 1 ≤ n`. The datum retains all four coefficient stages and axioms A1–A6. |
| Same derived pullback, tensor, and internal Hom | Public import of `Sheaf.Paper.DerivedPullbackTensorHom`; `sixFunctorDomainHom` restricts the actual finite `sixFunctorFiniteHom`, integral `constructibleIntegralHom`, rational `rationalDerivedInternalHom`, and algebraically closed `commonStageDerivedInternalHom`. No bifunctor is supplied afresh. |
| Coefficient unit `Λ_T` | `M.closed.monoidal.tensorUnit`, an object of the existing finite-Tor category for the selected coefficient stage. This is the tensor unit of its supplied closed presentation. |
| Separated finite-type k-scheme X | `X : SixFunctorSpace D` bundles the given map to `Spec (.of D.k)` and its locally-finite-type/quasi-compact properties; each of the four new stage definitions additionally binds `[IsSeparated X.obj.hom]`. No smoothness or properness is imposed. |
| Base s and structure map a_X | Existing `sixFunctorPoint D` and `sixFunctorStructure X`; their underlying scheme and morphism are `Spec (.of D.k)` and the original `X.obj.hom`. |
| `ω_X = Ra_X^! Λ_s` | Existing `S.finiteDuality.dualizing X c`, `S.higher.integralDuality.dualizing X c`, `S.higher.rationalDuality.dualizing X c`, `S.closure.commonStageDuality.dualizing X c`. Unfolding `SixFunctorDualityData.dualizing` gives `(stage.exceptional (sixFunctorStructure X) c).obj duality.unit`. Its base coefficient units are already normalized by the operation datum. |
| K in D^b_ctf | Finite and integral definitions take the opposite of `(S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory` and its integral counterpart. Rational and common-stage definitions use the full `⊤` subcategories, exactly the datum's field-coefficient finite-Tor convention. |
| Verdier dual `RHom(K, ω_X)` | Reused `S.toSixFunctorOperationDatum.finiteVerdier X c`, `.integralVerdier X c`, `.rationalVerdier X c`, `.commonStageVerdier X c`. Their bodies call `SixFunctorDualityData.verdier`, which pairs the contravariant input with the very dualizing object above and applies the dependency's internal Hom. These already exist on bounded constructible inputs and hence apply to the specified finite-Tor inputs. |
| Coefficient dual `RHom(K, Λ_X)` | New `SixFunctorDatum.finiteCoefficientDual`, `.integralCoefficientDual`, `.rationalCoefficientDual`, `.commonStageCoefficientDual`. Each calls `sixFunctorCoefficientDual`; its body is `(Functor.curry.obj (sixFunctorDomainHom P Q H M.homPermitted M.homDomain)).flip.obj M.closed.monoidal.tensorUnit`. Thus the second input is the tensor unit, not the dualizing object, and arrows act contravariantly through the recorded Hom. |
| Separated finite-type f:X→Y and its compactification | Existing projection notation takes `Q : SixFunctorCompactifiedSquare D`, with `Q.f` the over-k morphism and `Q.compactification` its specified open/proper factorization, or the concrete `c : Compactification f` directly. Separation and finite type have the meanings inherited from the recorded operation datum and the compactification. The same maps specialize to separated finite-type X,Y. No new square or compactification is chosen here. |
| `PF : Rf_!K ⊗ L → Rf_!(K ⊗ Lf^*L)` | For the abstract datum, reuse `((S.toSixFunctorOperationDatum.finiteExchangeProjection Q).2.2.app K).app L` at finite coefficients, and `(S.higher.integralExchange Q).projectionComponent K L`, its rational counterpart, and `(S.closure.commonStageExchange Q).projectionComponent K L`. The latter has exactly the stated source and target in `SixFunctorExchangeData.projectionComponent`. |
| Concrete PF, including finite K in D^b_c and L in D^b_ctf | Reuse `((AlgebraicGeometry.ProEtale.projectionMapOfCompactification A c).app K).app L` in the existing sheaf realization, or `ExchangeProjectionStage.projection` in the supplied domains. The concrete finite map has ambient inputs, so this includes the larger constructible/finite-Tor domain; the datum's finite-Tor-only wrapper is not substituted for that larger domain. The intrinsic finite operations use the recorded `sixFunctorFiniteRealization` comparison. |
| Chosen-compactification meaning and suppressed superscript | Existing `ExchangeProjectionStage.projection` composes the proper counit projection mate and the open projection comparison, transported by its compact-support identification. The datum retains its compactification/coefficient comparisons; no independence or invertibility theorem is added. |
| Integral completed operations | `S.integralClosed X` uses `constructibleIntegralHom`, restricted from Hom over the completed ring sheaf. The existing integral projection stage is normalized to completed pullback/tensor by `SixFunctorHigherOperations` and `SixFunctorIntegralNormalization`. |
| Rationalization and common-stage scalar extension | `S.rationalClosed X` and `S.commonClosed X` use the dependency's rational and common-stage Hom functors, including their normalized morphism actions. The existing higher-stage projection data retain the corresponding comparison equations; no rational-to-finite reduction is introduced. |
| A3 invertibility only on the displayed finite-Tor domain | Existing fields `S.finiteProjection`, `S.integralExchange.projection`, `S.rationalExchange.projection`, `S.commonExchange.projection`. These remain hypotheses of the datum, not new theorems. |
| Forward references to concrete PF theorems | Documented as forward references in the module docstring; no theorem, claim of existence, or proof dependency is introduced for them. |

Dependency declarations and source reading:

- `Sheaf.Paper.SixFunctorDatum`: read `SixFunctorDatum` in full, `SixFunctorClosedDomain`,
  and `sixFunctorDomainHom`. The latter's `homPermitted` and `homDomain` witnesses come
  from the supplied datum, so the new definition imposes no extra Hom-constructibility
  hypothesis and does not choose a replacement object.
- Its public dependency `Sheaf.Paper.SixFunctorOperationDatum` and
  `Sheaf.Paper.SixFunctorOperationDatumStages`: read the full signatures/docstrings of
  `SixFunctorSpace`, `sixFunctorPoint`, `sixFunctorStructure`, `SixFunctorDualityData`,
  `.dualizing`, `.verdier`, all four operation-datum Verdier definitions,
  `SixFunctorExchangeData.projectionComponent`, `finiteExchangeProjection`,
  `sixFunctorFiniteHomPairs`, and `sixFunctorFiniteHom`. Also read the finite,
  higher, and common-stage unit normalizations and exchange-data interfaces.
- `Sheaf.Paper.DerivedPullbackTensorHom`: read `constructibleIntegralHomPairs`,
  `constructibleIntegralHom`, `constructibleRationalHomPairs`,
  `rationalDerivedInternalHom_existsUnique`, `rationalDerivedInternalHom`, and the
  complete signature/docstring of the recorded main declaration
  `commonStageDerivedInternalHom_existsUnique` and its chosen uniquely specified functor.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: read `ExchangeProjectionStage`,
  `compactificationProjectionFromData`, and `.projection`, including the two comparison
  transports and the absence of any invertibility assertion.
- The concrete finite map is already in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`,
  `AlgebraicGeometry.ProEtale.projectionMapOfCompactification`; read its full signature,
  docstring, and composite. It is reached through the operation datum's imports.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`, `CoefficientClosedStructure`: read its
  full structure. Its `monoidal` field supplies the coefficient tensor unit; its Hom
  adjunction fixes the closed tensor presentation. No file-local instance is used.

Edge cases checked before writing:

- No zero complex is excluded: the new definition evaluates the full internal-Hom
  functor at every object of the finite-Tor domain, including zero. It asks for no
  nonvanishing or dualizability witness.
- No nonempty scheme or positive dimension is assumed. The empty separated finite-type
  scheme is admitted by `SixFunctorSpace` and each new signature.
- Finite coefficients include n=1 and arbitrary allowed ramification of E. The only
  level bound is the source's `hn : 1 ≤ n`; n=0 is excluded by the source itself.
- Identity/proper/open morphisms and identity compactifications are inherited without
  exceptions from the existing projection construction. No inverse to PF is selected.
- Finite and integral Tor domains are not replaced by the entire bounded constructible
  category. Conversely the field stages use their full constructible finite-Tor
  convention, without imposing an artificial integral Tor hypothesis.
- Opposites are on the first Hom argument. Currying and `.flip.obj` fix the second
  argument, so an arrow K→K' induces K'^vee→K^vee.
- All universe variables are explicitly declared (`u a b`); categories use their
  existing universes, and no equality of site-object and morphism universes is added.

Searches for existing notions (performed before writing):

- `msearch.py NA def-sf-pf leanfinder`, query
  `Verdier dual internal Hom dualizing complex coefficient dual internal Hom unit projection transformation six functors`:
  eight hits, mostly `LightCondensed.ihomPoints` and abstract tensor-Hom/evaluation lemmas;
  none provides this four-stage coefficient-dual notation.
- `msearch.py NA def-sf-pf loogle`, query
  `CategoryTheory.ihom, CategoryTheory.MonoidalClosed`: twelve hits on the abstract
  internal-Hom API and its restrictions, no geometric coefficient-stage construction.
  Read `CategoryTheory.ihom` at Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:76:
  this chooses an already supplied closed right adjoint, rather than defining these
  finite/integral/rational/common-stage coefficient duals.
- `msearch.py NA def-sf-pf grep`, query
  `verdierDual|coefficientDual|dualizingComplex|projectionMap` in `CategoryTheory`:
  zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and
  `grep -rn 'def-sf-pf' lean/WeilConjectures`: the upstream étale `dualizingComplex`,
  `verdierDual`, and `Etale.DerivedCategory.coefficientDual` cover ordinary étale
  derived categories only, not the integral-complete, rationalized, and common-stage
  categories of this node. The pro-étale finite `derivedDual` is similarly a partial
  overlap. The operation datum already defines all four dualizing objects and Verdier
  duals and the needed projection components, which are reused rather than rewritten.
- Exact-name `rg` over Mathlib, WeilConjectures, and Sheaf for the five new names:
  no existing declaration; the only prefix overlap is the different existing
  `sixFunctorCoefficientDuality` (base-unit/exceptional-duality data at a finite field).
- `dag/lean_names_upstream.json` search for `def-sf-pf`: no additional attachment.

Validation: compiled the module with the prescribed `scompile.py` against the live
published library; both sandbox and library passes were clean, with no warnings.
The final delivery dry run is recorded by `deliver2.py`.

## Second reading by NA

No second reading by a worker: this worker was dispatched directly. Under the human's
2026-10-17 direct-delivery policy, the maintainer supplies the independent review.
