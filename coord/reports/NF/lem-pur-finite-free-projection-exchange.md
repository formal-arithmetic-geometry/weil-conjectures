## Worker report

The module `Sheaf.Paper.FiniteFreeProjectionExchange` states
`WeilConjectures.FiniteFreeProjectionExchange.finite_free_projection_exchange`.
Its one theorem has proof `sorry`; all other declarations contain concrete dispatches,
canonical comparison composites, or predicates spelling out the displayed equations.
No new independent notion or dependency interface was required. There is no
statement correction or disputed statement.

Hypotheses and objects, matched to the node:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. Primality and the different
  coefficient characteristic are `[Fact l.Prime]` and `_hl : l ≠ D.p`.
- The coefficient field is `E : Type (u + 1)` with `Field`, `Algebra (Padic l) E`,
  and `FiniteDimensional (Padic l) E`. The upper field and inclusion are
  `t.field` and `t.inclusion` in the published `FiniteCoefficientAdjoints.Stage l E`.
  Its exponent is positive: `t.exponent : ℕ+`. Thus n=1 is included and n=0 is
  excluded exactly as in the source.
- A is `(FiniteCoefficientAdjoints.baseStage t.exponent).ring`, the published
  quotient of the integers of E by its chosen uniformizer to the nth power.
  B is `t.ring`, the quotient of the upper integers by the image of the BASE
  uniformizer to that same nth power. `extensionArrow t` uses `t.inclusion` and
  equal levels, and `.ringMap` is the published quotient homomorphism. Equality
  with the upper-uniformizer en-level is equality of ideals in the imported
  `finite_free_coefficient_extension`; no unramifiedness is assumed. Finiteness
  is the published `stageFinite` instance and finite freeness of the equal-level
  arrow is the coefficient lemma, not an extra hypothesis.
- `X Y` and `X' Y'` are `Scheme.{u}` over `Spec (.of D.k)`. Each structure morphism
  has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`, expressing separated
  finite type over k. Every named map has `IsOver` for that base. The map f also
  has the separated/locally finite type/quasi-compact instances.
  `sq : IsPullback a b f g` is V'=V times_W W', with a=u, b=h', g=v. No smoothness,
  properness or Tor condition is imposed on g. The stated properties of X' follow
  automatically from this square and X,Y,Y'; those binders exclude no case.
- `pro : Bool` covers both actual small sites. `Sites.D`, `Sites.Ctf`,
  `Sites.tensor`, `Sites.scalar`, `Sites.push`, and `Sites.direct` come from the
  recorded coefficient dependency. False is the ordinary etale derived category;
  true is the fixed-scalar pro-etale presentation. `Sites.Ctf` means bounded
  constructibility and an ordered finite Tor interval, with the existing
  constructible-origin condition on the pro-etale site. Projection requires it
  on M and K; exchange requires it only on M.

Conclusions, matched clause by clause:

- `support pro A c` is degreewise extension by zero followed by the usual derived
  direct image of c.g, definitionally the published compactification functor.
  Its intrinsic presentation is `Scheme.sfIntrinsicCompactSupport` through the
  canonical coefficient realization. No new compactification is chosen.
- `comparison` is `Sites.direct φ c.g` at j_!M followed by Rp_* of
  `(scalarOpen ...).hom.app M`. `Sites.direct` is the specified B-linear proper
  counit-transpose map. On the etale site `scalarOpen` is the recorded
  `ExceptionalCoefficients.openIso`; on the pro-etale site it is left-adjoint
  uniqueness for the actual restriction square, hence the unit-normalized
  balancing isomorphism. There is no arbitrary map parameter.
- The first conjunct is `IsIso (comparison ... c M)` for every Ctf input and
  every compactification. The second gives its exact naturality equation for
  every morphism r between such inputs. Together these state the canonical
  natural isomorphism on the indicated domain.
- The third conjunct is `RefinementEquation` for every pair of compactifications
  c,d. `refinement` uses the published etale
  `rightDerivedLowerShriekOfCompactificationPlusιIso` or pro-etale
  `rightDerivedLowerShriekOfCompactificationOriginIso`, the canonical site
  transport of the former. These coherent comparisons include every proper
  refinement and identity. M is any bounded-below etale origin whose image is
  Ctf; N is ANY bounded-below origin for its scalar image and e is ANY
  representative isomorphism. The equation inserts e.inv before the B-comparison
  and e.hom afterwards, so it covers all witnesses and all isomorphic inputs.
- The fourth conjunct is `ProjectionEquation`: S(PF_A), then c on the
  tensor/pullback object, then the canonical target identification, equals the
  scalar tensorator, then c_M tensor identity, then the actual PF_B. This is
  exactly the first displayed equality with its suppressed identifications.
- The sixth conjunct's first part is `ExchangeEquation` for every c and square.
  Its left side is S(Ex_A) followed by c_{h',u*M}. The right side starts with
  inverse scalarPull for v, then v*(c_h), then Ex_B, then scalarPull for u inside
  compact support. Both are B-derived morphisms from S v* P_A M to P'_B S u* M,
  exactly the node's second displayed equality.
- The fifth conjunct asserts `ProperProjectionEquation` in the proper case and
  `OpenProjectionEquation` in the open-immersion case. The last two parts of the
  sixth assert `ProperExchangeEquation` and `OpenExchangeEquation` in those
  respective cases. The maps are the published proper counit projection, proper
  derived exchange, inverse open tensor map, and inverse open base-change
  isomorphism. These are actual B-linear equalities, not cohomology tests.
- `TensorFamily` supplies the normalized tensorator used in these equations.
  Every component satisfies imported `Sites.NormalizedTensor`: HEq with the
  actual etale tensorator, or ordinary cochain balancing normalization on the
  pro-etale site. Existence is a conclusion, not an extra assumption of coherence.
  No smooth orientation, smoothness datum, or trace compatibility occurs.

Dependency declarations read and used:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `lem-coef-finite-free-extension`: `Sheaf.Paper.FiniteFreeCoefficientExtension`, `WeilConjectures.FiniteFreeCoefficients.finite_free_coefficient_extension`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `lem-sf-proetale-constructible-origin`: `Sheaf.Paper.ProEtaleConstructibleOrigin`, `AlgebraicGeometry.ProEtale.constructible_proEtale_origin`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `lem-coef-finite-direct-image`: `Sheaf.Paper.FiniteCoefficientDirectImage`, `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `lem-weil-finite-compact-projection-formula`: `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`, `AlgebraicGeometry.Etale.isIso_finiteCompactProjection`.
- `def-cbc-exchange-map`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.

The dependency signatures and docstrings were read in their recorded source modules,
including Stage/ringMap and the two sites' scalar/tensor/constructibility/direct-image
interfaces. ExchangeProjectionStage defines the same mate/open composites; the finite
specialization here uses the actual published maps. The recorded D+ etale exchange
is used via its unbounded compactification formula restricted to bounded inputs;
both have exactly the proper-mate/open-base-change construction. All recorded
statement modules are public imports; all other stated proof-dependency modules
are non-public imports. The ten proof steps appear in the theorem docstring.

Edge checks: zero complexes, empty schemes, identity coefficient extension E=L,
positive minimum level n=1, arbitrary ramification, identity and arbitrary proper
refinements, and arbitrary horizontal k-morphisms are included. No nonempty or
smoothness hypothesis occurs. No equality of site object/morphism universes is
imposed. All variables and universes are explicit; auto implicits are disabled.

Searches performed:

- msearch LeanFinder: `Finite free coefficient extension preserves compact support
  projection formula and base change exchange maps of etale sheaves`. Eight hits
  about etale algebras/base change, no derived compact-support equation.
- msearch Loogle: `"projectionFormula", "baseChange"`. Zero hits.
- msearch grep, CategoryTheory:
  `scalar.*(projection|exchange)|coefficient.*(projection|exchange)`. Zero hits.
- msearch LeanSearch: `Finite free scalar extension commutes with compact support
  projection and base change exchange maps for derived etale sheaves`. Eight hits
  concerning ordinary algebra and ModuleCat scalar extension, no match.
- rg in WeilConjectures and Sheaf for scalar/coefficient projection/exchange,
  and grep for this node id in WeilConjectures: no exact existing statement.
  Inspected pro-etale Derived.ScalarExtension: its projection theorems transport
  invertibility, rather than stating this two-site list of actual equalities and
  refinement independence. FiniteFreeCoefficientExtension gives the ingredients,
  not this theorem. Main declaration name checked against both source roots and
  dag/lean_names_upstream.json: no collision.

Validation: scompile.py compiled the full module, including all dependency imports,
both as a sandbox module and under its intended library name, with no warnings or
errors. The earlier unknown helper name was repaired using the canonical composition
of the existing derived open-base-change isomorphism and the two exact-pullback
comparisons. There is one postponed theorem and no postponed definition data.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
