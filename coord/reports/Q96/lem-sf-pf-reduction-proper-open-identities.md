## Worker report

This delivery states `AlgebraicGeometry.ProEtale.PfReductionFactors.pfReductionProperOpenIdentities`
in `Sheaf.Paper.PfReductionProperOpenIdentities`. Its proof is `sorry`. Six real helper
definitions expose the proper/open maps, inputs and complete conclusion. Two further real
definitions now live in their owning definition module. Two definition nodes record the
compact-support restriction and scalar-coordinate constructions. There are no dependency
module repairs and no natural-language statement correction.
The existing Q37 review is a stage-1 split review; the node had no Lean attachment.

Hypothesis and conclusion matching:

- The finite-field datum is `D : FiniteFieldDatum`; its coefficient datum is `C : D.CoefficientDatum`.
  They retain the specified algebraic closure, prime different from the characteristic, and
  coefficient algebraic closure. `E`, its `Field`, `Algebra (Padic C.l) E`, and `FiniteDimensional`
  instances are the stated finite extension. Only the finite-field and coefficient data are used.
- The source's positive exponents n,m are Lean's `n+1,m+1`, for arbitrary naturals n,m.
  `_hmn : m ≤ n` gives the inclusion of the two coefficient ideals. `Ideal.Quotient.factor`
  is exactly the quotient homomorphism A_(n+1) to A_(m+1). Every positive pair, including
  equal levels and level one, occurs. Finiteness is the already imported theorem-backed
  instance `WeilConjectures.pullbackTensorCoefficientFinite`.
- `X Y : SixFunctorSpace D` are the existing full category of finite-type k-schemes.
  `IsSeparated X.obj.hom` and its Y counterpart impose their separation over k.
  `f : X ⟶ Y` is a k-morphism. Its `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  instances are precisely separated finite type. `d : Compactification f.hom.left` supplies
  Z, `d.i = j`, `d.g = r`, the open immersion, properness, and factorization equality.
- All formulas use `Scheme.proEtaleDerivedCategory` with ordinary constant-ring modules
  and module universe u+1 over a site with object universe u+1 and morphism universe u.
  `models : OpenScalarTensor.Models` and `choices : Choices models` are existing normalized
  presentations of those tensors and scalar derived adjunctions. Their tensor comparisons
  carry the existing chain-level pure-tensor characterization. They are presentation data,
  not arbitrary functors or maps. Their availability is the existing
  `open_scalar_tensor_models` / `open_scalar_tensor_normalization` theorem.
- K and L are fixed-module derived-plus objects. `input` applies exactly the already published
  `sfIntrinsicDerivedEquivalence` to their underlying complexes, so these represent arbitrary
  bounded-below intrinsic inputs. The predicates `_hK` and `_hL` use the recorded
  `WeilConjectures.finiteTorConstructible`, giving bounded constructibility and finite Tor amplitude.
  `wK,wL : Scheme.FixedEtaleOriginWitness` retain the exact etale antecedents and comparison
  isomorphisms. `_hwK,_hwL` use `finiteTorConstructibleEtale` on those antecedents, imposing
  the bounded constructible finite-Tor requirement on the retained witnesses themselves.
- `tensor models A T` is the existing unbounded derived tensor. `scalar models φ T` is
  derived scalar extension with its B-action. `choices.scalarTensor φ T` supplies s.
  `lambda models φ u` is the canonical comparison in the inverse direction to t_u;
  `mixedScalar` is s followed by `tensor.mapIso (1,t_u)`, exactly a^u.
- `properProjection` transposes the pullback tensorator followed by counit tensor identity
  under the existing geometric adjunction. It is exactly the counit-defined pi.
  `properScalar` is the mate of lambda=t_r inverse under those same adjunctions, exactly c.
- `pA,pB : Projection` are the existing presentations of the canonical open tensor map.
  Their `inverse_adjunct` field determines that map by the open Hom bijection; they are
  not unnormalized maps or a compatibility assumption. `openTensor` takes their forward
  isomorphisms and applies the canonical j*/r* compositor. Thus it is exactly gamma.
  Formulas write j followed by r in pullbacks; the compactification's factorization
  identifies that composite with f, retaining the canonical compositor.
- `beta models φ j` is precisely d, the common-right-adjoint open/scalar comparison.
  `compactRestriction` conjugates the published intrinsic restriction comparison by
  `reductionOpenModel` at the open factors. `compactScalar` is defined independently
  by its scalar Hom adjunct: compact support of the scalar unit followed by that
  canonical restriction comparison. This is the specified c_f in the same coordinates.
- `Identities` has five conjuncts. The first explicitly states c's naturality for
  every h:V→W. The second is c_f(K)=Rr_*(d_K)∘c_(j!K). The third is the same equation
  at H=K tensor Lf*L. The fourth is the displayed proper identity, with M=j!K and
  reduced proper input rho_Z(M). The fifth is the displayed open identity, with d_K
  inserted on the right before gamma_B. Lean `≫` composes left to right, so the
  textual order of every composition is the reverse of the source's right-to-left notation.
  All equations are in the B-linear derived categories, with no flatness or projection
  invertibility hypothesis or conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorDatum`: finite-field/coefficient data and `SixFunctorSpace`,
  through its recorded operation-stage imports.
- `WeilConjectures.Compactification.RefinementCategory`: the recorded compactification
  interface; underlying `Compactification` supplies the two factors and their properties.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` and
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: constant coefficients,
  `Scheme.proEtaleDerivedCategory`, the normalized pullback/direct image adjunctions.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`: recorded coefficient-operation
  comparisons; the helpers select their already defined normalized ringed scalar/tensor maps.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: `Scheme.FixedEtaleOriginWitness`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale` and its imported
  `finiteTorConstructible` from `Sheaf.Paper.FiniteTorAmplitude`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, imported through the recorded six-functor
  data: the counit projection and compositor-containing open projection convention.
  The helpers spell out its finite ordinary-site specialization using the existing adjunction.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`: the recorded compact-support scalar
  adjunct convention and its imported `CoefficientTensorModel` universal-arrow comparison.
  `compactScalar` writes the same scalar-adjunction universal map on intrinsic constant
  coefficients, rather than assuming the factorization that this node asserts.
- `Sheaf.SixFunctors.OpenScalarTensorData`: `Models`, `Choices`, `Projection`, `tensor`,
  `scalarPair`, `scalar`, `lambda`, `beta`, `restrictionTensor`.
- `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`: `reductionOpenModel`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`:
  `intrinsicCompactSupportRestriction`, with its published section-normalized restriction maps.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`:
  `Scheme.proEtaleConstantRingPullbackComposition`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `Scheme.sfIntrinsicDerivedEquivalence`, the existing fixed/intrinsic coefficient transport.

The existing operation-definition ids and two definition owners are included in `stmt_deps`.
The theorem `lem-sf-compact-support-restriction-of-scalars` stays in `proof_deps`, where its
composition law belongs. It is no longer a statement dependency used only for a plain def.
The six retained helper docstrings name the item; the two moved helper docstrings name their
definition owner. The single postponed theorem retains its full eight-step proof docstring.
Scoped `attribute [-instance] ... in` commands prevent an imported broad integral-Hom
localization instance from leaving unresolved coefficient-universe metavariables during
elaboration. They apply only to the immediately following declaration and impose no size
restriction and make no exported instance change.

Edge cases checked: n=m (the quotient factor is the identity case), level one, j=id,
r=id, empty X/open, and zero K or L. No nonempty or nonzero hypotheses occur. The
nonflat quotient Z/l^2→Z/l is permitted: every scalar operation is derived and the
proper coefficient map is a mate, without an assertion that pi is invertible.

Searches made: `msearch.py` LeanFinder query “Derived scalar extension commutes with
proper projection and open extension by zero tensor projection for a compactification”
returned 8 hits about ordinary module scalar associativity, condensed projection and
Stone–Cech extension; none states these derived sheaf identities. The Loogle query
“CategoryTheory.Adjunction, CategoryTheory.MonoidalCategory, Sheaf.derivedExtendScalars”
returned 0 hits (the last expected name is not present). The Mathlib grep query
“projection.*scalar|scalar.*projection|open.*tensor”, CategoryTheory, returned only
`Mathlib/CategoryTheory/Monoidal/Internal/Module.lean:33`, an `open scoped TensorProduct`.
Repository rg searches for proper/open scalar and tensor projection names found the
recorded general ringed coherence and open/scalar normalization interfaces, which the
module reuses. Searching the exact item id under WeilConjectures and Sheaf found no
existing declaration. The exact tool outputs remain in the sandbox's searches.jsonl.
The source blueprint paragraph and Stacks sites-cohomology.tex remark-compatible-with-diagram
were read directly. No statement dispute was found.

All currently stated proof-dependency modules are imported (statement dependencies publicly,
proof-only dependencies privately). The adjunction-mate node is a Mathlib leaf and its
`CategoryTheory.mateEquiv` is already publicly provided by the supplied projection module.
`compactScalar` writes the recorded `intrinsicCompactSupportCoefficientComparison` universal
formula in the normalized `models` scalar adjunction and `openExtension` coordinates; these
have different chosen adjunction presentations from the recorded `pbcDerivedExtend` and
`sfIntrinsicExtensionByZero` coordinates. The formula uses their actual units and the
conjugated canonical restriction isomorphism, so it retains the specification of the
published map without adding a comparison-map parameter.


## Repair of the returned immutable head c221b884ee45

The saved packet was inspected and dry-run first: commit af8991aaeb1 passed preflight
and compilation. That mechanical pass did not settle the independent H2 return. The
following changes repair it without changing the reviewed theorem, its five conjuncts,
its hypotheses, or the mathematical formula of any helper.

1. `def-sf-intrinsic-compact-support-restriction` now owns the published plain definition
   `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction`, with `existing: true`
   and its unchanged module. The item cites that definition node in `stmt_deps` instead
   of `lem-sf-compact-support-restriction-of-scalars`. The latter remains in `proof_deps`.
2. `def-sf-compact-support-scalar-coordinates` owns `compactRestriction` and `compactScalar`.
   Their existing formulas were moved into `Sheaf.Paper.CompactSupportScalarCoordinates`;
   the item imports it publicly and removes these names from its own `lean.declarations`.
   The new node explicitly cites `def-coef-compact-support-tensor-comparison`. Its statement,
   Lean note and module docstring explain why the recorded
   `intrinsicCompactSupportCoefficientComparison` cannot be applied definitionally: it uses
   `pbcDerivedExtend` and `sfIntrinsicCompactSupport`, whereas these formulas use `scalarPair`,
   `directImageConstantPush` and `openExtension`. These are chosen adjunction presentations.
   The new formula is the same universal construction evaluated on their actual units and
   Hom bijections, with the canonical restriction conjugated by `reductionOpenModel`.
   No map is taken as a free parameter and no factorization identity defines it.

The current read clone still has `lean: null` on the item. The wrapper builds the repaired
packet on the current server base, retaining current-main records outside the authorized
fields. No shared source or launcher script was edited and no direct Git command was run.

## New nodes

`def-sf-intrinsic-compact-support-restriction` records only the concrete canonical
restriction isomorphism, not the composition theorem formerly sharing its owner. Source:
Stacks 0GL6, proper/open restriction paragraph, and the published ring-sheaf normalization.
The existing declaration is reused without copying its module. Finite rings and a ring map
are precisely its coefficient binders; `j` has `IsOpenImmersion`, `r` is arbitrary, and
`scalarRestriction φ X ⋙ reductionCompactSupport A j r ≅ ... ⋙ scalarRestriction φ Y`
is the stated natural isomorphism. Its body first whiskers the open restriction isomorphism
and then the inverse direct-image restriction isomorphism. The node asserts no cocycle.

`def-sf-compact-support-scalar-coordinates` records the two real coordinate formulas needed
by conjuncts 2 and 3. Source: the same Stacks 0GL6 scalar-change paragraph, 07A6 scalar
adjunction, and the exact universal-arrow definition in the cited def-coef node. Its
finite-ring, scheme-map and open-immersion binders match both declarations. The normalized
model is the `m : Models` argument of `compactScalar`. For arbitrary B-object `N`,
`compactRestriction` is direct-image of `reductionOpenModel A j` inverse, then the published
intrinsic restriction component, then scalar restriction of direct-image of
`reductionOpenModel B j`. For arbitrary A-object `K`, `compactScalar` applies the inverse
scalar Hom bijection to direct-image/open-extension of the scalar unit followed by that
restriction component. This is precisely each formula in the node's statement. There is
no flatness, properness, boundedness or invertibility condition on these definitions.

Searches for both nodes were made with the authorized `msearch.py`: LeanSearch query
“Canonical compact support restriction of scalars comparison and coefficient tensor
comparison defined by scalar adjunction unit” gave 8 ordinary module change-of-ring hits;
LeanFinder query “Compact support restriction comparison Rp_* j_! Res isomorphic Res
Rp_* j_! and scalar coefficient comparison as its adjunction mate” gave 8 compact/condensed
adjunction and scheme-module restriction hits; Mathlib grep
`compactSupport.*(Restriction|Coefficient)|intrinsicCompactSupport|compactScalar|compactRestriction`
gave 0 hits. The full query and hit names are retained in `searches.jsonl` and in each new
node's `mathlib_searches`. Repository rg found the existing intrinsic declaration only in
its theorem module and no definition-node owner. Other occurrences in DAG records are
consumer notes or theorem ownership, not the definition of this comparison. No upstream
WeilConjectures match was found. The two PfReductionFactors helpers existed only in this
saved packet; def-coef supplies their construction in other chosen coordinates. Blueprint
searches for “intrinsic compact-support restriction” and “compact-support scalar coordinates”
each found 0 nodes; ancestor is `prop-sf-pf-reduction`.

## Second reading by Q96

Self-check of this repair (the maintainer supplies the independent review): both definition
records and the resulting modules were reopened. The existing isomorphism's direction is
from compact support after restriction to restriction after compact support. In the new
coordinate formula the A open-model inverse occurs first and the B open-model hom last;
this matches the domain and codomain of the intrinsic comparison. `compactScalar` uses
`.homEquiv.symm`, so its adjunct is compact support of the X scalar unit followed by that
restriction arrow, with exactly the B-action required by def-coef. Both moved definitions retain
their original parameters and formulas; the compactRestriction call states its already fixed universe explicitly, and typed local
adjunction values fix the existing scalar/restriction functors before applying the Hom
bijection. These are real existing data, not additional assumptions. Site objects remain
in u+1, site morphisms in u, coefficient modules in u+1, and derived Homs in u+2. The old scoped IntegralHom attribute is unnecessary in the smaller module, which does
not import that instance. Instead the generic completed-coefficient sheafification
and generic scalarReductionSiteSmall instances are disabled only for compactScalar,
as in the published scalar-extension module. Its body instantiates the existing
essentiallySmallSelf theorem at the fixed u+1 size for X and Y; the finite constant-ring site conventions are unchanged. The item still asserts naturality, factorization at K,
factorization at H, the proper identity and the open identity, in that order. Its signature
and single sorry are unchanged. Definition helpers contain no sorry. Equal coefficient
levels, level one, identity maps, empty schemes, zero complexes and nonflat quotients remain
permitted exactly as in the original edge-case check. No statement correction is needed.


Validation after the repair: the prescribed scompile.py invocation checked both
`CompactSupportScalarCoordinates.lean` and `PfReductionProperOpenIdentities.lean` separately
in dependency order against the live published build. Both compile cleanly; the new module
has no sorry, and the theorem module retains exactly its original one. JSON self-checks
confirm that the item differs from current main only in `lean` and `stmt_deps`, that the
restriction theorem remains a proof dependency, that both file signatures match the recorded
signatures, and that every Lean line has at most 100 characters.
