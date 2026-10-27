# Stage 2: lem-coef-finite-free-system-restriction

## Worker report

The module `Sheaf.Paper.FiniteFreeSystemRestriction` states
`WeilConjectures.FiniteFreeSystemRestriction.finiteFreeSystemRestriction`.
It asserts existence of the simultaneous scalar/geometric data with their specified
normalizations and all the displayed compatibility equations. Definitions contain
actual data; the three theorems have `sorry` proofs and full proof docstrings.
All helper declarations belong to this node and are recorded in `lean.declarations`.
There are no new DAG nodes or replacement dependency modules.

The theorem's hypotheses correspond as follows (names below lie in
`WeilConjectures.FiniteFreeSystemRestriction` unless qualified).

| Node hypothesis | Lean rendering |
| --- | --- |
| Algebraic closure of a finite field of characteristic p | `D : FiniteFieldDatum.{u}`; its fields contain the field and characteristic data. |
| Prime ell different from p | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`. |
| Finite extensions E subset L of Q_ell | `E L : Type (u+1)`, `[Field E]`, `[Field L]`, both `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]`, and `i : E →ₐ[ℚ_[l]] L`. An algebra hom of fields is the specified embedding. |
| Valuation rings R subset S | `Padic.coefficientExtensionIntegers l E/L` and the existing `integralScalarIntegerInclusion l E L i`. |
| Uniformizers pi and v, ramification index e | The dependency's chosen `coefficientExtensionUniformizer` in E and L; `ramification`, `_he : 0 < ramification`, and `_hram : Associated (i(pi)) (v^ramification)`. This is precisely pi = unit times v^e, not an unramified assumption. |
| One R-basis of S fixed at every level | `d`, `b : Fin d → S`, `_hb` asserting bijectivity of the actual coordinate sum R^d → S. This expresses a basis without inventing a second module action on S. |
| Positive levels n >= 1 and actual quotient transitions | Lean index n denotes exponent n+1. `A`, `B`, `aTransition`, `bTransition`, `levelMap`, and `levelMap_transition` use the real ideal quotients and quotient maps. |
| Fixed small pro-etale sites of separated finite-type k-schemes | `Spaces D` is the subtype of `Over (Spec D.k)` with `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` structure maps. Scheme maps in all geometric fields are arbitrary maps of their underlying schemes, as the node says. |
| Size convention | Scheme universe u, pro-etale object universe u+1 and Hom universe u; coefficient/module universe u+1 and derived localization universe u+2. No object/Hom universe equality is imposed. |

The conclusions correspond clause by clause as follows.

| Node clause | Lean rendering |
| --- | --- |
| B_n = S/pi^n S = S/v^(en), with one reduced basis | `Assertions.ramifiedIdeal` is actual ideal equality, and `reducedBasis` is bijectivity of the sum using the reductions of the same supplied `b`. The quotient transitions and coefficient inclusion are fixed constructions, not independently chosen maps. |
| Strict semilinear module-system categories and ordinary unbounded derived categories | Recorded `SemilinearProperOpen.Modules` and `Derived` over the actual constant ring systems; `systemInclusion` uses the dependency's vertical-sequence ring sheaf. No completed or bounded derived category is substituted. |
| U termwise restriction and T derived tensor | `U0` is published `SemilinearSections.res`; `U` is its exact derived localization `resD`. `ScalarAssertions.scalar.model` is the dependency's `DerivedChangeOfRingsCochainModel`; its ordinary extension is the specified sheafified tensor, and `scalar.T` is its universal derived extension. |
| Coefficient system normalized for every m >= n | `coefficientModule`, `coefficientObject`, and `ScalarAssertions.normalized` use the existing `Normalized` predicate with `(scalars X).lower.scalar`. It quantifies over every `h : n ≤ m` and the actual derived-transition adjunct, including m=n. |
| Constructible levels | `ScalarAssertions.constructible` uses the dependency's `AlgebraicGeometry.ProEtale.IsConstructible`. `fixedModule` is restriction along the canonical constant-section map into the sheafified ring, retaining the same underlying additive sheaf, rather than a new constructibility definition. |
| Tor amplitude [0,0] | `ScalarAssertions.torAmplitude` uses the recorded fixed-ModuleCat `ProEtale.DerivedCategory.torAmplitudeIn` on the degree-zero coefficient object. |
| Pullback carries B to B | `Geometry.coefficient_push` is fixed on every level and test-object section by `coefficient_push_section`, using the published constant-section `coefficientMap`. `coefficient_pull_isIso` asserts that its actual ordinary pullback adjunct is invertible; exact localization gives the derived coefficient comparison. |
| Exact ordinary tensor/restriction adjunction | `ScalarAssertions.scalar.ordinaryAdjunction`, `scalar.unit_section`, and `extension_exact`. The published `res` has finite-limit and finite-colimit preservation instances, so no second restriction exactness assertion is needed. |
| Restriction preserves K-injective complexes | `ScalarAssertions.restriction_kInjective` on complexes of entire systems, using `CochainComplex.IsKInjective`; no levelwise K-injectivity assumption is used. |
| Termwise localizations compute T,U | `extension_computes` asserts invertibility of the universal cochain-model counit on every complex, and `U = resD` is termwise exact localization by definition. |
| Derived scalar adjunction, transpose and x tensor 1 unit | `scalar.adjunction`, the `ScalarData.unit_section` tensor insertion and `transpose_model` equations. The abstract adjunction Hom equivalence sends a to eta followed by U(a); the unit normalization identifies eta with the localized actual insertion. |
| Sectionwise ordinary restriction/direct-image identity | `OrdinarySquare.push` and `push_section`, with identity on all sections `(n,V)` and hence all transitions. |
| Pullback scalar comparison | `OrdinarySquare.pull`, `mate`, then `derivedPull = Functor.mapDerivedCategorySquareIso pull`. The inverse-pull square has `push.hom` as its mate for the specified ordinary adjunctions. |
| Derived direct-image scalar comparison | `derivedPush` is the specified right mate for the published derived geometric adjunctions. `Geometry.push_isIso` asserts its invertibility separately; `Geometry.pushIso` packages it. |
| Open-extension scalar comparison | `derivedOpenInv` is the open-adjunction mate of the same pullback comparison. `Geometry.open_isIso` is separate; `Geometry.openIso` takes its inverse to match the node's direction. |
| Geometric units and counits | The ordinary mate equation and the definitions by `mateEquiv` for the specified derived adjunctions fix both unit/counit squares. They are not arbitrary isomorphisms between functors. |
| Identity comparisons and direct-image/open/pull compositors | `Compatibility.push_id`, `open_id`, `pull_id`, `push_comp`, `open_comp`, `pull_comp`, using the published `sId/jId/pId` and `sComp/jComp/pComp`. Equality transports are mapped by the functors themselves. |
| Clopen projectors | `Compatibility.clopen` uses the actual published `pi`, including its identity/zero normalization, and the specified pull/open scalar comparisons. |
| Intrinsic proper/open comparisons | `Compatibility.beta`, `alpha`, `gamma`, using the exact published transformations. The beta field is Cartesian. Alpha and gamma permit all commutative proper/open squares, including non-Cartesian refinement squares. |
| Well-typed proper/open right mate | `gamma` has diagrammatic-order endpoints `R_r ⋙ J_j ⟶ J_k ⋙ R_p`, i.e. usual-order `J_j R_r → R_p J_k`. No reversed or ill-typed mate is substituted. |
| Fixed compact-support realization and scalar comparison | `compact j p = J j ⋙ R p`, and `Geometry.compactIso` is precisely the proper-then-open scalar paste with associators. It specializes to any chosen compactification; no arbitrary compact functor is postulated. |
| Actual compactification-composition words | `compactCompositionWord` is a real word: associators, the intrinsic proper/open gamma, the open compositor, and the proper compositor. `Assertions.compact_composition` states its full comparison square before evaluation. The generator equations also apply to refinement factors (r=id); functoriality gives their finite composites and whiskerings. |
| Inverses where required, without new invertibility | `inverse_compatibility` states preservation of an already invertible factor from its hom square. Apply it to the proper/open factors when an existing compactification word uses their inverses. It assumes the two factor isomorphisms and asserts no proper/open invertibility theorem. |
| Normalized bounded constructible finite-Tor inputs, no uniform n bound | `compact_composition` quantifies over M with `Normalized` for the upper actual system and `levelwiseCtf`. The latter uses finite support of the recorded level homology, the existing `IsConstructible`, and the recorded derived tensor vanishing outside an interval. Both the cohomology bound and the Tor interval are inside `∀ n`, so no uniform interval is introduced. |
| Whole systems before evaluation or inverse limit | Every natural transformation and compatibility equation is on `Derived` of the sequence-site category. Evaluation occurs only in the hypotheses describing individual coefficient levels/input classes. No inverse limit or levelwise equality criterion replaces a derived morphism equality. |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (reexported by the
  coefficient/Tor modules): `Padic.coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionTransition`, and
  `finite_coefficientExtensionRing` (finiteness for the proof plan).
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`:
  `WeilConjectures.integralScalarIntegerInclusion`. Its existing landed definition
  node `def-weil-pbc-integer-quotient-inclusions` (Q134, `existing: true`) is added
  to `stmt_deps`. This is the canonical codomain restriction of the supplied
  field embedding; the scalar-extension theorem is not a statement dependency.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  Size and scheme-property dependency records are conventions; their actual
  universe binders and existing property classes are used directly.
- `Sheaf.Paper.SemilinearDerivedSections`, publicly exposing
  `SemilinearDerivedCalculus` and `SemilinearSystemModels`:
  `WeilConjectures.SemilinearSections.Data`, `ScalarData`, `systemMap`, `res`,
  `resD`, `evaluation`, `e`, `Normalized`; their full signatures and docstrings
  were read. `NormalizedDVRTower` uses the same transition-adjunct normalization
  in its completed-tower presentation; this item's ordinary unbounded strict
  system categories use the recorded semilinear `Normalized` directly.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (the published `res` implementation), and
  `PresheafOfModules.restrictScalars` for canonical fixed-ring coefficient transport.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the public generic
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, also used by `ScalarData`.
  No ordinary ModuleCat-only change-of-rings pair is applied to a sheaf category.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the normalized
  `ScalarData` interface expresses its section and cochain-transpose clauses.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  the recorded public `AlgebraicGeometry.ProEtale.IsConstructible` interface.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: publicly exposed
  `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn`.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
  `AlgebraicGeometry.ProEtale.SemilinearProperOpen.Modules`, `Derived`,
  `coefficients`, `transition`, `coefficientMap`, `ringSystem`, `push`, `pull`,
  `ordinaryAdj`, `P`, `R`, `J`, `adj`, `jAdj`, `pId`, `sId`, `jId`, `pComp`,
  `sComp`, `jComp`, `pi`, `beta`, `alpha`, `gamma`. These actual simultaneous
  operations and their normalization formulas, not private copies, determine
  every geometric comparison and compactification factor.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originComposition` describes the canonical origin
  principle. The strict-system realization of its word is transparently written
  here using the recorded simultaneous operations, since the item explicitly
  asks for the word in those categories.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`:
  `Padic.exists_integral_basis` (the fixed basis hypothesis and proof plan).
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` and its pasting laws;
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategorySquareIso`.

The remaining proof dependencies are retained unchanged in the DAG; no proofs are
attempted here. The main docstring spells out the route through ordinary exact
scalar adjunction, K-injective preservation and derived comparison, open extension,
clopen restriction, and mate pasting.

Edge cases checked:

- n=0 means exponent 1, not a forbidden zero-exponent coefficient ring. Every
  positive exponent appears, including the residue level. Normalization includes
  m=n and arbitrary gaps m-n.
- Ramification e>1 retains levels en rather than replacing B_n by S/v^n.
  Identity coefficient extension and e=1 are allowed. Basis rank zero is not
  artificially excluded: the bijective-coordinate hypothesis rules it out for
  the nonzero valuation ring. The same basis is used at every level.
- Empty schemes, zero modules/complexes, identity maps and identity open
  immersions remain in all quantifiers. Constructibility on the empty scheme
  and zero Tor amplitude are allowed.
- Unbounded derived systems are used throughout. The levelwise finite Tor and
  bounded cohomology intervals may vary with n; there is no global bound.
- Ordinary mates are not assumed to preserve invertibility: invertibility of
  derived push and open comparisons is asserted separately. The intrinsic
  proper/open map has the correct endpoints and is never declared invertible
  by this statement.
- Proper/open squares need not be Cartesian. Refinement squares with r=id are
  covered; Cartesian beta is stored separately. Inverses are only taken from
  supplied isomorphisms and transported by the displayed inverse-square lemma.
- Universe sizes preserve the small pro-etale site's object/Hom distinction.
  `fixedModule` transports the coefficient action canonically rather than
  shrinking the site or assuming coefficient/site universe equality.

Searches for an existing statement:

1. `msearch.py ... leanfinder` with the finite-free coefficient restriction,
   inverse systems, derived pull/push/open, mate-compatibility query: 8 hits,
   including free pullback and ordinary pushforward adjunctions; none states the
   simultaneous assertion or its compactification compatibility.
2. `msearch.py ... loogle "SheafOfModules.restrictScalars, Adjunction, PreservesFiniteLimits"`:
   zero hits (the service reported unknown identifier `Adjunction`).
3. `msearch.py ... grep "restrictScalars|changeOfRings" Algebra/Category/ModuleCat/Sheaf`:
   10 hits, including the genuine sheaf restriction/change-of-rings interfaces
   reused by the dependency. No whole-system geometric assertion.
4. `msearch.py ... leansearch "Finite free restriction of coefficient scalars on inverse module systems preserves pullback derived pushforward extension by zero and adjunction mates"`:
   8 hits: `ModuleCat.restrictCoextendScalarsAdj`, its Hom-equivalence map,
   sheaf pullback adjunctions and presheaf restriction. None is the item.
5. Local `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
   finite-free restriction/system calculus and the node id found the constituent
   scalar and geometric interfaces but no declaration of this combined result.
   The exact node-id search in `lean/WeilConjectures` found no declaration.

Source check: the DAG source records paragraph 8 of the earlier
`lem-coef-rational-operations.proof.md`; the reviewed node explicitly records its
system-calculus expansion. In `literature/blueprint/latest`, the current finite-free
coefficient source is
`sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/sk-prop-sfb-cartesian-coefficients-finite-free.proof.md`.
Its integral coordinate bijection and inverse-image naturality were read. The
current latest tree no longer has the old proof filename. No source-based change
to this reviewed node statement is necessary. No `STATEMENT-DISPUTED` finding.

Validation: `scompile.py Q34 lem-coef-finite-free-system-restriction` compiled the
sandbox and library module separately against the published live library, cleanly,
including the final identity equations and inverse-compatibility theorem.
All definitions have real data. No diagnostic declarations or extra axioms remain.

## Second reading by Q34

The dispatcher brief expressly forbids starting other agents and assigns the
independent reading to the maintainer. Accordingly this section records a separate
self-check, not a claim of an independent second worker. I reopened the full node
and final module and made the clause table above. The check added explicit identity
comparison equations and inverse-factor compatibility; it also fixed long-line
warnings. It verified positive indexing, actual ramified ideal quotients, basis
coherence, section-normalized ordinary squares, separate mate invertibility,
proper/open endpoints, and nonuniform levelwise bounds. The node's mathematical
statement, proof, and proof dependencies are unchanged. The maintainer's independent
review is still required, as specified by the worker brief.

## Repair of independent review 7ce4f7104ad0

H2: replaced the packet-only statement dependency
`lem-weil-integral-scalar-extension-well-defined` with the landed definition owner
`def-weil-pbc-integer-quotient-inclusions`. Read that node's statement and Lean
record and the full definition and docstring of
`WeilConjectures.integralScalarIntegerInclusion` in
`Sheaf.Paper.IntegralScalarExtensionWellDefined`: it is exactly the codomain
restriction used by this module. Retained that module import and the complete
reviewed Lean source. Updated `lean.note` and the dependency account above.
This is a worker repair of the returned delivery, rather than a reviewer FIX.
Comparison with the current live node confirms that only `lean` and the addition
of this landed definition to `stmt_deps` differ; no mathematical statement,
proof, proof dependency or other node field changes. The independent review
accepted the remaining mathematical interfaces and edge cases.
