## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CoefOpenCounit.open_scalar_adjunction_counit`
in `Sheaf.SixFunctors.OpenScalarAdjunctionCounit`. It has precisely one postponed
proof (`sorry`), for the dispatched node. The other fourteen declarations are concrete
comparison constructions, transparent aliases, or proposition definitions grouping the
clauses of this one statement. No new mathematical object is selected from a bare
existence claim. No dependency module or new DAG node is needed.

Source read: `literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/lem-coef-finite-closed-shriek.md`, especially the final
locally closed factorization paragraph and the exceptional-counit characterization;
the expanded seven-step proof and statement of the dispatched DAG node.

Hypotheses and clauses, matched individually:

* The fixed algebraic closure of a finite field is `F : FiniteFieldDatum.{u}`. Its
  `k`, prime `p`, finite base field and algebraic-closure instances are the recorded
  ones. The distinct prime is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)`.
* The two finite extensions are `(E L : Type u)` with `Field`, `Algebra (Padic l)`
  and `FiniteDimensional (Padic l)` instances for each. Positive exponents are
  `(m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)`. The coefficients are exactly
  `Padic.coefficientExtensionRing l E m` and `Padic.coefficientExtensionRing l L n`.
  The binder `φ` is an arbitrary `→+*` between these rings, hence unital. It has no
  flatness, injectivity, surjectivity, or compatibility-with-field-embedding assumption.
* `W V X : Scheme.{u}` each have an `Over (Spec (.of F.k))` structure. Each structure
  map has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances, rendering
  precisely the three separated finite-type k-schemes. `t.IsOver` and `j.IsOver`
  make both maps k-maps. `IsClosedImmersion t` and `IsOpenImmersion j` give the
  factorization; `h` is written as `t ≫ j`, so its factorization equation is built in.
  The parameter `c : Compactification (t ≫ j)` retains the compactification used to
  define the actual operations, with no replacement by arbitrary functors.
* Fixed-coefficient sheaves on the actual `ProEt.topology T` use
  `ModuleCat.{u+1} (ULift.{u+1,u} A)`. These are the published fixed-module coordinates
  of constant-ring module sheaves. The scalar clause uses the published intrinsic
  constant-ring coordinates `proEtaleRingModules T (proEtaleConstantRing T A)`.
  Both are existing equivalent presentations, not private notions of a site or sheaf.
  The object universe remains `u+1`, morphisms `u`, and module values `u+1`.
* The first two conjuncts are `CoefficientFactored F.k l E m hm t j c` and the
  identical expression for `L,n,hn`. This wrapper derives quotient finiteness from
  `Padic.finite_coefficientExtensionRing` and derives `IsNoetherian V` from finite
  type over the field and quasi-compactness. Thus the quasi-compact open immersion
  required by the low-level compositor is a consequence, not an extra hypothesis.
* `lower A c` and `upper A c` are aliases for the existing actual compact-support
  functor and comparison-transported exceptional functor with `c.hasCompactification`.
  In particular `upper` is the constructible exceptional inverse image, never an
  unrestricted pro-etale right adjoint. `counit` is the published
  `rightDerivedUpperShriekCounit`, with target compactness derived from its finite-type
  structure map. `upperOrigin` abbreviates the published origin proof, without
  introducing a new postponed theorem or proving a new mathematical assertion.
* In `Factored`, `PreservesFiniteColimits (lowerStar ... t)` asserts exactness of the
  closed direct image (left exactness is already its right-adjoint instance), so
  ordinary derived closed image is canonically termwise `t_*`. The next two clauses
  say that closed direct image and open extension each preserve the full
  `plusEtaleOrigin` class. Quantification is over that full subcategory, retaining
  every ambient morphism, without assuming constructibility of these inputs.
* `factorization` is a constructed natural isomorphism from `lower A c` restricted
  to that full origin class to ordinary derived `t_*` followed by termwise `j_!`.
  It is the inverse of the specified `originCompositionAmbient`, followed by the
  canonical special-compactification comparisons. `originCandidate` is the unique
  preimage under the published origin equivalence of the composite of
  `fixedCompactSupportComparisonIso`, the canonical etale compactification-independence
  isomorphism, and the inverse fixed comparison;
  this is not an unspecified or arbitrarily chosen endpoint isomorphism.
* The existential `e` in `Factored` is a natural isomorphism, on the full bounded
  constructible subcategory of X, from the actual `upper A c` to exact open
  restriction followed by the actual closed exceptional functor. Its following
  equation is the counit characterization: first apply the specified compact-support
  factorization to `h^!M`, then `j_!` of `t_*e_M` followed by the actual closed counit,
  then the actual open counit. This equals the actual counit of h. `closedCounit`
  itself is that actual counit transported by the specified closed comparison.
  This is precisely the counit of the composite relative adjunction `j_!t_* ⊣ t^!j^*`;
  no full unbounded exceptional adjunction is assumed. The equation fixes the
  isomorphism compatibly with the actual adjunctions, rather than asserting merely
  that their endpoints are isomorphic.
* The final clause of `Factored` quantifies over every `constructibleFiniteTor`
  object M on X and asserts that both `j^*M` on V and `t^!j^*M` on W satisfy that
  same recorded predicate. It is the published bounded constructible condition
  intersected with finite Tor amplitude, not boundedness alone. This is stated
  separately over both coefficient rings by the first two theorem conjuncts.
* `ScalarCounit φ j`, the third conjunct, quantifies over every object of the ordinary
  unbounded derived category on X. Its forward `e` is the existing `openScalarIso φ j`;
  its `r` is `(tensorPullbackIso φ j).inv`. These are already concrete natural
  isomorphisms, so their existence and naturality are retained in their types.
  `openScalarIso` is defined by `leftAdjointUniq` for the composite actual scalar
  and open adjunctions, using the existing action identification of their right
  adjoints. The scalar adjunction is the normalized one from the recorded derived
  change-of-rings interface; the scalar unit on flat-term K-flat representatives is
  `x ↦ 1 ⊗ x` in its scalar-first convention, equivalently `x ↦ x ⊗ 1` by symmetry.
  The inverse of the published balancing comparison is the scalar mate, fixing r.
  No fresh normalization or choice of scalar adjunction is introduced here.
* The equation in `ScalarCounit` is, in Lean's diagrammatic order,
  `e_(j_A^*M) ≫ j_!,B.map r_M ≫ ε_j,B,S_XM = S_X.map ε_j,A,M`.
  All arrows lie in the actual B-module derived category, so B-linearity is in
  their type. There is no boundedness or finite-Tor hypothesis on M in this clause.
  Restriction of scalars and its exactness are the existing published scalar
  restriction; the canonical restriction/pullback square is the one used literally
  in the definition of `openScalarIso`.

The definitions used directly and their owning modules:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public imports):
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.Paper.FiniteTorAmplitudeSites`: publicly retains the native
  `ProEtale.DerivedCategory.constructibleFiniteTor`; its definition in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude` was read.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and
  `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` retain the constructible
  exceptional and support conventions. Their fixed-module presentations used here are
  the existing `rightDerivedUpperShriek`, `rightDerivedLowerShriek`, and
  `rightDerivedUpperShriekCounit` in the upstream finite-coefficient derived modules.
  These use the same recorded comparison-transported functors and actual adjunctions.
* `Sheaf.Paper.SfDerivedDirectImage`: ordinary derived direct images; its existing
  fixed-module presentation is `(ProEtale.lowerStar ... t).rightDerivedFunctor`.
* `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`:
  `Scheme.exceptionalOpenAdjunction`, with its equivalent upstream fixed-module
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` used for the factored equation.
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, `originCompactSupport`, `originComposition`.
* `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `fixedCompactSupportComparisonIso`, owned by
  `def-sp-fixed-compact-support-comparison`; the canonical etale
  `Etale.rightDerivedLowerShriekOfCompactificationPlusιIso` supplies compactification
  independence in the explicit composite used by `originCandidate`.
  `SpecifiedExceptionalClassHom` is only a private proof-dependency import for the
  already recorded `thm-sf-ambient-adjoint-class`, not a statement dependency.
* `Sheaf.SecSmoothPurity.OpenScalarExchange`: `scalarExtension`, `scalarRestriction`,
  `constantPullback`, `openExtension`, `tensorPullbackIso`, `openScalarIso`.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` and
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction` retain the recorded
  everywhere-defined scalar construction and its unit-normalized adjunction.
* `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictionDerivedPullback` and `proEtaleRingRestrictScalars`;
  `Sheaf.Paper.KFlatScalarComparisonNormalization`: `ScalarPullback.θ_h` and
  `kflat_scalar_comparison_normalization`, fixing the scalar mate used by tensorPullbackIso.
* Mathlib `CategoryTheory.Adjunction.comp`, `comp_counit_app`, `leftAdjointUniq`,
  `rightAdjointUniq`, `unit_conjugateEquiv_symm`, and `eq_unit_comp_map_iff`.
* The remaining stated proof dependencies are imported privately:
  `FiniteCoefficientFlatModel`, `KFlatRingedToposPullback`, `SfPreservationClass`,
  `ProEtaleConstructibleOrigin`, `SpecifiedExceptionalClassHom`, and
  `OpenScalarTensorNormalization` (their full published module prefixes are in the file).
  No proof module is used to assume the claimed compatibility as a hypothesis.

Three existing landed nodes are added to `stmt_deps` to name constructions used
in the signature's predicate definitions: `def-sp-open-scalar-operations` owns the
canonical `openScalarIso`, `tensorPullbackIso`, and the scalar/open operation aliases;
`thm-sf-comp-composition` owns the specified `originCompositionAmbient` compositor;
`def-sp-fixed-compact-support-comparison` owns `fixedCompactSupportComparisonIso`.
The compositor constructs canonical data and was explicitly accepted as a genuine
statement dependency in the return. Neither `lem-fix-open-scalar-exchange` nor
`thm-sf-ambient-adjoint-class` is added to `stmt_deps`. The latter remains an
unchanged original proof dependency. No original statement, proof, or other DAG field
changes; all original statement dependencies are retained.

Searches actually run (see sandbox `searches.jsonl`):

* LeanFinder: `Open extension by zero commutes with derived scalar extension and
  preserves the adjunction counit` returned eight ordinary ModuleCat extension/
  restriction adjunction results, including `ModuleCat.ExtendRestrictScalarsAdj.counit_app`.
  None states the sheaf/site factorization and both counit clauses of this node.
* Loogle: `CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.leftAdjointUniq`
  returned the service's overload message; recorded as unavailable, not a negative result.
* Mathlib grep: `comp_counit_app|leftAdjointUniq_hom` in `CategoryTheory/Adjunction`
  found generic uniqueness and composite-adjunction lemmas. A second grep
  `openScalar.*[Cc]ounit|scalar.*counit|comp_counit_app` found three generic adjunction
  references. These supply the categorical ingredients, not the node's statement.
* Project rg searches in `lean/WeilConjectures` and `lean/Sheaf` for the node id found
  no existing declaration. Searches for scalar/open comparisons found the existing
  definitions in OpenScalarExchange and OpenScalarTensorData, which are reused.
  Searches for the compact-support comparison found `fixedCompactSupportOriginIso`.
  Upstream searches for `constructibleFiniteTor`, `boundedConstructible`,
  `rightDerivedUpperShriekCounit`, and exact closed direct image located the canonical
  definitions used here. The generic composition theorem does not also state the
  scalar/open counit identity, so no single existing declaration matches this item.

Edge cases checked before finalizing: empty W, V or X are admitted without nonemptiness
or dimension hypotheses; all relevant categories become zero in the empty cases.
Identity t or j is admitted and canonical unitors are included in special compactification
comparisons. Zero M is admitted. Positive exponents include level one, and scalar maps
such as Z/l² → F_l are not excluded. Unbounded M is explicitly retained in ScalarCounit.
The exceptional assertion is made on bounded constructible objects, not enlarged to
an unbounded exceptional adjunction. Neither coefficient ring is assumed flat over the
other. The lift of coefficients preserves all rings and arbitrary unital maps and does
not identify the site's object and morphism universes. There is no node fault or
STATEMENT-DISPUTED flag.

Validation: scompile.py checked the module in sandbox and real library module modes,
cleanly with no diagnostics, in 53.0 and 52.8 seconds respectively. All declarations
bind their variables and universe explicitly (`autoImplicit` and `relaxedAutoImplicit`
are false). All lines have at most 100 characters. Only the dispatched theorem has sorry.

## Second reading by Q92

A fresh reading of the node against every predicate definition checked the two
coefficient instantiations, the full bounded-constructible domain of the natural
exceptional identification, both intermediate origin-preservation clauses, the precise
finite-Tor outputs, and the arbitrary unbounded domain of the scalar equation.
The equality includes the compact-support factorization, t_* applied to the
exceptional identification, the actual closed counit, and the actual open counit;
its source is h_!h^!M and its target is M, as required. On the scalar side the
comparison orientation is the forward e and the inverse of lambda, agreeing with r
in the node. This catches the potential inverse/orientation mismatch explicitly.

Repairs during this rereading: imported the module that publicly owns the specified
fixed compactification comparison; replaced an extra quasi-compactness binder on j
by its Noetherian consequence inside CoefficientFactored; used an abbreviation for
the already published exceptional-origin proof to avoid a proposition-def linter
warning. The arbitrary compactification c is retained as the specified construction
parameter, and the comparison is the canonical one, not merely some isomorphism.
No new mathematical claim was proved in these helpers. The theorem's proof is sorry.


## Returned-delivery repair (immutable head f3f0bc7bfe34)

1. Replaced the added `lem-fix-open-scalar-exchange` statement dependency with
   the already landed definition node `def-sp-open-scalar-operations`. Its
   `existing: true` record owns every scalar/open operation used here, including
   `openScalarIso` and `tensorPullbackIso`; no exchange theorem is needed to
   form `ScalarCounit`. The public import remains its recorded defining module.
2. Replaced the added `thm-sf-ambient-adjoint-class` statement dependency with
   the already landed definition node `def-sp-fixed-compact-support-comparison`.
   Expanded `originCandidate` directly as `fixedCompactSupportComparisonIso`,
   whiskered canonical etale compactification independence, and the inverse
   fixed comparison before taking the fully faithful preimage. This is the exact
   defining body of the former `fixedCompactSupportOriginIso` call, so the
   canonical map and the mathematical statement are unchanged. The ambient
   adjunction theorem stays only in the original `proof_deps`; its private
   module import records the unchanged stage-3 proof plan.

Retained `thm-sf-comp-composition` as explicitly accepted by the reviewer: its
`originCompositionAmbient` constructs the specified compositor in `factorization`.
A new reading of the file and node checks that the repaired helpers use only the
recorded definition data at these two points. No theorem or hypothesis was replaced,
no source statement correction is needed, and no dependency node is edited. The
two coefficient instances, actual exceptional counit equation, intermediate
origin-preservation assertions, finite-Tor conclusions, and the entire unbounded
scalar counit clause retain exactly the previously reviewed signatures.

The saved-packet dry run before this repair returned OK at `074c2878527`; the
repair addresses the independent review findings beyond those mechanical checks.

Repair validation: `scompile.py` compiled the repaired module cleanly in sandbox
and library module modes (5.3 s and 5.0 s), with no diagnostics. The self-check
found only the permitted `stmt_deps` additions outside `lean`, no removed original
dependency, no change to the source statement, no overlong lines, and exactly one
`sorry`, the dispatched theorem.
