## Worker report

The module `Sheaf.Paper.IntegralTensorShriek` states both clauses of
`det-lem-int-tensor-shriek`. The two named theorem proofs are `sorry`.
`integralTensorShriek_pointComplex` is a real termwise construction, with no postponed
proof or chosen arbitrary object. The natural-language proof in the theorem docstrings
follows all thirteen DAG steps, including compatible reduction towers, the integral
criterion rather than its preservation clause, and the finite localization tower.

Hypothesis and clause correspondence:

- The prime coefficient characteristic is `(l : ℕ) [Fact l.Prime]`.
  The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The standing base is `(k : Type u) [Field k] (p : ℕ) [CharP k p]`,
  `0 < p` and `p ≠ l`, exactly the positive unequal characteristic setting.
- `X.Over (Spec (.of k))`, `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` on its structure map express separated finite type over k.
  `IsNoetherian X` renders the explicitly recalled Noetherian hypothesis.
  The sources of immersion maps inherit their base structure by composition, so no
  independent structure map or noncommuting base-map choice is imposed on them.
- The coefficient is the existing `(integralModelCondensedCoefficients l E).X`,
  the continuous condensed valuation ring, and its pulled-back ring is `condensedRingObj`.
  This is not the discrete constant ring. The ordinary ambient category is
  `DerivedCategory (pulledBackModuleObjects ... X)`, the recorded module-object category.
- Membership in Dbc is precisely the recorded `boundedConstructible (condensedRingObj ...)`.
  No completeness hypothesis is added to its definition or to input objects.
- In `integralTensorShriek_preserves`, the first conjunct quantifies every U and
  `j : U ⟶ X` with `IsOpenImmersion j`. Its conclusion applies the actual
  `CondensedRing.openImmersionLowerShriek ... j` through `mapDerivedCategory`.
- The second conjunct quantifies every Z and `i : Z ⟶ X` with `IsClosedImmersion i`.
  The image is the existing canonical `CondensedRing.lowerStar ... i` through
  `rightDerivedFunctor`. On closed immersions this is the ordinary exact termwise
  direct image in the source; it retains its canonical derived object, rather than
  assuming an arbitrary exact functor.
- The third conjunct allows every `S`, `Z`, open `v : S ⟶ Z` and closed `i : Z ⟶ X`.
  The functor is exactly open extension followed by closed direct image, so a_! is
  the specified i_* v_!, without imposing a chosen compactification.
- `integralTensorShriek_generated` takes every ambient object K with its Dbc membership.
  An `ObjectProperty` P denotes a full ambient subcategory.
- `P.IsClosedUnderIsomorphisms` and the three `P.IsTriangulatedClosed₁/₂/₃`
  express all three implications when two vertices of a distinguished triangle belong.
  Mathlib's latter classes conclude in `P.isoClosure`; isomorphism closure makes that
  exactly P. There is no additional shift, zero, retract, or summand closure hypothesis.
- The generator premise quantifies `T : X.FiniteLocallyClosedStratification` and
  `a : Fin T.n`, with the dependency's actual immersion and scheme realization.
  Open v, closed i and `v ≫ i = T.immersion a` specify the factorization of that
  actual stratum immersion. All such factorizations are allowed.
- M is an object on `T.domain a`, explicitly required to belong to its Dbc.
- The local condition is existence of an actual pro-etale scheme cover C. For every
  cover member b there is a cochain complex Q on the condensed coefficient point,
  with `IsZero (Q.X n)` outside a finite integer interval, and
  `Mod.IsFree ... (Q.X n)` in every degree. Here `Mod.IsFree` means isomorphic to
  a finite direct sum of the regular module, not arbitrary-rank freeness.
- The derived isomorphism compares the actual `CondensedRing.upperStar` restriction
  of M with `DerivedCategory.Q.obj (integralTensorShriek_pointComplex ... Q)`.
  That helper applies `(upperStarFromPoint ...).mapMod` termwise. Finite free modules
  on the point and their morphisms are finite-rank scalar modules and scalar matrices:
  Hom of the regular module into itself is the ring evaluated on the terminal
  profinite singleton, namely O_E. Choosing bases turns Q into exactly an ordinary
  bounded finite free O_E-complex, and conversely such a scalar complex gives Q.
  Thus no arbitrary sheaf-valued differential is admitted in place of the source's P.
- The generator premise concludes P of exactly i_* v_! M. The final conclusion P K
  is universally quantified over all such full subcategories; this is precisely
  membership in the smallest one, expressed through its universal property.

Dependency declarations used:

- `sk-def-sfb-dc-setting`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  its standing assumptions are expanded as binders above. No new setting predicate.
- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing the existing
  `Padic.coefficientExtensionIntegers` and spectral absolute-value construction.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint` and its actual adjunction.
- `sk-def-sfb-module-objects`: `Sheaf.Paper.ModuleObjects`,
  `AlgebraicGeometry.ProEtale.pulledBackModuleObjects` (Mathlib `Mod`).
- `sk-def-sfb-bounded-constructible`:
  `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, reusing
  `AlgebraicGeometry.ProEtale.boundedConstructible` from its published upstream import.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `CondensedRing.lowerStar` and `CondensedRing.upperStar` with their coefficient maps.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `CondensedRing.openImmersionLowerShriek`, with the derived functor supplied by
  `...Derived.OpenImmersionLowerShriek` and Mathlib's exact-functor machinery.
- `def-constructible-stratification`:
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`; no extra constructible
  stratum condition is inserted into this dependency notion.
- `def-weil-triangulated-category`: Mathlib's `Pretriangulated`, derived category
  instance, and `ObjectProperty.IsTriangulatedClosed₁/₂/₃` in `Triangulated.Subcategory`.
- `def-pc-scheme`, `def-weil-open-immersion`, `def-weil-closed-immersion`:
  Mathlib `AlgebraicGeometry.Scheme`, `IsOpenImmersion` and `IsClosedImmersion`
  in their recorded modules.
- `def-sfb-integral-model-condensed-coefficients`: `Sheaf.Paper.IntegralModelCondensedCoefficients`,
  declarations `AlgebraicGeometry.ProEtale.integralModelCondensedCoefficients` and
  `integralModelCondensedCoefficients_isCommMonObj`. It composes
  `Padic.coefficientExtensionAbsoluteValue` and `Padic.coefficientExtensionIntegers` with
  `Profinite.continuousCoefficientRingObj`. The theorem node
  `lem-sfb-integral-model-surjective-closed-reflection` is not a statement dependency: its
  reflection theorem and its module are unused here. The new owner explicitly reconciles
  this ring with `FiniteConstantModel.integralCoefficients`, which uses the same absolute
  value construction.

All recorded proof-dependency modules are imported. Mathlib proof tools are imported
as non-public imports. The currently unstated integral criterion, derived completion,
constructible comparison, and integral-heart-local-model nodes have no module to import;
they remain named in the proof plan, rather than replaced by assumptions.

Edge cases checked: empty X and zero-stratum stratifications are allowed by the dependency;
the one-stratum identity stratification also works when X is empty. Zero M is an allowed
model, represented by the zero bounded complex with rank zero terms, so no extra
contains-zero axiom is needed on P. Empty covers occur only over the empty scheme.
Integer bounds impose actual termwise boundedness, not merely bounded cohomology, on Q;
rank zero outside its support is allowed. Torsion cohomology is included (e.g. the
uniformizer two-term finite free complex). No connectedness, algebraic closure of k,
reducedness, equidimensionality, or smoothness is assumed. The equality specifying a
stratum factorization is equality of scheme morphisms, not point-set containment.

Searches performed before writing:

- `msearch.py ... leansearch`: “Open extension by zero and closed direct image preserve
  bounded constructible integral pro-etale complexes”. Eight hits concerned compact
  support of functions, proper restrictions, ordinary exact-extension properties and
  complex embeddings; none states this integral preservation and generation result.
- `msearch.py ... leanfinder`: “Extension by zero and closed pushforward preserve integral
  bounded constructible complexes, generated by extensions of locally finite free
  complexes on strata”. Eight unrelated measure-theoretic and constructible-image hits.
- `msearch.py ... loogle`: `ObjectProperty.triangulatedClosure, DerivedCategory, Module.Free`.
  No hit: unknown `ObjectProperty.triangulatedClosure`. Read the actual Mathlib
  `Triangulated.Subcategory` classes instead.
- `msearch.py ... grep`: `Constructible.*(lowerShriek|extension|strat)|lowerShriek.*Constructible`.
  No Mathlib hits.
- `rg` on Mathlib, upstream WeilConjectures and the shared `lean/Sheaf`, plus the upstream
  names table: the two chosen theorem names do not exist. Searching the blueprint ID
  in upstream WeilConjectures returned no matching declaration. Broader pattern search
  found finite/discrete coefficient and adic-system results, and
  `FlatModelGeneration`, which uses the different finite-Tor constructible encoding;
  none has this internal condensed integral module statement and its specified generators.
  The published `...Derived.BoundedConstructible` has general preservation lemmas but
  has no generation clause of this item, and supplies useful existing functor interfaces.
- Read `Mod.IsFree` and `Functor.mapMod`, the point pullback/adjunction, internal-module
  bounded constructibility, exact derived functors and all three triangle-closure classes
  directly in the pinned Mathlib/published sources.

Validation: `scompile.py Q82 det-lem-int-tensor-shriek` accepted both its isolated
sandbox check (50.3 s) and final `Sheaf/Paper/IntegralTensorShriek.lean` module check
(38.9 s), with no errors or warnings. The recorded main signature was compared byte for
byte to the file and matches; every source line is at most 100 characters.

The item has no statement correction or known mathematical dispute.

## New nodes

`def-sfb-integral-model-condensed-coefficients` is a new definition node in this delivery.
Its statement defines the commutative condensed valuation ring attached to a finite
p-adic extension, with source the coefficient-setup sentence of
`det-lem-int-tensor-shriek`. Searches found no existing node or exact declaration assembling
this object. Its module uses the two requested dependencies and records both the definition
and its commutative ring-object instance. The module docstring records that its
`coefficientExtensionAbsoluteValue` construction is the same one used by
`FiniteConstantModel.integralCoefficients`, so there is one mathematical owner.

## Second reading by Q82

A fresh reading of the repaired node, new definition node, and both modules checked the
ownership change and the consumer signatures. The item's `stmt_deps` now names only
`def-sfb-integral-model-condensed-coefficients` for the coefficient construction; the
reflection theorem node is absent. The new module imports the condensed-ring and finite
coefficient-extension interfaces, defines the continuous ring using
`coefficientExtensionAbsoluteValue`, and supplies its `IsCommMonObj` instance. The item
module imports this owner and elaborates both theorem signatures with the same ring object.
Clause (1) still has the open, closed, and open-then-closed functors and all Dbc predicates;
clause (2) still has every stratum factorization, local cover, bounded finite-free complex,
object-property closure, and generator conclusion. No hypothesis or conclusion changed,
and the two modules compile independently in dependency order.

## Dependency modules

No dependency-module repair was needed. The returned theorem dependency was replaced by
the new definition owner because only its coefficient definitions were used.
