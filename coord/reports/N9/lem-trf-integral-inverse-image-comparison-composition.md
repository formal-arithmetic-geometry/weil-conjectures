## Worker report

The module `Sheaf.Paper.IntegralInverseImageComparisonComposition` states the integral
comparison composition law and its constructibility clause. Both theorems have only
`sorry` proofs; the two helper definitions select uniquely specified data and apply
Mathlib's exact-functor localization. No theorem is proved, no dependency node is
modified, and the item's natural statement and dependency lists are unchanged.

The item was read with its full proof, every statement dependency's statement and
record, the relevant declaration signatures and docstrings, and the source blueprint
`main-20261015/blueprint/sec-trace-formula/sk-thm-trace-transport/`
`thm-trf-l-function-euler-product.proof.md`, Global powers (lines 35--54).
The source requires composition before rationalization. No statement fault or
STATEMENT-DISPUTED issue was found.

Hypotheses and clauses, in the order of the natural statement:

- Prime ell is `(l : ℕ) [Fact l.Prime]`.
- The finite coefficient extension is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The existing coefficient definitions
  choose its valuation ring and uniformizer and construct its actual quotient rings.
  There is no extra uniformizer or coefficient tower supplied by a caller.
- Schemes are `{Z W V : Scheme.{u}}`, and the isomorphisms are `(h : Z ⟶ W)
  (k : W ⟶ V) [IsIso h] [IsIso k]`. Their composite is `h ≫ k`, with its inferred
  isomorphism instance. Neither finite type nor Noetherianness is assumed.
- Ell is invertible on each scheme by `[∀ z : Z, Invertible (l : Z.residueField z)]`
  and the corresponding W and V instances. A local ring element is a unit if its
  image in its residue field is a unit: the inline `isUnit_of_map_unit` terms,
  with `map_natCast`, supply exactly the recorded kappa's stalk-unit parameters.
  These are applications of existing Mathlib lemmas, not further hypotheses.
- The small pro-etale sites are the existing `Scheme.ProEt` and its topology.
  Its object universe is u+1 and its morphism universe is u; this is not replaced
  by a site of equal object and morphism sizes. One common ambient universe for
  schemes and E follows the recorded constructible/compositor APIs; it can be
  enlarged to contain both inputs. There is no bound on the cardinality of E
  relative to an independently fixed scheme universe in the mathematical assertion.
- Completed coefficients are `completedIntegralCoefficientSheafUnrestricted` and
  `integralTowerModules`, as used by both recorded operations. Their source is the
  inverse limit of the constant positive quotient sheaves, not discrete O_E modules.
- The inverse image with transported completed action is the dependency's
  `inverseImageIntegralModules`, and on derived categories `inverseImageIntegralDerived`.
  Its action uses the inverse of `inverseImageCompletedCoefficientMap`, whose finite
  projections are the prescribed constant-coefficient structure maps.
- Completed pullback is the existing `integralDerivedPullback`. The specified kappa
  is `inverseImagePullbackComparisonDerived`, including its chosen K-flat resolution,
  zero-homotopy Roos lift and representative transport. It is evaluated on N,
  respectively `(integralDerivedPullback l E k).obj N.obj`, with the correct schemes.
- The canonical d is supplied by `integralInverseImageComposition_existsUnique`:
  it is the unique natural isomorphism of the actual module inverse images whose
  value on every section is `M.val.map` of the canonical `Over.mapComp` component.
  This both pins the canonical map and expresses linearity via the module-hom type.
  It is the very d introduced by this item's statement, not an independent notion
  needing a new node. `integralInverseImageComposition` extracts that unique map;
  `integralInverseImageDerivedComposition` applies it termwise and localizes, using
  the published `Functor.mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`.
- The specified c^E is literally `(integralComparisonComposition l E D h k N).hom`.
  `D : IntegralComparisonSystem l` exposes the dependency's normalized realization
  data. It carries the fixed coefficient reduction calculus, K-injective-normalized
  Roos comparison, and pullback realization characterized on every simultaneous
  flat-term K-flat presentation. It is not an arbitrary isomorphism or a coherence
  assumption. The dependency's `integralPullbackComparisonRealization` supplies such
  D unconditionally, including E=L and the identity coefficient embedding. The
  statement holds for the specified families in any such normalized presentation.
- The constructible input is `(N : sfIntegralConstructibleCategory l E V)`.
  The first conjunct is exactly `sfIntegralConstructible l E W
  ((integralDerivedPullback l E k).obj N.obj)`, i.e. Lk*N belongs to D^b_c(W,O_E).
- The second conjunct is `d.hom.app N.obj ≫ κ_(h≫k) ≫ c.hom =
  (inverseImageIntegralDerived l E h).map κ_k ≫ κ_h`, where Lean's composition
  reads from left to right. This is precisely c ∘ κ_(kh) ∘ d = κ_h ∘ h⁻¹(κ_k).
  Both sides have source h⁻¹k⁻¹N and target Lh*Lk*N in the actual ambient
  `DerivedCategory (integralTowerModules l E Z)`. There is no reduction functor,
  rationalization, equality only on cohomology, or assumed equality of these maps.

Dependency declarations used, with the recorded modules:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly retains
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `coefficientExtensionTransition` and states
  `finite_coefficientExtensionRing` (available transitively).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
  The scheme-property dependency is explicitly a convention collecting other nodes;
  `Scheme`, `IsIso` and residue-field invertibility express the properties used here.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, used through the dependency's canonical
  isomorphism-sectionwise model, `proEtaleIsoPostcompose`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` retains
  `WeilConjectures.completedIntegralCoefficientSheafUnrestricted` and the coefficient
  system and module constructions; its primary `integralConstantToCompletionOfUniverses`
  is not needed to state this particular equality.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`, including completeness and one common finite
  interval for all positive reductions.
- `Sheaf.Paper.DerivedPullbackTensorHom`: retains `integralDerivedPullback` and defines
  `constructibleIntegralPullback`. The latter confirms the constructible clause's
  exact underlying operation; there is no private pullback construction.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`, and the publicly
  retained `inverseImageIntegralModules`/`inverseImageIntegralDerived`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `WeilConjectures.IntegralComparisonSystem`, `integralComparisonComposition`,
  `integralPullbackComparisonRealization`. Its normalized model definitions were read.

All recorded, stated proof-dependency modules are imported without `public` where
needed only for the future proof: pre-derived adjunction, constant coefficient
composition, cone counit realization, finite pullback composition, independently
sized strict-tower derived limit, exact countable products, strict Roos comparison,
and Mathlib's abelian functor category. The proof-only node
`lem-trf-integral-pullback-resolution-matching` has no recorded Lean declaration in
the supplied DAG; there is consequently no module to import. It is not needed to
TYPE this statement. Its role is preserved verbatim in the proof docstring rather
than replaced by an assumption. The prescribed proof remains the counit comparison
of strict tower maps, not finite-reduction detection.

Edge cases checked: identity h or k, including both identities; zero N; empty schemes
and empty site objects (the section restriction formula still applies); n=1, which
is tower index zero because all imported coefficient towers use exponent n+1;
arbitrary cohomological interval, including negative degrees; coefficient field
E=Q_l and identity scalar inclusion. No positive-degree, nonzero-object,
nonempty-scheme, finite Tor-amplitude or finite-type condition is introduced.

Searches for an existing statement/construction:

- `msearch.py ... leanfinder "inverse image completed integral derived pullback
  comparison compatible with composition"`: eight hits, including ordinary
  `PresheafOfModules.pullbackComp`, `SheafOfModules.pullbackComp`, and
  `Scheme.Modules.pullbackComp`; no completed integral comparison equation.
- `msearch.py ... loogle "SheafOfModules.pullbackComp, Functor.mapDerivedCategory"`:
  zero hits; service reports unknown unqualified `Functor.mapDerivedCategory`.
- `msearch.py ... leansearch "canonical composition isomorphism inverse image
  sheaves of modules"`: eight hits, including ordinary pullback composition and
  continuous pushforward component formulas; none states this integral equation.
- `msearch.py ... grep "inverseImage.*[Cc]omp|pullbackComp"
  Algebra/Category/ModuleCat/Sheaf`: five hits in `PullbackContinuous.lean`, all
  ordinary pullback composition, rather than the completed comparison.
- `rg` on upstream `WeilConjectures` for integral inverse-image composition and on
  `SixFunctors/ProEtale` for inverse-image composition/pullbackComp: no statement
  about this specified cone kappa. The upstream pullback comparators concern
  constant/adic inverse image, not this completed-module Roos comparison.
- `grep -rn` of the exact item id in upstream `WeilConjectures`: no hits.
- `rg` on the side project's `lean/Sheaf` for integral inverse-image composition:
  only existing uses of the individual functors/comparisons and unrelated affine
  restriction composition. Read `IsomorphismComparisonScalarExtension` for the
  applicable exact-functor localization construction; it states a different square.
- Mathlib/source reads checked the full signatures of `Over.mapComp`, exact-functor
  `mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`, and the local residue
  unit-reflection lemma. No existing canonical compositor for these transported
  completed actions was found, so the section-normalized helper belongs here.

Validation: `scompile.py N9 lem-trf-integral-inverse-image-comparison-composition`
compiled both sandbox and library-path copies cleanly (5.4 s and 6.4 s); no warnings
or errors. The first attempt exposed an undetermined stalk in a residue-hom term;
all those arguments now name the full scheme stalk explicitly. Every variable
and universe is bound; `autoImplicit` is false. Every line is at most 100 characters.

## Second reading by N9

Author's separate second pass, not an independent-agent review: re-opened the node,
its source Global powers paragraph and the completed file. Checked all binders,
orientation of `Over.mapComp` and of contravariant section restriction, directions
of the localization compositor and c^E, both kappa endpoints, the constructibility
conjunct, and that the equality lives before any quotient or realization that could
lose tower homotopies. The only elaboration repair was explicit stalk annotation;
no natural-language clause or hypothesis changed. The dispatcher prohibits starting
another agent; the maintainer's independent reading remains the review gate.
