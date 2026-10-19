## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` states
`AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit`, with its proof `sorry`.
The source is the current main-20261015 blueprint node
`sec-proetale-coefficients/sk-prop-sfb-qlbar-colimit-x/sk-prop-sfb-qlbar-colimit-x-integral-limit.md`.
The natural-language proof in the theorem docstring follows all six DAG proof steps.
The resolved stage-1 repair note concerns the already-completed proof split; it does not
withdraw a Lean interface or request a stage-2 repair.

Hypotheses and clauses:

- Prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The ring, uniformizer, ideals,
  quotients and transitions are exactly `Padic.coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`,
  `coefficientExtensionRing` and `coefficientExtensionTransition` from the dependency.
  The scheme is arbitrary `(X : Scheme.{u})`, with no Noetherian or characteristic condition.
- Positive exponent n is indexed as `n + 1` for `n : ℕ`. `sfbIntegralFiniteLevel` bundles
  the recorded quotient using `finite_coefficientExtensionRing`.
  `sfbIntegralFiniteTower` is `Functor.ofOpSequence` of the recorded reductions.
  `integralCoefficientSheafSystem` is the existing ring-sheaf tower with these same levels
  and transitions, starting at exponent one.
- Clause 1, finite sets: `a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X`
  is a natural isomorphism for every `T : FintypeCat.{u}`. The first functor is precisely
  Mathlib's constant sheaf of the universe-lifted set. The second is lifted Yoneda of
  `X[T] = (profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj T)`.
  The imported `profinite_test_object_functor` identifies these finite test schemes,
  naturally over X, with the coproducts of T copies of X. A finite set admits a Fintype
  structure, so bundling excludes no finite set, including the empty one.
- Clause 1, integral profinite set: `sfbIntegralProfinite` equips the recorded integer
  ring with exactly `coefficientExtensionIntegersTopology`; its three profiniteness
  properties are projections of `coefficientExtension_integers_profinite_tower`.
  The existential cone `c` and isomorphism `j` have every leg explicitly constrained
  to `Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1))`.
  `Nonempty (IsLimit c)` records the displayed presentation of the profinite integers.
  The next `IsLimit` records the scheme presentation after the specified test functor.
  This is a cone specified by all reductions, not an arbitrary presentation.
- Clause 1, represented sheaf limit: the presheaf underlying
  `completedIntegralCoefficientSheafUnrestricted l E X` is isomorphic to lifted Yoneda
  of `X[O_E]`. This existing coefficient sheaf is literally the limit of the constant
  ring sheaves; ring and sheaf forgetful functors preserve their sectionwise limits,
  so its underlying set sheaf is the stated set-sheaf limit. Finite-level passage from
  ring to set constants uses Mathlib's actual `constantCommuteCompose`, followed by a.
- Clause 2: `sfbCondensedIntegers` uses the existing
  `Profinite.continuousMapRingObjOfUniverse` of the integer ring, with the spectral
  absolute-value topology and the canonical `Sheaf.monObj_sheafCompose_obj` structure.
  `sfbPullbackFromPoint X` is the recorded inverse image. The fourth conjunct is an
  isomorphism from its underlying set presheaf to lifted Yoneda of `X[O_E]`.
  A natural isomorphism of underlying presheaves is precisely representation of the
  sheaf, since the inclusion of sheaves is fully faithful. Universe lifts change only size.
- Clause 3: `e` is an isomorphism from `(coefficientRing X (sfbCondensedIntegers l E)).X`
  to `sfbCompletedIntegersAb l E X`. `IsMonHom e.hom ∧ IsMonHom e.inv` says it is an
  isomorphism of ring objects in abelian sheaves, the recorded encoding of ring sheaves.
  The target's ring structure is the canonical one on the existing ring-sheaf limit.
  The `∃!` predicate characterizes its finite projections: for every profinite S,
  continuous `f : S ⟶ O_E`, and positive level, the adjunction unit gives the section
  pulled back from f. Apply e, then the limit projection, then the finite-set
  representation. The result must be the map represented by `X[q_n ∘ f]`.
  This is the canonical comparison on all test objects; the adjunction and joint
  monicity of the limit projections imply uniqueness. There is no freely chosen
  coefficient map or replacement of the pulled-back ring by a discrete constant ring.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint` and its right adjoint; the helper
  adjunction is the composite of the published point and scheme pullback adjunctions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.profiniteToProEtOf`, `coefficientRing`,
  `pointUpperStarLowerStarAdjunction`, and the specified ring-object transport.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: the integer ring, spectral absolute value, uniformizer,
  quotients, reductions, and `Padic.finite_coefficientExtensionRing`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf` and
  `constantCommuteCompose`; `uliftYoneda` is Mathlib's lifted representable presheaf.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse` and `continuousMapRingObjOfUniverse`.
  The original condensed-ring dependency's upstream declarations have coefficients
  in Type 0; this already-landed node gives the same construction for Type u.
- `Sheaf.NumberTheory.Padics.IntegersProfiniteTower`:
  `Padic.coefficientExtensionIntegersTopology` and
  `coefficientExtension_integers_profinite_tower` (all universes explicitly instantiated).
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` reexports
  `integralCoefficientSheaf`, `integralCoefficientSheafSystem`, and
  `completedIntegralCoefficientSheafUnrestricted` from `CompletedIntegralCoefficients`.
  Only that unrestricted construction is used: no global finite-field datum is required.

The three already-landed nodes carrying the last three interfaces are added to
`stmt_deps`. No new node or dependency module is delivered. Existing proof-dependency
modules are imported without `public`; the proof docstring names the gluing, Yoneda,
left-exact inverse-image and ring-operation arguments they supply.

Edge cases checked: T empty, singleton and all finite sets; X empty and arbitrary
non-quasicompact X; exponent one (index zero); E = Q_l, ramified and unramified finite
extensions; arbitrary prime including two. Empty covers give the terminal sections
on the empty object. No n=0 quotient enters the positive tower. No site object/morphism
universe is collapsed: `X.ProEt` has object universe u+1 and morphism universe u;
set/abelian/ring sheaves take values in u+1.

Searches:

- msearch LeanFinder: `pro etale integral coefficient sheaf is inverse limit of finite
  constant quotient sheaves`; eight generic hits (BDeRham, BDeRhamPlus and etale algebra
  declarations), no match to this statement.
- msearch Loogle: `constantSheaf, limit` reported unknown identifier constantSheaf.
  The corrected query `"CategoryTheory.constantSheaf"` returned five constant-sheaf
  declarations, none providing the pro-etale integral comparison.
- msearch LeanSearch: `constant sheaf on pro etale site represented by finite coproduct
  and inverse limit integral coefficients`; returned constantSheaf, generic sheaf
  coproducts and light condensed results, no whole-item match.
- msearch grep: `constantSheaf|yoneda.*[Ll]imit` in CategoryTheory/Sites returned the
  generic constant-sheaf, Yoneda-limit and coherent-site ingredients.
- rg in upstream WeilConjectures for the item id and integral/limit patterns found no
  existing whole-item declaration. The published ContinuousMap and ModuleObject.Basic
  signatures were read in the shared framework, following coord/pefw-upstream-framework.md.
- rg in lean/Sheaf for integral/limit and coefficientExtensionRing first located the
  existing profinite integer tower and completed integral coefficients. A broader
  `continuousMapRing.*[Uu]niverse|continuousMapRing.*Type u` search then found
  `Sheaf.Topology.ContinuousMapCondensedRing`; the preliminary duplicate interface
  was removed and the existing declaration imported. No duplicate is delivered.
- rg in Mathlib/Condensed for continuous-map ring sheaves found no additional construction
  needed here. rg of the proposed helper names in Mathlib/upstream/source-name index
  and lean/Sheaf found no existing declarations with those names.

Validation: the final module passes scompile.py (sandbox and library compilation,
approximately three seconds each), with no errors or warnings except the permitted
postponed theorem. Every helper has real data; only the main theorem has `sorry`.
No statement correction or disputed mathematical assertion was necessary.

## Second reading by Q09

This is the author's second reading; the maintainer supplies the independent review.
I reopened the current node and the complete module after compilation. The source's
three clauses are all present: natural finite-set representability; the reduction-
specified profinite and relative scheme limits and the represented set-sheaf limit;
the represented underlying set sheaf of the pulled-back integer coefficient ring;
and the unique ring-object isomorphism to the existing ring-sheaf limit. The final
unit/projection equation fixes the canonical comparison and is typed on actual
continuous-function sections, rather than replacing the map by an arbitrary isomorphism.
I checked the directions of j, the finite-level representation, the adjunction unit,
and every limit projection. The finite-level ring-to-set comparison is the actual
Mathlib comparison, not an assumed identification. All exponents are n+1. The spectral
topology used for continuous functions is definitionally the integer topology used
for the bundled profinite integer set. The initial universe metavariable in extracting
profinite properties was repaired by explicitly instantiating both tower-theorem
universes. The already-landed generalized condensed construction replaced a duplicate
local draft. No hypothesis or conclusion was otherwise changed. No dependency node
was modified, and no proof was supplied for the main theorem.
