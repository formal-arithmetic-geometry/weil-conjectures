## Worker report

The delivery states the orientation-free finite-coefficient composition assertion in
`Sheaf.Paper.CompositionTensorMate`. Its main declaration is
`AlgebraicGeometry.ProEtale.CompositionTensorMate.composition_tensor_mate`.
Every helper is a construction or a definition of one of this node's clauses;
the only postponed proof is the main theorem. The R1 repair adds a definition
ownership node for the existing upstream derived tensor braiding; no statement
correction is required.

The earlier retry's reason confused the live stage-1 review with a stage-2
binding: the current node is split and reviewed by Q21 but has no `lean` record.
The stage-1 review is retained. This delivery adds the requested stage-2 statement.

### Hypotheses

* `P : WeilConjectures.PurityFiniteSetting.{u}` is exactly the recorded finite
  field, coefficient prime, finite coefficient extension, uniformizer quotient,
  and positive level. `P.Coefficient` is the standard universe lift of that
  quotient. No field assumption on this coefficient ring is introduced.
* `X Y Z : Scheme.{u}`, their `Over (Spec (.of P.field.k))` instances, and the
  `LocallyOfFiniteType` and `QuasiCompact` instances on their structure maps
  express exactly finite-type k-schemes. They are not required to be absolutely
  separated.
* `f : X ⟶ Y`, `g : Y ⟶ Z` and their `IsOver` instances express the two
  k-morphisms. `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` are precisely
  separated finite type for each morphism.
* `d e : ℕ` and `SmoothOfRelativeDimension d f`,
  `SmoothOfRelativeDimension e g` express pure smooth relative dimensions,
  including zero. No smoothness of the schemes over k is assumed.
* `Assertion` constructs the Nagata compactifications and compactness and
  flat-pullback instances internally using the published finite-field setting.
  These are not extra hypotheses of the theorem. The small pro-etale site keeps
  object universe u+1 and morphism universe u; coefficients have universe u+1.

### Every clause and its Lean rendering

All names below are in `AlgebraicGeometry.ProEtale.CompositionTensorMate`.
`D`, `S`, `F`, `G`, `unit` are aliases or constructions using the existing
small-site category, K-flat pullback, compact support, standing transported
exceptional inverse image, and derived tensor unit. `omega` is `G.obj unit`.
They do not select new operations.

* `Assertion` begins with `SmoothOfRelativeDimension (d+e) (f ≫ g)`,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of that composite.
* The `genericDomains` conjunct of `InputClause` for all finite-Tor K states exactly that
  `Rg^!` preserves the recorded `DerivedCategory.constructibleFiniteTor`.
  `TensorClause g` includes membership of `omega g`; the f and gf
  memberships and tensor-source memberships make explicit the domains used in
  the statement's adjunctions and finite-Tor tensor maps.
* `OriginClause` for f, g, gf asserts that bounded constructible sources admit
  bounded-below etale origins and their compact-support images do also. This is
  exactly the domain paragraph. It does not assert that compact support preserves
  finite Tor amplitude.
* `restrictedAdjunction` is the published restricted exceptional adjunction on
  the full bounded constructible categories. `AdjunctionClause` supplies its
  preservation proofs as conclusions and uses `Adjunction.comp`; its underlying
  counit is equated to `compositeEpsilon`, namely `Fg.map epsilon_f ≫ epsilon_g`.
* `alpha` is `originCompositionAmbient` on its origin domain. `c` is the two
  standing Hom transposes of `alpha ≫ epsilon_gf`. `Assertion` explicitly
  identifies it with `standingExceptionalComposition P f g K` for every bounded
  constructible K. `MateClause` asserts naturality on every bounded constructible object, `IsIso c`,
  and the exact transpose equation
  `Fg.map (Ff.map c) ≫ compositeEpsilon = alpha ≫ epsilon_gf`.
* `theta` is the standing Hom image of the precise composite: symmetry,
  inverse of the specified `projectionMap` component, the standing counit at the
  coefficient unit tensored with identity, and the left unitor. Its argument
  order is pullback tensor omega, as in the node. `TensorClause` for g,gf asserts invertibility on their finite-Tor domains.
  `TensorInputClause` for f tests exactly omega_g and Rg!K, the two inputs
  displayed in the node.
* `W` is `omega f ⊗ S_f.obj (omega g)`. `sigma` is symmetry, `theta f (omega g)`,
  then the inverse of `c` at the unit, in diagrammatic order. `Package` asserts
  its invertibility and the stated inverse-transpose equation for
  `sigma ≫ c_unit`.
* `t` is `Fg.map (pi_f ≫ T_f ▷ omega_g ≫ leftUnitor) ≫ T_g`, including the
  coefficient unit constraint suppressed in the TeX display.
* `r` is the pullback compositor, the signed symmetry on omega_f and pulled-back
  omega_g, the tensor associator inverse, and the inverse of the strong-monoidal
  pullback comparison. `InputClause` asserts its invertibility and the membership
  of both tensor sources in the specified finite-Tor domains.
* `lhs` is `(1 ⊗ sigma) ≫ theta_gf ≫ c_K`; `rhs` is
  `r_K ≫ (S_f.map theta_gK ⊗ 1) ≫ theta_f(G_g K)`. The equality in `InputClause`
  is literally (*), with its displayed factor order.
* `compositePi` is the successive inverse projections for f and g, preceded by
  the signed source symmetry and actual pullback compositor. `commonTranspose`
  follows it by `t ▷ K` and the coefficient left unitor. `InputClause` equates
  the actual composite-adjunction inverse image of EACH side with this map.
* The last clause of `InputClause` quantifies over every morphism between the
  finite-Tor K and L and writes the naturality square using `S_(gf).map a ▷ W`
  and `G_f.map (G_g.map a)`. Equality of the two sides gives naturality of both.

The inverse helper `inverseOnDomain` returns the uniquely specified inverse when
its component is invertible and zero otherwise. The standing Hom maps and counits
are similarly extended by zero off their domains. These totalizations are concrete
definitions, not arbitrary maps or existence choices. `Package`, `TensorClause`,
`OriginClause`, and `InputClause` establish all actual domains and the invertibility
of every displayed projection component, so no off-domain value is involved in
any asserted formula. Sigma uses the unique inverse of the specified c component;
no dualizing isomorphism is chosen independently.

### Dependencies read and used

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, with its standard quotient and size lift.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`; finite type and separatedness are the recorded
  Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: the finite intrinsic operations and
  their constant-coefficient realization; the fixed-module presentation here is
  the existing `upperStar.leftDerivedFunctor`, `derivedTensor`.
* `Sheaf.Paper.FiniteTorAmplitudeSites` and its published imports: the finite
  constructible/Tor predicates; in fixed-module coordinates this is the existing
  `ProEtale.DerivedCategory.constructibleFiniteTor`, not a new predicate.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its Data module:
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`. At finite level
  the standing operation is `ProEtale.rightDerivedUpperShriek`, with
  `rightDerivedUpperShriekAdjunction` on the specified full domains.
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originComposition`
  and its actual ambient components `originCompositionAmbient`.
* `Sheaf.Paper.EtaleOriginDerivedCategory`: `EtaleOriginDerivedCategory` and its
  fully faithful forgetful functor. Existence of an origin is expressed by the
  recorded `DerivedCategory.plusEtaleOrigin` predicate.
* `Sheaf.Paper.StandingExceptionalComposition`: `standingExceptionalHomEquiv`,
  `standingExceptionalComposition`, including their complete defining composites.
* `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `IsCohomologicallySmoothFiniteCompared`, its three clauses, and the canonical
  `finiteComparedCompactification`. The new tensor map uses the original
  pro-etale inverse-projection/counit transpose, which that interface tests in
  comparison coordinates.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the supplied-domain projection
  construction; its fixed finite specialization is the published
  `ProEtale.projectionMap` at the standing compactification.
* `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, including the
  defining Hom equivalence and `comp_counit_app`.
* `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`, with its full arbitrary ring-sheaf
  domain and constant specialization. In the fixed-module coordinates the same
  K-flat compositor is the published `leftDerivedUpperStarComp`.
* `Sheaf.CategoryTheory.DerivedTensorKoszulSymmetry`:
  `CategoryTheory.derivedTensorKoszulSymmetry`, the canonical upstream
  `DerivedMonoidal.braiding'` specialized at Qh/quasi-isomorphisms. This is
  definitionally the former `projectionCoherenceSymmetry` helper. The new
  definition node `def-pur-localized-derived-tensor-braiding` owns this
  specialization, constructed entirely from the upstream braiding. `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` is imported
  only for the coefficient-coherence proof dependency.

All stated proof-dependency modules are imported for stage 3. The source read is
main-20261015 `sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`,
Steps 1--2, and the live twelve-step split. The orientation/DNC half of the unit
is not imported into this assertion or used to replace the orientation-free maps.

### Edge cases

Identity f or g: the prescribed unit/counit and pullback constraints give the same
formulas. Relative dimensions d=0 or e=0 are admitted. K equal to the coefficient
unit reduces the common transpose to t with the unit constraints. Zero K, empty
X, empty Y, and empty Z are admitted; the corresponding categories and maps reduce
to zero. No nonemptiness or positive dimension enters any binder. A ramified
coefficient extension and level n>1 remain allowed, with the original finite
quotient ring, not a field or a reduced quotient. Signed symmetries retain odd
cohomological degrees; no parity shortcut is imposed.

### Searches

The real msearch wrapper was used with LeanFinder on the composite exceptional
adjunction/dualizing tensor/projection-counit statement: eight generic categorical
hits, no geometric theorem stating this package. Loogle on
`CategoryTheory.Adjunction.comp_counit_app, CategoryTheory.Adjunction.projectionTensorMap`
found no exact match (projectionTensorMap is project-native). The Mathlib grep for
`projectionTensorMap|dualizingComplexTensorMap|standingExceptionalComposition` in
CategoryTheory had zero hits. LeanSearch on the complete tensor mate composition
statement returned eight adjunction/composite counit facts, including comp and
comp_counit_app, which give only the categorical clause.

Project rg searches by the node id, standingExceptionalComposition, dualizing
tensor-map composition, and projectionTensorMap_comp found the generic upstream
projection tensor composition theorem, ordinary-etale invertibility criteria,
the recorded standing mate, and the downstream purity composition theorem.
Their full signatures and maps were read. None states all clauses of this node
on its actual pro-etale finite-Tor domains, so no existing binding is substituted.
The plain `CompactObject.lean` example is now a withdrawn empty module in the live
clone; the node record and the current module-mode convention were read instead.

No STATEMENT-DISPUTED issue or unit-statement fault was found.

### Elaboration of the constructions

`routeEquations`, `comparisonNaturality`, and `mateEquation` state literal
category-theoretic equations on the actual functors and maps passed by the finite
wrappers. They introduce no choice of maps or adjunctions. The `generic*` helpers cache the published structures before specializing their
coefficient instances. Their definitions are the same displayed tensor composites
and predicates. Their functor and morphism parameters are supplied with the actual
standing operations and maps in the finite wrappers; none is a parameter of the
main theorem. This avoids repeated kernel expansion of the derived tensor structure.
The final file uses the default heartbeat settings and the original 60-second
per-file compiler limit. No local notation, local instance declaration, private
copy of a mathematical notion, or extra mathematical assumption is introduced.

## Repair of return R1

The immutable returned head ad0a13107922 used the coefficient-coherence theorem
as a statement dependency solely for its `projectionCoherenceSymmetry` helper.
The saved packet still passed the initial dry run (37cc5b8b67e), confirming that
this was a dependency-ownership defect rather than an elaboration failure.
The current live item has the original fourteen statement dependencies and no
Lean record. Relative to it, this repair adds only the new definition node to
`stmt_deps` and the item's `lean` record. The theorem remains in `proof_deps`.
The item's statement, twelve proof steps and all other node fields stay verbatim.

In all four constructions (`genericTensorTranspose`, `genericSigma`, `genericR`,
`genericCompositePi`) the theorem-owned helper is replaced by
`CategoryTheory.derivedTensorKoszulSymmetry`. Its new owning definition module
specializes the existing `DerivedMonoidal.braiding'` at Qh and quasi-isomorphisms,
with the same generic-category signature as the old helper. Unfolding the two
helpers gives exactly the same expression, with the same category, instances,
factors and universes. This is the return's option to define the symmetry on the
upstream braiding. The new definition module is a public statement import;
the coefficient-coherence theorem's module is a plain proof import.
The optional extraction of the theta/pi helpers was not needed for R1; those
accepted helpers remain in the item module with their existing docstrings.

## New nodes

`def-pur-localized-derived-tensor-braiding` owns
`CategoryTheory.derivedTensorKoszulSymmetry` in
`Sheaf.CategoryTheory.DerivedTensorKoszulSymmetry`. It is precisely the canonical
Qh/quasi-isomorphism specialization of the existing upstream localization
braiding. No new derived tensor or independently chosen braided structure is
introduced. Its object and morphism universes are the independent explicit v,w;
C is `Type v`, its category has universe w, `Abelian` and
`IsGrothendieckAbelian.{w}` supply the abelian context, and the monoidal, closed,
monoidal-preadditive, braided, functorial-flat-resolution instances are exactly
the existing K-flat construction's interface. K and L range over its actual
`DerivedCategory C`, and the result is the specified isomorphism
`K ⊗ L ≅ L ⊗ K`. For symmetric coefficients this is the symmetry. These generic
binders are internal to the helper; the main theorem supplies the actual module
sheaf categories and their published instances, adding no hypothesis.

The helper's entire body is the existing `DerivedMonoidal.braiding'` at Qh and
quasiIso. Its forward and inverse data are the existing `braidingNatTrans` and
`braidingInvNatTrans`, and `braiding_hom_counit` characterizes them. The cochain
sign is inherited from upstream `HomotopyCategory.braidedCategory`, whose source
and docstring were read. The source is the canonical symmetry used in
main-20261015 composition Steps 1–2 and Stacks' usual signed derived commutativity
constraint (`cohomology.tex`, lemma-symmetric-monoidal-derived). The new node
cites the existing abstract-derived-category and monoidal-category definitions.
It needs no theorem and contains no `sorry`.

Fresh LeanSearch returned eight generic localization/flatness/total-flip facts;
LeanFinder returned eight Tor and derived-category functor facts; Loogle reported
zero matches and unknown identifier for the upstream name (it indexes Mathlib).
The Mathlib grep returned zero hits. Source rg found the actual upstream
`braiding'` and the old helper's exact specialization. DAG rg and blueprint_refs
searches found no definition node owning this specialization; in particular
`def-sfb-native-derived-koszul-braiding` owns a native condensed internal-module
instance, while `def-zl-ringed-derived-closed-symmetric-monoidal-data` owns
representative-coherence data. All fresh tool queries and actual result names
are retained in the new node's searches. The existing upstream general braiding
is used directly in the helper's body, rather than constructed again. The helper
is needed as a generic specialization to cache the category instances: directly
inlining the upstream braiding at the four geometric uses exceeded the ordinary
60-second compiler limit. Restoring the generic interface addresses the cost,
without changing the canonical map or raising any limit.

## Second reading by Q01

Repair self-check by the same worker; the maintainer supplies the independent
review. The prior independent return accepted every mathematical clause of the
item and requested only R1. The source of the old helper and of the upstream
braiding was read side by side: replacing the former by its body leaves theta,
sigma, r and the composite inverse projection definitionally unchanged. All
hypotheses, domains, origin clauses, composite counit, specified comparison,
naturality, transpose equations, tensor order and unit constraints listed above
therefore retain exactly their accepted meanings. Empty schemes, zero objects,
identity morphisms, relative dimension zero and odd degrees retain the same
signed maps. The new node's generic binders agree with the helper signature and published
K-flat interface; its specialization introduces no new assumption or universe restriction.
Only the main theorem contains `sorry`; the new declaration is a concrete definition.

### Validation

The initial saved packet passed the required dry run. `scompile.py` then compiled
each repaired delivery module against the live server sources. The local check's
main-module attempt exceeded 60 seconds, so the prescribed wrapper confirmed both
files on the server: 23.1 seconds for the new definition module and 54.3 seconds
for CompositionTensorMate, with no errors or warnings. No limit was raised.
The only postponed proof remains `composition_tensor_mate`.
The repaired packet is dry-run checked again before delivery.
