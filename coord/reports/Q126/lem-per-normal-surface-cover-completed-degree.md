## Worker report

The module `Sheaf.DeligneLaumon.NormalSurfaceCoverCompletedDegree` states
`AlgebraicGeometry.normal_surface_cover_completed_degree`, with one whole-proof `sorry`.
It introduces no definition, axiom, auxiliary theorem, or private construction. The node
is changed only in `lean`.

Source read: `literature/stacks-project/resolve.tex`, lines 3840–3895, especially Tag 0BGN's
intermediate-field diagram and the completed-local-degree sentence. The node's reviewed
10-step argument is included in the theorem docstring, with all dependency citations.
Its explicit coordinate-injection route, rather than the older CM alternative still
mentioned in source.place, gives the required bound for each completed factor.

Hypothesis and clause correspondence:

- `Y : Scheme.{u}`, `[IsIntegral Y]`, `[IsNoetherian Y]`, `hRegular : IsRegularScheme Y`,
  `hExcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y,U)`, and
  `hDim : topologicalKrullDim Y = 2` give exactly the integral regular excellent
  Noetherian surface. Excellence is required on all affine charts, using the existing
  ring predicate; no duplicate excellent-scheme definition is introduced.
- `Y.functionField` is F; `K : Type u`, `[Field K]`, `[Algebra Y.functionField K]`, and
  `[FiniteDimensional Y.functionField K]` give the finite field extension. Its degree d
  is written directly as `Module.finrank Y.functionField K`.
- X and π are exactly `Y.normalizationIn K` and `Y.fromNormalizationIn K`.
  The conclusion gives `IsIntegral X`, integrally closed domain stalks at every x,
  `∀ U : X.affineOpens, IsExcellent Γ(X,U)`, `IsNoetherian X`, and
  `topologicalKrullDim X = 2`. The normal-stalk conjunction is the recorded normal-ring
  interface applied to local rings; there is no extra regularity assumption on X.
- The existential isomorphism `e : Spec K ≅ Spec X.functionField` and its equation with
  `(Y.fromSpecOfAlgebraFunctionField K).toNormalization` express the canonical
  function-field identification with K. The equation preserves the given extension,
  rather than allowing an unrelated abstract field isomorphism.
- `IsFinite π ∧ Surjective π` gives both morphism assertions.
- For every x with `IsClosed {x}` and `ringKrullDim (X.presheaf.stalk x) = 2`, the
  conclusion says `IsClosed {π x}` and `ringKrullDim (Y.presheaf.stalk (π x)) = 2`.
- The rings R,S in the local clause are universally quantified representatives of
  these stalks, equipped with `eR : R ≃+* O_{Y,πx}` and `eS : S ≃+* O_{X,x}`.
  This avoids forbidden statement-local lets. It adds no hypothesis on the surface:
  the canonical stalks themselves with identity equivalences are among the demanded
  cases, and all other cases are transports of that same assertion. Universes are
  explicit, and the stalk representatives have the same universe as the schemes.
- `AdicCompletion (IsLocalRing.maximalIdeal R) R`, and similarly S, are the actual
  maximal-ideal completions. The existential class proofs give regular local and
  domain structure for Rhat, local and domain structure for Shat. `IsRegularLocalRing`
  includes Noetherianity; Shat also has explicit `IsNoetherianRing` and
  `IsIntegrallyClosed` conclusions. Both are `IsAdicComplete` for their own maximal
  ideals, and `ringKrullDim Shat = 2` is asserted. No uncompleted R→S finiteness is claimed.
- The map `φ : Rhat →+* Shat` is specified at EVERY quotient level n: whenever a
  has representative r modulo m_R^n, φ(a) has representative
  `eS.symm (π.stalkMap x (eR r))` modulo m_S^n. Every quotient class has a
  representative, and completion coordinates separate points, so this specifies the
  canonical map, not an arbitrary extension or a chosen comparison. This is the
  same levelwise characterization used by `AdicCompletion.completion_finite_extension`.
  Its conclusions `φ.Finite` and `Function.Injective φ` give finite injectivity.
- The existential algebra structure on `FractionRing Rhat` acting on
  `FractionRing Shat` must commute with φ and the two canonical fraction-ring maps.
  Hence it is the uniquely induced fraction-field extension. `Module.Finite` rules
  out the infinite-dimensional finrank-zero convention; the following `Module.finrank`
  inequality is exactly `[Frac Shat : Frac Rhat] ≤ d`.
- The final universally quantified C,D have commutative-ring, domain, Noetherian and
  integrally closed instances, `[Algebra C D]` and `[Module.Finite C D]`.
  `IsFractionRing C Y.functionField` identifies F with Frac C; `IsFractionRing D K`
  identifies K with Frac D. The two scalar-tower conditions make both C→K composites
  agree. Fraction-ring maps of domains are injective, so these really encode C⊆D⊆K.
- For the given `f : Y ⟶ Spec C`, `[IsProper f]` is the properness hypothesis;
  `Y.fromSpecFunctionField ≫ f = Spec.map (algebraMap C Y.functionField)` says its
  generic map is the prescribed identity of F. The resulting `h : X ⟶ Spec D` has
  `IsProper h`; its first diagram gives `h ≫ Spec(D→C) = π ≫ f`, and its second
  gives the prescribed generic K-map. Thus this is the induced proper morphism,
  including both the base compatibility and the identity on K.

Dependency declarations read and reused:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`
  (nonempty scheme and domain section rings on nonempty opens).
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme` = locally Noetherian and upstream stalkwise regular.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`, with its
  full quasi-excellent/G-ring/J-2 and universally catenary definitions.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`; scheme dimension uses the existing `topologicalKrullDim`.
- `def-sc-function-field`: `Sheaf.AlgebraicGeometry.FunctionField`, whose docstring
  explicitly directs integral schemes to Mathlib's `Scheme.functionField`, the generic
  stalk. The components product is not used for this integral-scheme clause.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-fin-normalization-extension`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `Scheme.normalizationIn`,
  `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` with `IsDomain`, using the recorded local-domain form.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `IsFinite` (the theorem needs its finite clause).
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `Surjective` (the class on a scheme morphism).
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, `IsAdicComplete`; `AdicCompletion.Algebra` supplies `evalₐ`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec` and `Spec.map`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`.

All proof-dependency modules with recorded Lean declarations were imported, with public
imports for statement interfaces and ordinary imports for the proof plan. Other
proof-dependency statements are not re-created in this delivery. Their mathematical
content remains in the copied proof docstring.

Edge cases checked mathematically: K=F gives the identity-normalization case with local
degree one. Purely inseparable extensions are included (no separability assumption).
A finite extension may have several completion factors: the bound is ≤ d, never equality;
for example sqrt(1+t) over a characteristic-zero two-dimensional regular local model
can split into two degree-one factors. The ramified example sqrt(t) can attain d.
The local statement is conditional on dimension-two closed points, so no existence of
such a point is assumed, nor is an absent singular locus excluded. Integral Y is
nonempty; finite-dimensional field extensions have positive degree, so a spurious d=0
case is not added. Nothing assumes Y is affine, separated over an external base, or of
finite type over a field. The final proper-model condition is an implication, not an
extra requirement on every Y. No node fault or disputed statement was found.

Searches actually run (2026-10-19):

- msearch LeanFinder: `normalization finite extension scheme completed local rings field
  degree proper morphism`: eight results on relative normalization, including
  `Scheme.Hom.normalization`, its integral instance, `normalizationDesc`, and its maps;
  none states the excellent surface/completed-degree theorem.
- msearch Loogle: `Scheme.normalizationIn, IsRegularScheme, IsExcellent, functionField`:
  zero results, unknown identifier `Scheme.normalizationIn` in the Mathlib service.
  This is not a claim of absence upstream: its upstream source was read and used.
- msearch grep: `normalizationIn|completedDegree|completionMap`, Mathlib subdirectory
  `AlgebraicGeometry`: zero matches.
- msearch LeanSearch: `normalization of excellent regular surface finite field extension
  completed local degree bound`: eight hits, mostly Dedekind ramification/inertia and
  polynomial integral normalization. These do not state the surface theorem.
- rg in `WeilConjectures/` and `lean/Sheaf/` for the item ID, `normalizationIn`, and
  completed-degree phrases: upstream normalization-in-a-field and its function-field
  identification exist and are used; the affine smooth-curve theorem is only a
  dimension-one finite-type specialization. The completed surface theorem is absent.
  The existing complete-normal-surface-resolution module cites this node in its proof
  docstring but does not state it. `dag/lean_names_upstream.json` has no item-ID match.
- rg for `IsExcellent` on affine opens, completion-map interfaces, and normal-scheme
  predicates located the published excellence convention, the private completionMap
  (not an exposed interface), and the published levelwise completion-finite-extension
  interface. No second definition of these notions is needed.

Validation: scompile.py compiled the sandbox and named library module, both clean,
about 4.5 seconds each. Every variable and universe is explicit; no line exceeds 100
characters. The sole theorem proof is `sorry` as required by stage 2.

## Second reading by Q126

This is the dispatched worker's second pass, not an independent-agent review; the brief
prohibits starting another agent and assigns independent review to the maintainer.
I reread the node's entire statement and the Lean signature after the clean compile.
The essential checks were the normality/domain conjunction (not regularity of X),
the condition on closed points and their local dimension, both completions being
complete for their OWN maximal ideals, the levelwise map being the actual stalk map,
and the induced fraction-field algebra being constrained by its commutative square.
The universally quantified stalk representatives specialize to the stalks with identity
equivalences, so no point or surface is excluded. Both generic-field diagrams were
checked: the first identifies k(X) with K canonically; the last fixes the identity on K
for the induced proper morphism. The C,D scalar towers fix the subring inclusions.
No mismatch required a statement correction. The finite-morphism import was made
public because `IsFinite π` belongs to the statement, not only the proof plan.
