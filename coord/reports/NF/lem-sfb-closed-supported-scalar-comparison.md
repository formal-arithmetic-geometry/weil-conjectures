## Worker report

The module `Sheaf.Paper.ClosedSupportedScalarComparison` states
`SheafOfModules.ScalarPullback.closed_supported_scalar_comparison`, with one `sorry`.
It also supplies two real-data helpers belonging to this statement:
`ClosedScalarCalculus` packages precisely the assumed conclusions of the recorded
unbounded calculus, and `closedScalarMap` constructs the displayed natural map by
whiskering and transposing the inverse comparison followed by the old counit.
No helper theorem, new notion node, dependency repair, or statement correction is needed.

Hypotheses and objects, read against the node:

- Scheme and complementary immersions: `{X Z U : Scheme.{u}}`, `i`,
  `[IsClosedImmersion i]`, `j`, `[IsOpenImmersion j]`, `[QuasiCompact j]`, and
  `hij : Set.range j.base = (Set.range i.base)ᶜ`. Quasi-compactness is imposed on
  j, not on X, Z, U, or the ring map.
- Small pro-etale site: the existing `proEtaleSiteModel` and
  `proEtaleModelTopology` are the AsSmall transport of `Scheme.ProEt` and its
  topology. Their object and morphism universes are u+1. The original site still
  has object universe u+1 and morphism universe u. This is an equivalent site,
  not an assumption equating these universes or a different topology. Arbitrary
  coefficient sheaves on the small site correspond to arbitrary sheaves on this
  model by the existing site equivalence. This is the allowed choice of small
  model in the site's own definition. The existing node
  `def-weil-proetale-inverse-image` is added to stmt_deps to record that transport.
- Ring map: `φX : AX ⟶ BX`, with sheaves of commutative rings in universe u+1
  on the model of X. `AZ`, `BZ`, `AU`, `BU`, and `φZ`, `φU` are their inverse
  images through `iA`, `iB`, `jA`, `jB : InverseImage ...`. These are the recorded
  algebraic presentations, including ring, additive, scalar, and map graph laws.
  `hi` and `hj` say the coefficient maps agree with those inverse images.
- Actual geometric inverse images: `adji` and `adjj` identify Li and Lj as left
  adjoints to the specified pro-etale base-change direct images. Thus Li and Lj
  are presentations of the actual inverse images, determined up to their unique
  adjunction-compatible isomorphism. They are not unconstrained geometric maps.
  Their left exactness and module exactness are precisely the inverse-image
  properties supplied by the normalization dependency, not flatness of φX.
- Unbounded derived categories: `DerivedCategory (Modules R)` and the six
  `[HasDerivedCategory.{w} ...]` bind the common chosen localization universe w.
  `Modules` is the dependency's abbreviation of `ringedSiteModules`, itself
  Mathlib's `SheafOfModules`. There is no boundedness or completion condition.
- Scalar extension and canonical adjunction: `mX`, `mZ`, `mU` are the existing
  `DerivedChangeOfRingsCochainModel`s, whose T fields are the universal ordinary
  unbounded derived change of rings. Their ordinary E fields are fixed on objects
  and maps to the sheafified balanced tensor. The supplied aX/aZ/aU and dX/dZ/dU
  are pinned by `normX`, `normZ`, `normU : AdjunctionNormalized ...`, including
  the pure-tensor ordinary unit and its K-flat representative normalization.
  These are presentations of the dependency's canonical scalar adjunction.
- Open/closed functors and actual maps: JA/JB are the open extensions, IA/IB the
  closed direct images. Their adjunctions to the fixed module inverse images,
  oa/ob and ca/cb, specify those functors. `calA` and `calB` package ALL the
  conclusions of `exactOpenClosedUnboundedCalculus`: its derived adjunctions,
  four exact component formulas on complexes, invertible open unit and closed
  counit, both mixed restrictions zero, joint reflection of isomorphisms, the
  supported-unit assertion, and bijectivity on Hom sets between closed-image
  objects. Triangle identities belong to the Adjunction structures. No arbitrary
  adjunction is substituted for the actual localized one.
- Specified scalar comparisons: the expressions are literally `θ_h iA iB hi ...`
  and `θ_h jA jB hj ...` from the recorded normalization module. `thetaI` and
  `thetaJ` retain their isomorphism conclusions, needed for the inverse and the
  support argument. No freely chosen comparison or isomorphism replaces them.
  These are the existing inverse scalar-adjunction mates of the canonical
  action identification `aD_h`; that identification is fixed on underlying maps.

Each conclusion:

- Natural B_X-linear map: `closedScalarMap calA.closedAdjunction
  calB.closedAdjunction mX.T mZ.T (asIso (θ_h ...))` is a natural transformation
  `IA.mapDerivedCategory ⋙ mX.T ⟶ mZ.T ⋙ IB.mapDerivedCategory`. Every arrow is
  in the derived category of B-module sheaves, so the new coefficient action is
  retained. Its real construction uses `Adjunction.whiskerRight` and `homEquiv`.
- Invertibility: the first conjunct is `IsIso` of this natural transformation,
  equivalently invertibility of all its components.
- For every M: the remaining clauses quantify over
  `M : DerivedCategory (Modules AZ)`. H is written out as
  `mX.T.obj (IA.mapDerivedCategory.obj M)`; no opaque let binder is used.
- Exact displayed formula: the component equals the B closed unit at H,
  followed by `IB.mapDerivedCategory.map (inv (θ_h ...).app ...)`, followed by
  `IB.mapDerivedCategory.map (mZ.T.map (...counit.app M))`. Lean's `≫` writes
  the source's right-to-left composition in application order.
- Zero open restriction: both open-restricted objects satisfy `IsZero`, and
  the open image of the displayed map equals the zero morphism. The object
  clauses spell out the supportedness used in the node's proof, not a bound.
- Precise normalization: `iB.mapDerivedCategory.map delta ≫ epsilon_B =
  inv theta_i ≫ mZ.T.map epsilon_A` is the exact source equation, without an
  additional comparison or a forgotten coefficient action.
- Uniqueness: every morphism f with the same source and target satisfying that
  exact normalization equals the displayed component. This is uniqueness among
  all B-linear derived morphisms, not merely among isomorphisms or natural maps.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`,
  available through the recorded FiniteType module (no finite-type hypothesis added).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSiteModel`,
  `proEtaleModelTopology`, `proEtaleModelBaseChange` and its continuous instance.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`:
  `CategoryTheory.exactOpenClosedUnboundedCalculus`, whose complete conclusion
  is packaged without adding or deleting a clause.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`: `ScalarPullback.Modules`,
  `InverseImage`, `inverseModules`, `inverseRing`, `restriction`,
  `AdjunctionNormalized`, `θ_h`, and `kflat_scalar_comparison_normalization`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the normalization
  module imports this recorded dependency and its representative interface.

Edge cases checked before writing and again on reading the statement: M = 0;
Z empty (all supported objects zero); U empty (closed unit everywhere invertible);
X empty; zero ring; identity coefficient change; nonflat Z/l² -> F_l. No
nonemptiness, boundedness, constructibility, torsion, flatness, or finite ring
hypothesis excludes any of these. The inverses have the required direction:
θ_i goes T_Z i_A^* -> i_B^* T_X, so its inverse maps Q_B H -> T_Z Q_A I_A M.
Both sides of the normalization have source Q_B H and target T_Z M.
The left triangle gives normalization; the right triangle gives uniqueness.

Searches actually run with msearch.py (NF, this item):

- leanfinder: “Derived extension of scalars commutes with closed immersion
  pushforward via the supported unit inverse pullback scalar comparison and counit”.
  Eight hits, including ordinary scheme-module pullback/restriction adjunctions and
  their units. None states the unbounded arbitrary-ring-sheaf supported comparison.
- loogle: `CategoryTheory.Adjunction.unit, CategoryTheory.Adjunction.counit`.
  Twelve hits on adjunction triangle identities and adjunction equivalences. These
  supply the abstract calculations, not this comparison theorem.
- leansearch: “Closed immersion scalar extension comparison is the unique morphism
  normalized by inverse image and counit”. Eight hits on ordinary closed-immersion
  scheme facts. None matches the derived coefficient statement.
- grep: `closed.*(scalar|coefficient)|supported.*unit|extensionByZero`, restricted
  to Mathlib/Algebra/Category/ModuleCat/Sheaf: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for supported scalar/closed coefficient
  comparisons found the different closed tensor projection and existing scalar-six
  pullback modules, not this full formula with normalization and uniqueness.
  The required item-id search in WeilConjectures returned no match. A further
  exact-name search in both source roots, Mathlib, and dag/lean_names_upstream.json
  found no `ClosedScalarCalculus`, `closedScalarMap`, or
  `closed_supported_scalar_comparison` collision.

No STATEMENT-DISPUTED finding or source correction. The source read is the current
main-20261015 det-prop-scalar-six-pullback.proof.md, especially (1)--(2), together
with the four explicit current DAG proof steps. The module's theorem docstring
carries all four proof steps and names the three supporting dependencies.

## Second reading by NF

The dispatcher requires this worker to work alone and forbids starting agents.
This is a separate rereading by the same worker, not a claimed independent review;
the maintainer's independent review remains the next review stage.

I reopened the node and checked every hypothesis and clause against the final file.
The complement equation has open image equal to closed image complement; only j
has the quasi-compact instance. The AsSmall site retains the actual pro-etale
site through the existing equivalence and avoids imposing equality on its two
original universes. The ring-map equations are in the correct directions, and the
canonical action mate is the recorded θ_h, not a variable isomorphism. All six
module categories are the ordinary unbounded localizations. The calculus helper
matches all groups of conclusions of its recorded dependency, including
the four actual unit/counit equations and essential-image Hom bijectivity.
The coefficient-adjunction normalization is retained in all three locations.
The natural-map transpose originally used the inverse Hom equivalence in the
wrong direction; the compiler diagnosed that, and the definition now uses
homEquiv in the forward direction, giving exactly unit followed by closed image
of inverse theta and old counit. The final statement includes the component
formula, invertibility, both zero objects and zero open map, exact normalization,
and uniqueness among every morphism. I explicitly named and included both
comparison-isomorphism instances to retain the open comparison assumption in the
elaborated theorem. All universes and variables are bound, and all lines meet
100 columns. No mathematical mismatch or correction remains after this reading.

Validation: the final module passed scompile.py in both the isolated sandbox
(52.3 seconds) and its real library module path (45.1 seconds), with no errors or
warnings. Every theorem in this delivery has exactly `by sorry`; the sole theorem
is the item itself. Both helper definitions contain real data.
