## Worker report

The module `Sheaf.Paper.FiniteRingCompactSupportProjection` states
`AlgebraicGeometry.Scheme.isIso_finiteRingCompactSupportProjection` with `sorry`.
The only other declaration is the real construction
`AlgebraicGeometry.Scheme.finiteRingCompactSupportProjection`: the prescribed
compactification projection natural transformation transported to the recorded
intrinsic constant-ring presentation. The node changes only in `lean`. Its reviewed
six-step split, statement, dependencies and source remain unchanged.

### Hypotheses and clauses

- Global finite-field datum: `(D : WeilConjectures.FiniteFieldDatum.{u})` supplies
  the actual finite base field, its cardinality, and its fixed algebraic closure
  `D.k`. `(l : ℕ) (_hl : l.Prime) (_hlp : l ≠ D.p)` renders precisely the prime
  different from the characteristic; the finite-field cardinality in `D` fixes that
  characteristic as `D.p`.
- Arbitrary finite commutative coefficient ring: `(R : Type u) [CommRing R]
  [Finite R]`. The bound `(n : ℕ) (_hn : 1 ≤ n)` and
  `(_hR : ∀ r : R, (l ^ n) • r = 0)` say `l^n R = 0` via additive natural-number
  multiplication. There is no flatness, presentation, valuation ring, nonzero-ring,
  perfectness or finite-Tor assumption.
- The three schemes are `X`, `c.Z` and `Y`. Each has the actual instance
  `.Over (Spec (.of D.k))`. For each of their structure morphisms, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` render separated and finite type.
  Finite type means locally of finite type plus quasi-compact, exactly the
  project's convention.
- `(f : X ⟶ Y) (c : Compactification f)` packages precisely the named maps
  `j := c.i`, `p := c.g`, and the intermediate scheme `Xbar := c.Z`.
  `c.isOpenImmersion` and `c.isProper` are fields of this existing structure,
  not extra hypotheses or a theorem asserting an unchosen compactification.
  `c.comm : f = c.i ≫ c.g` expresses the node's definition of `f`.
  `[c.i.IsOver (Spec (.of D.k))]` and `[c.g.IsOver (Spec (.of D.k))]` say both
  maps are the required k-morphisms. No extra condition on `f` is imposed.
- `(M : proEtaleDerivedCategory X R)` and
  `(K : proEtaleDerivedCategory Y R)` are the ordinary localization of unbounded
  integer cochain complexes of module sheaves over the recorded constant ring.
  They are intrinsic ringed-site modules, not completed, solid, rational,
  constructible-only, bounded-below, or finite-Tor categories.
- `_hMc` and `_hKc` apply the existing
  `IsConstructibleProEtaleModuleSheaf` to every cohomology sheaf, computed by
  `DerivedCategory.homologyFunctor` in the very same intrinsic module category.
  This predicate is re-exported by the recorded
  `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`. Its full definition was
  read: positive finite stratification by locally closed constructible immersed
  subschemes, canonical coefficient pullback, locally constant restrictions and
  finite geometric stalks. No etale-origin witness replaces this hypothesis.
- `_hMb` and `_hKb` independently assert `∃ a b : ℤ, a ≤ b ∧ ...` with `IsZero`
  of cohomology for `i < a ∨ b < i`. This is exactly finite cohomological range,
  with no requirement that the two complexes have the same bounds and no bound
  on the derived tensor product.
- The conclusion is
  `IsIso (((finiteRingCompactSupportProjection R c).app M).app K)` in the
  intrinsic derived category on `Y`.

### The canonical map and naturality

`ProEtale.projectionMapOfCompactification` already constructs exactly the map in
this node. Its definition and component formula were read, including the current
published source obtained with `scompile.py --source` for
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`.
It is the following composite, with all operations ordinary and unbounded:

1. `rightDerivedLowerStarProjectionMap` for `c.g`, evaluated at `j_! M,K`.
   Its definition is `Adjunction.rightAdjointProjectionMap` for the specified
   derived pullback/pushforward adjunction and the canonical pullback/tensor
   comparison. Its component formula is the adjoint of counit tensor identity.
2. The pushforward of the inverse component of
   `derivedOpenImmersionLowerShriekProjectionIso` for `c.i`. The inverse has
   exactly the direction displayed in the node, from tensoring `j_! M` to
   extending the tensor on the open.
3. The pushforward/extension/tensor image of
   `leftDerivedUpperStarCompactificationIso`, the inverse of the derived
   pullback composition isomorphism transported along `c.comm`.

`finiteRingCompactSupportProjection` does not choose an isomorphism between these
objects. It precomposes that actual natural transformation in its two arguments
with the inverse derived coefficient realizations and postcomposes with the
forward derived coefficient realization on `Y`. The Lean implementation is
`Functor.whiskeringLeft₂` followed by `Functor.postcompose₂`, applied on maps.
Thus its type is a natural transformation of bifunctors on the intrinsic derived
categories; naturality in BOTH arguments is part of the construction's type.
The theorem states invertibility of its specified components.

The realization is `sfIntrinsicModuleEquivalence T R`, the equivalence supplied
by the dependency module `ProEtaleIntrinsicExtensionByZero`. Its forward functor
is the published `finiteCoefficientIntrinsicRealization`: keep the fixed-scalar
module presheaf and sheafify along the canonical constant-scalar unit. Its inverse
is the inverse of that equivalence, not a freely selected equivalence. Deriving
these exact functors gives the same presentation change on unbounded categories.
This is the same transport already used by the recorded intrinsic open extension
and finite-coefficient pullback. It preserves the constant scalar action, tensor,
adjunction units/counits, and extension by zero; on flat K-flat representatives
both tensor presentations are the total sheaf tensor with that scalar action.
Consequently the transported map is precisely the displayed intrinsic projection
map under these canonical identifications. No new module category or tensor notion
is defined, and no optional coefficient identification is a theorem hypothesis.

### Dependency declarations

All recorded statement-dependency modules with a module are public imports:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated` and
  `UniversallyClosed`. Properness includes quasi-compactness through universally
  closed morphisms. The collection node `def-weil-scheme-morphism-properties` is
  a convention with no independent declaration, as its record explicitly says.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: ordinary finite coefficient
  module/derived presentations. Its canonical intrinsic realization is retained
  through `ProEtaleFiniteModuleIntrinsicComparison`, imported by the intrinsic
  extension module; `proEtaleDerivedCategory`, `proEtaleConstantRing` and
  `proEtaleRingModules` are the existing underlying intrinsic definitions.
- `Sheaf.SixFunctors.IntrinsicDerivedTensor`: `proEtaleDerivedTensor`, the
  recorded K-flat total tensor construction; the map uses its functorial
  fixed-scalar K-flat presentation through the canonical realization above.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingDerivedPullback`, constant-section comparison, ordinary
  module adjunction, and re-exported finite realization operations.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicModuleEquivalence` and `sfIntrinsicExtensionByZero`.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`: the re-exported
  `IsConstructibleProEtaleModuleSheaf` in the coefficient universe used here.

The natural transformation uses the published finite-coefficient modules
`Derived.LowerShriekProjection` and `UpperLowerStar.FlatModuleCat` directly.
The still-open proof has the six-step natural-language proof in its docstring.
Every stated proof-dependency module is imported, without `public`: finite-ring
derived origin; etale extension exactness; pro-etale extension exactness and
comparison; support-site comparison pullback coherence; the independent-universe
canonical tensor-pullback theorem; proper torsion projection; the etale projection
map; ringed exchange/tensor coherence; and the unbounded open projection formula.
`lem-sfb-unbounded-direct-image-comparison` has no recorded Lean declaration yet,
so there is no module to import for that proof-only dependency. It remains named
in proof step 4; its absence does not alter or prevent this statement.

### Edge cases

Checked before writing: the zero coefficient ring is allowed and satisfies the
annihilation condition; `n = 1` is allowed; zero complexes satisfy any nonempty
bounding interval; arbitrary positive, zero or negative cohomological degrees are
allowed; the two bounding intervals are independent; empty schemes and the empty
open immersion are admitted by the existing definitions (the positive-number-of-
strata convention permits an empty stratum); identity open/proper factors are
allowed. The tensor is permitted to be unbounded below, in particular for finite
nonregular or nonflat coefficient rings. No proof uses geometric stalk
conservativity on arbitrary pro-etale sheaves. The small-site encoding retains
its actual object universe `u+1` and morphism universe `u`; neither is identified
with the other. Finite coefficients are lifted to `ULift.{u+1,u} R` only inside the
fixed-scalar presentation, and are brought back by the recorded realization.

### Searches and validation

- `msearch.py leanfinder`, query: "Canonical compact support projection formula
  for bounded constructible proetale complexes over arbitrary finite commutative
  torsion rings". Eight hits (condensed/profinite constructions and scheme-limit
  section lemmas), none matching this assertion.
- `msearch.py loogle`, query:
  `rightDerivedLowerStarProjectionMap, projectionMap`. No hits; Mathlib does not
  know the project declaration name.
- `msearch.py grep`, query:
  `projectionFormula|projection_formula|rightAdjointProjectionMap`. No hits in
  Mathlib.
- `msearch.py leansearch`, query: "The canonical compact support projection
  morphism is invertible for bounded constructible proetale complexes over
  arbitrary finite commutative primary rings without finite Tor amplitude".
  Eight hits on truncation projections, an invertible module and projective
  resolutions; none match.
- `rg` in upstream `WeilConjectures/SixFunctors/ProEtale` found the exact
  projection construction and its older projection theorems. Read
  `Derived/LowerShriekProjection.lean`, `Derived/LowerStarProjection.lean` and
  `Derived/ProjectionFormula.lean`. The existing finite theorem requires finite
  Tor amplitude; it does not state this node. The source search for this node id
  has no match.
- `rg` in `lean/Sheaf` found `FiniteCompactProjectionFormula`: its rings are the
  specific DVR quotients and its second input has finite Tor amplitude; it is
  not this statement. The intrinsic realization, tensor, operations, open
  extension and constructibility modules were read and reused. No existing
  full theorem was found. Searches in upstream, Mathlib, `lean/Sheaf` and the
  upstream-name index found neither of the two new declaration names.
- Read the blueprint Proof (3) and Stacks
  `etale-cohomology.tex`, `lemma-projection-formula-proper-mod-n` (Tag 0F0G):
  the latter explicitly permits arbitrary torsion rings and unbounded E,K.
- `scompile.py` compiled the natural-transformation version both as sandbox file
  and as library-path file, in 2.6 s and 2.7 s, with no errors or warnings.
  An earlier component-only exploratory version was superseded; the delivered
  version retains naturality in its type and compiles within the standard limit.

No statement correction, new independent notion, dependency replacement, or
STATEMENT-DISPUTED flag is needed. Nothing is proved: the only theorem ends in
`by sorry`; the helper definition has real functorial data.

## Second reading by Q70

Independent maintainer second reading, 2026-10-17, of immutable delivery
0a5debc8e4dc7918210155c48bd4c6532bcd8cea. This reader did not write or
previously second-read the delivery. The original section was only a placeholder;
this replacement records the actual independent reading required by H1/H11.

Read the item JSON, all nine statement-dependency JSON files, the delivered module
and worker report themselves. Read blueprint main-20261015,
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.proof.md,
Proof (3), and Stacks etale-cohomology.tex:20193,
lemma-projection-formula-proper-mod-n (0F0G). The latter explicitly allows a
proper morphism, arbitrary torsion ring, and arbitrary unbounded derived inputs.
The finite-ring, intrinsic-constructibility version here is consistent with that
source and the item's recorded comparison route.

Hypothesis and conclusion audit:

- `FiniteFieldDatum.{u}` supplies the fixed finite base field and algebraic
  closure. `l.Prime`, `l ≠ D.p`, `1 ≤ n`, and
  `∀ r : R, (l ^ n) • r = 0` give precisely the prime and annihilation
  conditions. `[CommRing R] [Finite R]` adds no flatness, DVR presentation,
  nontriviality, finite Tor amplitude, or perfectness hypothesis.
- `X`, `c.Z`, and `Y` each carry their k-structure and exactly separated,
  locally finite type, quasi-compact structure morphisms. The latter two
  properties mean finite type. The actual `Compactification` structure was read
  in WeilConjectures/Compactification/Defs.lean:69: its fields give the open
  immersion `c.i`, proper morphism `c.g`, and `c.comm : f = c.i ≫ c.g`.
  Both factor maps are explicitly over k. Any given factorization in the node
  supplies this structure; no additional compactifiability assumption is made.
- `proEtaleDerivedCategory` is the ordinary localization of integer cochain
  complexes of modules over the constant ring sheaf on `ProEt.topology`.
  `proEtaleRingModules` is that same module category. The definition was read
  in ProEtaleDerivedCategory.lean and ProEtaleOperations.lean; there is no
  completion, condensed replacement, or substitution of the etale category.
- `_hMc` and `_hKc` use the reexported
  `IsConstructibleProEtaleModuleSheaf` from ProEtaleConstructibleSheaf.lean.
  Its body requires a positive finite partition into constructible locally
  closed immersed strata, locally constant restrictions, and finite geometric
  stalks. The site-universe generalization in the recorded dependency module
  reexports this original small-coefficient predicate; using it at `R : Type u`
  is the intended specialization, not a private definition. No etale-origin
  witness replaces intrinsic constructibility.
- `_hMb` and `_hKb` separately give finite cohomological intervals through
  `DerivedCategory.homologyFunctor` and `IsZero`, in the same module category.
  They impose no bound on the tensor product.
- The conclusion is invertibility of the component of the specified natural
  transformation at `M,K`. Naturality in both variables is retained by the
  bifunctor natural-transformation type, rather than being lost in a
  componentwise existence assertion.

Canonical-map audit: read the exact published finite-coefficient modules using
`scompile.py --source` where the local group clone did not contain them:
Derived.LowerShriekProjection, Derived.LowerStarProjection, Derived.Tensor,
Derived.UpperStarMonoidal, and UpperLowerStar.FlatModuleCat, all under
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient. In particular,
`projectionMapOfCompactification_app_app` expands into the proper counit mate,
proper pushforward of the inverse open projection isomorphism, and the
pullback-composition identification along `c.comm`. The proper factor's
`rightDerivedLowerStarProjectionMap_app_app` is exactly the adjunct of the
pullback/tensor comparison followed by counit tensor identity. The tensor is
`curriedTensor` of the K-flat derived monoidal structure, with its total-left-
derived-functor interface; it is not data defined by `sorry`.

Read `sfIntrinsicModuleEquivalence`, `finiteCoefficientIntrinsicRealization`, and
`sfIntrinsicExtensionByZero`. The forward realization sheafifies the existing
fixed-scalar module presheaf along the canonical constant-scalar unit; its inverse
is the inverse of this specific equivalence. This uniquely extends scalar action
to locally constant scalar sections. It identifies ordinary sheaf tensors and
inverse images, hence their derived tensors, and transports adjunctions. The
helper transports the actual published map by precomposition in both variables
and postcomposition on Y. Consequently its source and target are canonical
presentations of the displayed intrinsic operations, and its map is the specified
projection map under those identifications. It chooses no arbitrary map or
projection-formula isomorphism.

Read the recorded interfaces for finite modules, intrinsic K-flat derived tensor,
constant-ring operations, intrinsic extension by zero, and constructibility,
alongside their source blueprint definition files (orders 1233, 663, 1234,
1471, and 1454). Read FiniteFieldFiber and the convention node (orders 411,
410), Mathlib's IsOpenImmersion and IsProper declarations, and the Stacks open
immersion/proper/universally closed definitions (01HE/01IO, 01W1).
UniversallyClosed supplies quasi-compactness, so the Mathlib proper convention
matches the node. The continuous-function finite coefficient presentation and
the intrinsic constant-ring presentation are related by the published canonical
realizations, not duplicated mathematical notions.

The six proof steps are reproduced in the theorem docstring. I also read every
proof-dependency statement: finite-ring constructible origin; exact etale and
pro-etale open extensions and their comparison; comparison pullback; unbounded
ringed tensor pullback; 0F0G and its specified projection map; unbounded
finite-type direct-image comparison; ringed exchange/tensor coherence; and the
unbounded open projection formula. They supply the clauses the six steps use.
In step 4 the unbounded direct-image comparison applies to both E and the
possibly unbounded-below tensor H. This proof-only prerequisite need not have a
Lean declaration to state the present theorem: none of its missing data is used
in the helper or theorem signature. Thus there is no missing statement helper
or universe repair to supply in this delivery.

Edge cases checked: zero ring, n = 1, zero complexes, empty X/c.Z/Y when
compatible with the maps, empty open immersion, identity factors, arbitrary
negative or positive cohomological bounds, different bounds for the inputs,
and derived tensors unbounded below over nonregular finite rings. A single
empty stratum accommodates the empty scheme. n = 0 is correctly excluded by
the source's n ≥ 1. The characteristic prime is correctly excluded. The small
site has object universe u+1 and morphism universe u; ULift raises finite scalar
presentation to u+1 without identifying these universes or imposing a new
mathematical restriction.

Independent duplicate searches used rg in the pinned Mathlib, upstream
WeilConjectures/SixFunctors/ProEtale, and the group clone's lean/Sheaf, with
projectionFormula, projection_formula, projectionMapOfCompactification,
rightAdjointProjectionMap, and the declaration names. The worker's LeanSearch,
LeanFinder and Loogle searches are recorded above. Existing projection maps are
reused. FiniteCompactProjectionFormula.lean uses DVR quotient coefficients and
finite Tor amplitude; the upstream comparison theorem also retains a bounded-
below tensor condition. Neither states the present arbitrary-finite-ring
assertion. The new helper is the necessary intrinsic presentation of the
published map, not a second independent projection construction.

Validation: the node's `lean.statement` is byte-for-byte the theorem signature
from `theorem` to before `:=`; every bound variable/universe is declared and
autoImplicit is false. All lines satisfy the 100-character limit. Both delivered
declarations have source/blueprint docstrings and the theorem has all six proof
steps. There is one real-data definition and one theorem ending in `by sorry`,
with no local proof beyond sorry. Both declarations are in lean.declarations.
No item statement, dependencies, source or dependency record needs correction.

Reproduced the immutable file with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q70
lem-sp-finite-ring-compact-support-projection
snapshot/lean/Sheaf/Paper/FiniteRingCompactSupportProjection.lean`
(the command arguments were on one line). Exit status 0: sandbox
Sheaf/Stage2/Sandbox0.lean 3.1 s; library-path
Sheaf/Paper/FiniteRingCompactSupportProjection.lean 4.3 s; no diagnostics.
The currently installed wrapper explicitly uses server-side persistent side-overlay
compilation and wire confirmation (2026-10-17), superseding its older local
execution description. Only the prescribed wrapper was invoked; no direct ssh,
global build, live Lean edit, Git mutation, or project-clone edit was performed.

Finding and repair: H1/H11 report-only defect. The original heading was followed
by a disclaimer instead of a real second reading. This complete replacement
report preserves the worker report and replaces only that placeholder with the
independent reading above. The mathematical delivery and Lean file are accepted
unchanged. Verdict: FIX.
