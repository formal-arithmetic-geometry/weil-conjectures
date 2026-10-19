## Worker report

The delivery states `AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow`
and `AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow_padicAlgCl` in
`Sheaf.Paper.ProperIndConstructibleBoundedBelow`. Both proofs are `sorry`; no theorem
is proved and no definition or instance is introduced. Each theorem's docstring gives
all five proof steps of the DAG, including the module-category identification, the
bounded-below representative, finite abutment filtration, kernel/cokernel recursion,
finite stabilization, extension descent, and both support arguments.

The source was read at main-20261015, sec-six-functors-basics,
`sk-lem-proper-unbounded-window/sk-lem-proper-unbounded-window-bounded-below.md`,
its `.proof.md`, the parent's `_section.md`, and the proper-heart source. The recorded
proper-heart statement explicitly invokes `sk-def-sfb-dc-setting`; that setting's
blueprint source was also read. See the correction and complete citer audit below.

Hypothesis and conclusion correspondence, for each theorem:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite coefficient case takes
  `E : PadicAlgCl.FiniteIntermediateField ℓ` and uses
  `Profinite.continuousMapRingObj E`. The second theorem uses
  `Profinite.padicAlgClRingObj ℓ` and has no unused finite-subextension parameter.
  This latter ring has finite-subextension-valued continuous sections; it is not
  the full continuous-function ring of the topological algebraic closure.
- The source-inherited field setting is `(k : Type u) [Field k]`,
  `(p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)`.
  Both schemes have `Over (Spec (.of k))`, and their structure morphisms have
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`, namely separated finite
  type. `[p.IsOver (Spec (.of k))]` makes `p` a morphism over that field.
  `[IsProper p]` is precisely properness.
- `(d : ℤ)` has no nonnegativity assumption. For each `y : Y`, `hd` bounds the
  topological Krull dimension of the pullback along
  `Spec.map (algebraMap κ(y) (AlgebraicClosure κ(y))) ≫ Y.fromSpecResidueField y`.
  This is the geometric fibre specified by the existing node. Since Mathlib's
  dimension is in `WithBot ℕ∞`, the integer bound is represented by
  `if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥`. This is an exact translation:
  nonempty spaces have nonnegative dimension; negative bounds permit exactly empty
  fibres. No replacement by the weaker bound `d.toNat` is made.
- `K : DerivedCategory (pulledBackModuleObjects Λ X)` is the actual unbounded
  derived category of internal modules over `condensedRingObj Λ X`, the pulled-back
  condensed coefficient ring. There is no input functor or abstract substitute.
- `hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
  (IsConstantModelConstructible Λ X) ((DerivedCategory.homologyFunctor _ n).obj K)`
  is membership in Dic: every cohomology sheaf is a small filtered colimit of
  finite constant-model constructible sheaves in the ambient module category.
  Mathlib `ObjectProperty.ind` already includes arbitrary colimit presentations and
  isomorphism closure. This is the same expression used by the existing IndCons
  and ambient-derived modules; there is no new IndCons or Dic definition.
- `hbelow : ∃ a₀ : ℤ, K.IsGE a₀` says bounded below, with no upper bound required.
  `DerivedCategory.isGE_iff` identifies it with vanishing cohomology below a₀.
- The first conjunct quantifies over every `n : ℤ` and asserts the identical
  IndCons predicate on `Hⁿ` of
  `(CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K` over Y.
- The second conjunct quantifies over every `a : ℤ` and sends `K.IsGE a` to
  `((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K).IsGE a`.
- The third conjunct quantifies over every `b : ℤ` and sends `K.IsLE b` to the
  same direct image being `IsLE (b + 2 * d + 1)`. The additional degree is retained.
  Mathlib `isLE_iff` identifies this with precisely the upper cohomology vanishing.

Dependencies used, with declarations read in their source:

- `sk-def-sfb-condensed-ring`: the recorded universe-general interface in
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` was inspected. For the
  canonical finite intermediate fields (whose carriers are in Type 0), use its
  exact closed audited upstream specialization `Profinite.continuousMapRingObj`
  from `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`,
  publicly exported by `...Condensed.FiniteSubextension`. Its sections and ring
  structure are the specified continuous maps with pointwise operations.
- `sk-def-sfb-qlbar-condensed`: its closed upstream audit, rather than a missing
  lean record, supplies `Profinite.padicAlgClCondensedRing` and
  `Profinite.padicAlgClRingObj` in `...Condensed.EllAdic`; the finite-subextension
  source and the full signatures/docstrings were read.
- `sk-def-sfb-pulled-back-coefficients`: `coefficientRing` and `condensedRingObj`
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `sk-def-sfb-module-objects`: `pulledBackModuleObjects` in
  `Sheaf.Paper.ModuleObjects`, definitionally the actual `CategoryTheory.Mod` over
  that pulled-back ring. This recorded declaration is used in the K binder.
- `sk-def-sfb-constructible`: `IsConstantModelConstructible` in
  `Sheaf.Paper.CondensedConstantConstructibility`. Its finite scalar presentations
  are chosen on the point before pullback; arbitrary coefficient-function matrices
  are not substituted. The qcqs/affine-local branches were read.
- `sk-def-sfb-derived-categories`: the existing `DerivedCategory` and standard
  cohomology/t-structure conventions, as its lean note specifies. The more general
  `rightDerivedFunctorOfQuasiIsoResolutions` interface was read; here the actual
  module categories have the published K-injective instance, and the recorded
  module-derived-pushpull convention explicitly uses `Functor.rightDerivedFunctor`.
- `def-sfb-module-lower-star`: `CondensedRing.lowerStar` in
  `...ModuleObject.UpperLowerStar.Defs`, the mapMod/comap composite, together with
  its underlying-sheaf/action and additive/finite-limit declarations.
- `sk-def-sfb-module-derived-pushpull`: `Functor.rightDerivedFunctor`, from
  `...CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`, specialized exactly
  as in `...ModuleObject.Derived.UpperLowerStar`. It derives the entire lowerStar
  composite in the module category on unbounded complexes.
- `def-weil-derived-cohomology-sheaves`: its retained exact `mathlib_match`,
  `DerivedCategory.homologyFunctor` in Mathlib's DerivedCategory.HomologySequence,
  applies to this abelian module category. The later specialized
  `Scheme.pbcQbarCohomology` primary binding is not the ambient cohomology functor
  needed here; the record expressly retains the ambient match. No duplicate or
  repair is needed.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from Mathlib's
  AlgebraicGeometry.Morphisms.Proper. Universal closedness supplies quasi-compactness
  so its locally-finite-type formulation agrees with finite type.
- The added existing dependencies give the standing scheme setting, the geometric
  fibre as Mathlib `pullback`, and Mathlib `topologicalKrullDim`. The setting is
  explicit binders, as its recorded note instructs; the compactification choice in
  its primary module is not needed in this theorem's signature.

The available proof-dependency modules are imported without `public`: upstream
ExactCouple, TruncationHypercohomology, RingedSiteGrothendieckAbelian, and the landed
IndHeartKernelsCokernels and IndConstructibleExtensions. The proper-heart theorem
has no recorded Lean statement, so its proof-only module cannot yet be imported.
It is retained in the proof plan and DAG, and is not assumed as a binder. Its proof
is not needed to state this node. No import cycle was introduced.

Edge cases checked before writing and again against the compiled signature:
zero K, empty X and/or Y, d=0 (the upper bound is b+1), negative d (only empty
fibres, without truncating the amplitude shift), arbitrary negative a and b,
b<a, and a bounded-below K having no upper bound. No dimension bound is assumed
on X or Y themselves. The site is the existing small pro-etale site; its distinct
object/morphism universes and the coefficient universe u+1 are preserved. Filtered
indices use u+1 exactly as the other existing IndCons modules. Every declaration
has all variables and universes bound, and `autoImplicit` is disabled.

Searches for existing statements:

- msearch.py leanfinder, query: “Proper direct image of bounded below ind
  constructible complexes preserves cohomology and has amplitude at most twice
  fibre dimension plus one”. Eight hits: generic DerivedCategory IsGE, IsLE,
  representative and shift results; no matching proper IndCons theorem.
- msearch.py loogle, query: `"rightDerivedFunctor"`. Twelve generic
  HasRightDerivedFunctor/totalRightDerived/universal-property hits; none states
  this proper geometric amplitude and preservation result.
- msearch.py leansearch, query: “proper direct image bounded below ind
  constructible cohomology amplitude”. Generic properness and cohomological
  boundedness hits; no matching statement.
- msearch.py grep, pattern:
  `proper.*[Bb]ounded[Bb]elow|indConstructible.*[Pp]roper|geometric.*[Ff]ib.*[Dd]im`.
  Zero Mathlib hits.
- Direct rg of `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id, proposed theorem name, proper bounded-below and indConstructible
  proper patterns found no existing declaration. Searches of IndCons and
  indConstructible found the canonical expression `ObjectProperty.ind` in
  IndConstructibleFilteredColimits, IndConstructibleExtensions and
  AmbientIndDerivedTriangulated; those files were read and this delivery reuses
  that notion without defining a replacement.
- Mathlib source search found `ObjectProperty.ind`, `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`, `homologyFunctor`, `pullback`, `AlgebraicClosure` and
  `topologicalKrullDim`; their definitions and relevant signatures were read.
  The current TruncationHypercohomology source was also read through
  `scompile.py --source` because it is absent in the older local source checkout.

Validation: prescribed scompile.py compiles the sandbox and actual delivered
module separately. The first pass type-checked with four line-width warnings;
these were repaired without changing mathematical content. The final clean compile
and the delivery dry-run results are recorded below when completed.

## Statement corrected

The original statement is preserved verbatim in `statement_change.old_statement`.
It starts “Let Λ=E or Qlb, p:X→Y proper with geometric fibres of dimension ≤ d,
and K in Dic(X,Λ) bounded below” and has the three conclusions represented above.
The correction prepends the standing field/scheme setting and the existing
coefficient, module, derived, IndCons/Dic and dimension conventions; all original
conclusions and integer quantifiers are preserved.

What required correction: the proper-heart result used in the first paragraph of
the source proof is explicitly stated in the standing separated finite-type
positive-characteristic field setting. The item's terse statement left that setting
out. Stating it for arbitrary schemes would demand the stronger generality absent
from its cited input. The correction follows this source use, not a restriction
chosen to make Lean elaborate. No blueprint unit statement is edited.

The audit used rg on the item id and then parsed every node's stmt_deps/proof_deps;
there are exactly two citers:

- `det-proper-unbounded-window-arbitrary`: holds true. Its opening explicitly takes
  Λ,p,d as in this item, thereby inheriting its setting; the uses on truncations and
  single-cohomology complexes still apply.
- `sk-lem-proper-unbounded-window`: holds false for its current expanded DAG
  statement's unrestricted “Let X,Y be schemes”. The source unit takes p,d as in
  the proper-heart result, but that inherited setting was lost in its expanded
  DAG statement. Its bounded-below applications require the same context to be
  made explicit when that node is handled. This breaking citer is named and not
  edited in this delivery.

Only the item's statement, lean, stmt_deps and statement_change are changed.
stmt_deps gains the existing owners sk-def-sfb-dc-setting, def-weil-geometric-fibre,
and def-kun-topological-krull-dimension, all named in the corrected statement.
Its previous stmt_deps is recorded verbatim. Its proof and proof_deps are unchanged.
There are no new definition nodes and no dependency modules.

Final file verification: scompile.py completed successfully and emitted no Lean
warnings or errors. The sandbox probe took 5.3 seconds and the actual module took
8.9 seconds, each below the unchanged 60-second limit. Both postponed declarations
are listed in lean.declarations; the primary signature is copied verbatim from the
actual module. No other Lean file is present in the delivery.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
