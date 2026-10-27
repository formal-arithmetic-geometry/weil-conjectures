## Worker report

Delivered module: `Sheaf.Algebra.Homology.InjectiveHomDoubleCohomology`.
Main declaration: `HomologicalComplex₂.exists_injectiveHom_double_cohomology`.
The declaration has one postponed proof, with the complete seven-step node proof in its
docstring. It constructs the specified bicomplex and states the two canonical linear
cohomology comparisons. No definitions, new nodes, dependency repairs, or statement
corrections are needed. The node copy changes only `lean`.

Source read: `literature/stacks-project/injectives.tex`,
`remark-spectral-sequences-ext-variant` (Tag 0G20), including the source-cohomology
Ext page and bounded-above source specialization. The node's explicit dual calculation
is the expanded module proof recorded in its seven proof steps; its endpoint argument
and the Ext comparison use Tags 0135 and 06XR, as recorded there.

Hypotheses and clauses, in statement order:

- A commutative ring is `(A : Type u) [CommRing A]`. Modules have independent
  universe `v`; `[HasExt.{w} (ModuleCat.{v} A)]` specifies the size model of the
  recorded derived Ext. This is not an extra algebraic finiteness hypothesis:
  `HasExt.standard` always provides a model. In particular there is no
  `Small.{v} A` restriction, and no equation between `u`, `v` and `w`.
- The integer-indexed source is `M : CochainComplex (ModuleCat.{v} A) ℤ`.
  The integer upper bound is `u₀`; `hM : ∀ a, u₀ < a → IsZero (M.X a)` says
  exactly that its terms above the bound vanish. The letter differs to avoid
  confusion with universe `u`.
- The target and any chosen resolution are `N : ModuleCat.{v} A` and
  `I : InjectiveResolution N`. Its `cocomplex` has natural indices, injective
  terms, and the quasi-isomorphism `ι` from `N` in degree zero. This is the
  node's nonnegative resolution, equivalently its integer extension by zero.
- The conclusion constructs `D : HomologicalComplex₂ ... (up ℕ) (up ℕ)`.
  Natural indices are the first quadrant; extension by zero gives precisely
  the node's zero terms outside it. The component isomorphisms `e i b`
  identify `(D.X i).X b` with the module of maps
  `M.X (u₀ - (b : ℤ)) ⟶ I.cocomplex.X i`. These charts do not leave an
  arbitrary double-complex differential: the next two equations specify both.
- The first conjunct is exactly postcomposition by `I.cocomplex.d i (i+1)`.
  The second is precomposition by
  `M.d (u₀ - ↑(b+1)) (u₀ - ↑b)`, multiplied by
  `((b : ℤ) - u₀ + 1).negOnePow`, the integer sign `(-1)^(b-u+1)`.
  `HomologicalComplex₂` means a complex of complexes, so its horizontal
  morphisms commute with the vertical differential, rather than anticommute.
  The shape laws supply all nonsuccessor zero differentials.
- The family `r i b` is an isomorphism in `ModuleCat A`, hence A-linear,
  from vertical cohomology to `Hom_A(H^(u-b)(M), I^i)`.
  The third conjunct states restriction and descent pointwise: for a vertical
  cycle `z` and a source cycle `x`, applying `r` to the class of `z`, then
  evaluating at the class of `x`, equals the representative map evaluated at
  the inclusion of `x` into `M`. This determines `r` uniquely because the
  homology class maps are surjective. It is not a bare existence of an iso.
- The fourth conjunct says the `r i b` commute with the horizontal maps
  `HomologicalComplex.homologyMap (D.d i (i+1)) b` and postcomposition by
  `d_I^i`. Thus it is the comparison of horizontal complexes described by
  the node, with exactly the induced differential on vertical cohomology.
- The family `t b i` is an A-linear equivalence from the i-th homology of
  `((homologyFunctor ... b).mapHomologicalComplex (up ℕ)).obj D`
  to `Abelian.Ext (M.homology (u₀ - ↑b)) N i`. The functor expression is
  Mathlib's existing complex `H_II^b(D)`; its differential is induced by
  `D.d`, not an independently supplied map.
- The fifth conjunct fixes the induced map on each horizontal cycle `z`:
  if its representative after `r i b` is the cocycle `h`, then `t` sends its
  class to `I.extMk h (i+1) rfl hh`. The local `hh` is exactly the cocycle
  equation; it is a universally quantified argument of this characterization,
  not an additional hypothesis on M, N, or the resolution. Naturality and the
  horizontal cycle equation imply it. `extMk` is the recorded Ext/resolution
  comparison's canonical cocycle class; `extMk_hom` identifies it with the
  derived morphism obtained by inverting the shifted augmentation.
- The last conjunct identifies `t(c • x)` with postcomposition of `t x` by
  `Ext.mk₀ (c • 𝟙 N)`. Mathlib's Ext module structure is exactly this action,
  as `Abelian.Ext.smul_eq_comp_mk₀` states. On D and its homology the action
  is ordinary A-module scalar multiplication; linearity of the charts and
  of `r` makes it postcomposition by the scalar on each `I^i`, i.e. the
  chain endomorphism `c id_I`. The docstring records its augmentation square.
- The quantifiers are all natural `i,b`, including zero; there is no finite
  injective dimension, Noetherian, finite-generation, or bounded-length
  assumption anywhere in the signature.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the source complex is the
  existing `CochainComplex`, and Ext uses this localization.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and
  `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. Its fields are
  `cocomplex`, degreewise `injective`, `ι`, and `quasiIso`.
- `def-sp-double-complex-total`: import the recorded
  `WeilConjectures.CategoryTheory.DoubleComplexTotal`. Use the recorded
  Mathlib declarations `HomologicalComplex₂`, `HomologicalComplex.homology`,
  `homologyFunctor`, `homologyMap`, and `Functor.mapHomologicalComplex`.
  Total filtrations are not part of this item's conclusion.
- `def-weil-derived-category-cohomology-functor`: its `mathlib_match` is
  `DerivedCategory.homologyFunctor`, with `homologyFunctorFactors` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
  At the complex level, use `HomologicalComplex.homology`, `cycles`,
  `iCycles`, and `homologyπ`. The concrete kernel/image identification is
  `ShortComplex.moduleCatHomologyIso` in
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` (proof import).
- `def-pc-ext`: `CategoryTheory.Abelian.Ext` in
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`; its A-module action
  and derived linear comparison are in `...Ext.Linear`.
- Proof dependency `lem-weil-pbc-ext-via-injective-resolution` is Mathlib:
  `InjectiveResolution.extAddEquivCohomologyClass` and `extMk`, with
  `extMk_hom`, in `Mathlib.CategoryTheory.Abelian.Injective.Ext`.
  This import is public because `extMk` specifies the cocycle formula in
  the statement itself. All recorded statement-dependency modules are imported.

Edge cases checked before writing: `b=0` has no incoming vertical boundary;
`M^(u+1)=0` makes every source element a cycle there, so the restriction
comparison is still injective. At `i=0` there is no incoming horizontal
boundary and `extMk` gives ordinary Hom via the augmentation. Zero source,
zero target, and the zero ring give the expected zero modules. For a source
in a single degree, the calculation is exactly the corresponding Ext of that
module. For an exact two-term identity complex both vertical and iterated
cohomology vanish. Negative upper bounds are allowed: all source degrees and
sign exponents use integers, never truncated natural subtraction. In
characteristic two the sign is still a unit (and becomes the identity).
An unbounded injective resolution is allowed; no direct-sum convergence or
finite-total assumption is used in this calculation.

Searches (2026-10-24, prescribed msearch wrapper; raw output in searches.jsonl):

- LeanFinder: `Cohomology of a Hom double complex into injective resolution
  identifies with Hom of cohomology and Ext`. Eight hits, principally
  `InjectiveResolution.extEquivCohomologyClass`, its additive equivalence,
  `extMk`, and their cocycle formulas. These handle a single source module,
  not the vertical dual cohomology of an arbitrary source complex.
- Loogle: `CategoryTheory.Injective, HomologicalComplex.homologyFunctor`.
  Zero hits.
- Mathlib grep: `extEquivCohomologyClass|homology.*[Hh]om|[Hh]om.*homology`
  in `CategoryTheory/Abelian/Injective`. Six hits in Ext.lean and
  Resolution.lean; no full result.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `injective.hom|injectiveHom|HomDouble|homDouble|hom_double|sourceHyper|SourceHyper`.
  Read `Sheaf.Algebra.Homology.SourceHyperExtModuleTarget`: it states the
  downstream spectral sequence, not this canonical double-cohomology result.
  Other hits concerned unrelated injective maps, scalar Hom identities,
  or derived adjunctions. The exact node ID had no upstream Lean hit.
- `rg` of Mathlib, project homology modules and the upstream name index for
  the final declaration name found no collision. Existing first-quadrant
  spectral-sequence modules use the same `homologyFunctor.mapHomologicalComplex`
  expression for iterated homology; it is reused directly, with no wrapper
  definition or private copy.

No statement dispute or node fault was found. The supplied source agrees with
the node and the explicit endpoint proof. Compilation uses only scompile.py.

## Second reading by Q43

A separate pass by the dispatched worker compared the node and the full Lean
signature clause by clause. The prompt prohibits starting another agent and
assigns independent review to the maintainer; this is a self-check, not a claim
of independent review. The component charts specify the same Hom modules,
with exactly the negative source-degree progression and the sign b-u+1.
The two differential equations determine the displayed double complex, whose
commutation is part of the existing Mathlib type. The restriction equation
contains both cycle inclusion and quotient descent, fixing the first iso;
the naturality equation uses d_I-induced homology maps. The `extMk` equation
fixes the second iso on every cycle and therefore on the quotient, including
zero degree. The final scalar equation uses the target scalar endomorphism,
not a separate unspecified Ext action. No extra hypotheses were found.
Compiler feedback led to explicit public visibility of the ModuleCat and
`extMk` interfaces and corrected multiline field syntax. No mathematical
clause or node statement changed. All universes and binders are explicit;
there are no local notations, private definitions, `let` binders, or hidden
proof holes in data.
