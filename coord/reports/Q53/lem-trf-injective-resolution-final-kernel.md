## Worker report

The module `Sheaf.RingTheory.InjectiveResolutionFinalKernel` states
`ModuleCat.injective_kernel_of_ext_ideal_quotient_eq_zero`. Its only theorem has
proof `sorry`, as required for stage 2. No definitions, additional nodes, dependency
repairs, or statement corrections are needed. Only the item's `lean` field changes.

Hypothesis and conclusion correspondence:

- The commutative ring in the common universe is `(R : Type u) [CommRing R]`.
  The module is `N : ModuleCat.{u} R`. The complex's terms also belong to
  `ModuleCat.{u} R`; this retains the common-universe condition of Baer's criterion.
- The given integer-indexed cochain complex is
  `I : CochainComplex (ModuleCat.{u} R) ℤ`; its differentials are `I.d j (j + 1)`.
  The cochain-complex structure includes the square-zero identities.
- The given linear augmentation is `ε : N ⟶ I.X 0`. A morphism of `ModuleCat`
  is an R-linear map, accessed as `ε.hom`.
- `I^j = 0` for negative j is
  `hneg : ∀ j : ℤ, j < 0 → IsZero (I.X j)`. Zero modules are expressed
  invariantly by Mathlib's categorical `IsZero`, allowing every presentation of
  the zero module rather than requiring literal equality of bundled objects.
- Every term is injective: `hinj : ∀ j : ℤ, Injective (I.X j)`.
- Exactness at N in `0 → N → I^0` is `hε : Function.Injective ε.hom`.
- Exactness at `I^0` is `hexact₀ : Function.Exact ε.hom (I.d 0 1).hom`.
- Exactness at every positive degree is
  `hexact : ∀ j : ℤ, 0 < j → Function.Exact
  (I.d (j - 1) j).hom (I.d j (j + 1)).hom`.
  For linear maps, `Function.Exact` says that the image of the first map is the
  kernel of the second (`LinearMap.exact_iff`). Thus these hypotheses express
  exactly the entire augmented exact sequence, for the given augmentation.
- The nonnegative integer is `(d : ℤ) (hd : 0 ≤ d)`, without changing the index set.
- For every ideal T the required Ext vanishing is
  `hExt : ∀ T : Ideal R, Subsingleton
  (Abelian.Ext (ModuleCat.of R (R ⧸ T)) N (d.toNat + 1))`.
  `d.toNat + 1` is precisely d+1 under `hd`; Ext is Mathlib's natural-degree,
  small model of the derived-category morphism group of `def-pc-ext`.
  An Ext group is zero exactly when its underlying type is subsingleton.
- J is the actual canonical `kernel (I.d d (d + 1))`, and the conclusion is
  `Injective (kernel (I.d d (d + 1)))`. The canonical isomorphism
  `ModuleCat.kernelIsoKer` identifies it with the usual linear-map kernel;
  `Module.injective_iff_injective_object` identifies the categorical injectivity
  used in the statement with injectivity of its underlying R-module.

Dependency declarations read and used:

- `def-sp-injective-resolutions`: `CategoryTheory.Injective`, from
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and
  `CategoryTheory.InjectiveResolution`, from
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. The statement uses
  the recorded `Injective` directly and writes out the given integer-indexed
  resolution's properties. It does not replace the given complex by a chosen
  natural-indexed resolution or by an arbitrary quasi-isomorphic object.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, and the integer-indexed `CochainComplex` API of
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, publicly available through
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`. No localization-choice
  binder is needed: this statement only uses the existing Ext model.
- `def-pc-ext`: `CategoryTheory.Abelian.Ext`, from
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`. Its `HasExt.{u}` instance
  on `ModuleCat.{u} R` comes from
  `Mathlib.Algebra.Category.ModuleCat.Ext.HasExt`; it is automatic in the
  common universe and is not an extra assumption.
- Proof dependencies are imported privately: the module-category
  `ModuleCat.enoughInjectives` and abelian/mono facts;
  `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass` and its
  cocycle-boundary API in `Mathlib.CategoryTheory.Abelian.Injective.Ext`;
  `Module.Baer.iff_injective` in `Mathlib.Algebra.Module.Injective`, together
  with its categorical bridge in `Mathlib.Algebra.Category.ModuleCat.Injective`.
  These are the recorded matches for the three proof-only statement nodes.

The theorem's docstring gives the whole node proof: extend an ideal map into
I^d, descend its differential to R/T, use vanishing Ext to subtract a boundary,
corestrict the corrected extension to the kernel, then apply Baer's criterion.
Sources read locally: `more-algebra.tex`, Tag 0A5T, proof of (3) implies (1),
and Tag 0AVF; `derived.tex`, Tag 06XR. The accepted DAG statement is unchanged.

Edge cases checked before writing:

- d=0 gives J isomorphic to N via the injective, exact augmentation; the
  hypothesis is Ext^1(R/T,N)=0, the ordinary Baer test. No positive-bound
  hypothesis excludes this case.
- T=0 tests the projective module R; its positive Ext is zero and adds no
  unintended restriction. T=top gives the zero quotient and trivial Ext.
- The zero module N and the zero ring are allowed. The argument and statement
  require neither nontriviality nor a nonzero resolution term.
- Negative-degree objects can be any zero modules; the hypothesis is not
  equality to an arbitrarily chosen categorical zero object.
- No upper bound, finite generation, Noetherianity, locality, or regularity is
  added to R, N, the ideals, or the complex.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder "The degree d kernel in an injective module
  resolution is injective if Ext d+1 vanishes for every ideal quotient of the
  ring"`: eight hits, including `HasInjectiveDimensionLT.mk`, `mk'`,
  `hasInjectiveDimensionLT_iff`, and degreewise injectivity of extended
  resolutions. None asserts this kernel result from ideal-quotient tests.
- `msearch.py ... loogle "CategoryTheory.InjectiveResolution,
  CategoryTheory.Injective"`: four hits, namely `InjectiveResolution.self`,
  `injective`, `mk`, and `instInjectiveXIntCochainComplex`; no exact result.
- `msearch.py ... leansearch "In an injective resolution of a module vanishing
  Ext in degree d+1 from all ideal quotients makes the degree d kernel
  injective"`: eight hits on resolution existence, resolution constructors,
  term injectivity and `HasInjectiveDimensionLT.mk`; no exact result.
- `msearch.py ... grep
  "injective.*(kernel|cycles)|hasInjectiveDimensionLE_of_quotients|extMk_eq_zero_iff"`:
  25 capped hits, on concrete kernels and model-category factorizations;
  none gives this statement. Direct reading of ModuleCat/InjectiveDimension
  found invariance results under linear equivalences, not the claimed result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` with the preceding
  kernel/injectivity pattern found related resolution and kernel discussions,
  including `RegularLocalBoundedInjectiveResolution`; that theorem assumes a
  regular local ring and asserts existence of a bounded complex, so is not
  this arbitrary-resolution kernel assertion. Searches for the exact node id
  and proposed declaration name gave no hits in either library. The proposed
  name was also absent from `dag/lean_names_upstream.json`.

Validation: single-file server compilation through the prescribed `scompile.py`.
The first compile identified a privately imported `Ideal`; adding the public
ideal-quotient definition import fixed it. No declaration was duplicated or
weakened to resolve the import visibility issue. Final dry-run and delivery
results are recorded by the delivery wrapper.

## Second reading by Q53

A second pass by the same dispatcher-started worker reopened the node and the
module. No independent agent was started, as explicitly required by the brief.

The ring and all modules use universe u; the original I and ε are universally
quantified. Nonnegative support is `hneg`, degreewise injectivity is `hinj`, and
the augmented exact sequence is split into injectivity at N, `hexact₀` at I^0,
and `hexact` at every positive degree. In particular the degree-one hypothesis
uses the actual differential from 0 to 1. The integer d is constrained by hd,
so the natural-number degree in Ext is exactly the same d+1. The ideal
quantifier includes both endpoint ideals. The conclusion is injectivity of
that complex's degree-d kernel. Read the canonical `kernelIsoKer` signature
and the categorical/module injectivity bridge to check that no different
notion of kernel or injectivity has entered the statement. The source proof
and all five DAG proof steps are present in the theorem docstring. No
mathematical mismatch or statement dispute was found. The import visibility
repair is the only change resulting from elaboration checks.
