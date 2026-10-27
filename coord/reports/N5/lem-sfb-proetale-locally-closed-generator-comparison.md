## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleLocallyClosedGeneratorComparison` states
`AlgebraicGeometry.proEtale_locallyClosed_generator_comparison`. This is one theorem,
with `sorry` as its entire proof, combining all three clauses of the node. It introduces
no definitions, instances, arbitrary comparison maps, or choices of isomorphisms.
The docstring records all nine proof steps of the reviewed split, with the named inputs.

### Hypotheses and geometric objects

- A scheme X: `(X : Scheme.{u})`.
- X quasi-compact and locally Noetherian: `[IsNoetherian X]`. Mathlib's class extends
  `IsLocallyNoetherian X` and `CompactSpace X`; there is no separatedness assumption.
- A finite commutative coefficient ring: `(Λ : Type u) [CommRing Λ] [Finite Λ]`.
  The actual fixed coefficient category is `ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)`.
  The lift is the existing intrinsic-module API's universe convention and is canonically
  ring-isomorphic to Λ; it changes neither modules nor projectivity. Because Λ is finite,
  representing it in the scheme universe excludes no coefficient ring up to this canonical
  coefficient transport. Sections and modules live in the larger universe u+1; the sites
  still have object universe u+1 and morphism universe u. There is no equality imposed on
  these two site universes.
- A locally closed stratum: `{S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]`.
- Its scheme-theoretic closure C: the actual Mathlib object `a.image`, not an arbitrary
  factor scheme or a reduced topological closure.
- The closed immersion g: the actual Mathlib map `a.imageι` (with its existing closed
  immersion instance).
- The resulting open immersion j: `(j : S ⟶ a.image) [IsOpenImmersion j]`, together with
  `(_hj : j ≫ a.imageι = a)`. This is the factorization specified in the node. Since
  `a.imageι` is monic and `a.toImage ≫ a.imageι = a`, the equation forces `j = a.toImage`.
  Quantifying over this explicitly named open factor does not supply a freely chosen map.
  Its existence requires no additional hypothesis: the underlying space of S is a
  subspace of the Noetherian space X, hence Noetherian, so a is quasi-compact and the
  recorded `IsImmersion.instIsOpenImmersionToImageOfQuasiCompact` applies.

### Clause 1

On the etale site the functor is `Etale.lowerStar (ModuleCat …) a.imageι`, and on the
pro-etale site it is `ProEtale.lowerStar (ModuleCat …) a.imageι`. These are the recorded
base-change/precomposition direct images, with the fixed scalar action. The latter is
also definitionally `Scheme.proEtaleSheafDirectImage a.imageι (ModuleCat …)` from the
recorded general inverse-image interface. On **each** site, the first four conjuncts
state `PreservesFiniteLimits` and `PreservesFiniteColimits`. For these additive functors
between abelian categories this is precisely exactness.

The next two conjuncts separately quantify over **every** module sheaf M on S on the
respective site. They state `IsIso` for the actual
`(…lowerStar … a.imageι).rightDerivedFunctorUnit.app` at
`(HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj (j_!.obj M))`.
Thus the target is the unbounded derived direct image of `(j_!M)[0]`. The source is the
localization of the termwise direct image of this single complex; the usual
map-of-single and quotient-to-derived isomorphisms identify it with `(g_*j_!M)[0]`.
Inverting this specified unit is exactly inverting the node's canonical morphism:
precomposing by the canonical source identification does not change invertibility.
Neither assertion is merely a degreewise cohomology comparison, an unnormalized
existence of a derived isomorphism, or an assumption of acyclicity of M.

The extensions used here and in clause 3 are the recorded
`Etale.openImmersionLowerShriek` and `ProEtale.openImmersionLowerShriek`, with coefficients
`ModuleCat …`: left Kan extension along localization followed by sheafification.

### Clause 2

This conjunct quantifies over
`L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))`.

- Local constancy on the etale site is `Scheme.IsLocallyConstantSheaf L`. Its existing
  definition is a covering whose localized restrictions are constant **module** sheaves;
  it is not a predicate on an underlying sheaf that forgets the scalar action.
- At every geometric point: the premise explicitly quantifies over
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`.
- Finite projective etale stalks: the premise is
  `Module.Finite (ULift Λ) (pointedEtaleStalk (A := ModuleCat …) L s) ∧
   Module.Projective (ULift Λ) (pointedEtaleStalk (A := ModuleCat …) L s)`.
  The stalk is the recorded colimit in the module category, not a set colimit with
  an arbitrary module action.
- Comparison inverse image: `ProEtale.comparisonUpperStar (ModuleCat …) S`, the left
  adjoint of `Scheme.proEtaleSiteComparisonModules`. To use the recorded intrinsic
  constant-ring predicates, the conclusion expresses the same sheaf as
  `(ProEtale.finiteCoefficientIntrinsicComparison S Λ).obj L`. Its definition is the
  specified comparison followed by `finiteCoefficientIntrinsicRealization`, the canonical
  associated-module-sheaf construction along the scalar sheafification unit. It is not
  a new inverse image or a realization chosen from a bare existence theorem.
- Pro-etale local constancy is the **recorded**
  `Scheme.IsLocallyConstantProEtaleModuleSheafOfUniverses S Λ` applied to this realization.
  This permits varying module models on an arbitrary pro-etale covering, without adding
  a freeness or constant-rank hypothesis.
- At every geometric point of S, the conclusion uses the **recorded**
  `Scheme.finiteCoefficientModuleStalkFunctor s Λ` on that realized sheaf. This is
  `geometricRingModuleStalkFunctor` followed by restriction of scalars along the canonical
  constant germ. Its output carries the correct `ULift Λ` action.
- The three conclusions are explicitly `Module.Finite`, `Module.Projective`, and
  `Module.Flat` over `ULift Λ` on this module stalk. No projectivity conclusion has
  been replaced by mere flatness or finiteness as a set.

### Clause 3

The last conjunct is `Nonempty (F ≅ G)` for functors from etale module sheaves on S to
pro-etale module sheaves on X, where

```
F = Etale.openImmersionLowerShriek … j ⋙
    Etale.lowerStar … a.imageι ⋙ ProEtale.comparisonUpperStar … X
G = ProEtale.comparisonUpperStar … S ⋙
    ProEtale.openImmersionLowerShriek … j ⋙ ProEtale.lowerStar … a.imageι
```

A functor isomorphism has exactly the displayed sheaf isomorphism as each component
and its naturality equation for every sheaf morphism. It therefore states the node's
naturality in M, rather than only unrelated isomorphisms for each M. The node specifies
existence of a natural isomorphism, so this clause does not add a normalization equation
for a comparison arrow not specified there. No lisse, projectivity, constructibility,
or boundedness condition is imposed on M in this clause.

### Dependency declarations and their modules

The recorded source modules and full signatures/docstrings were read before use.
Statement-dependency modules are public imports; the recorded proof-dependency modules
are plain imports unless also needed publicly by the statement.

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent general-site abbreviation of `SheafOfModules`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, with the inherited global Grothendieck-category instance.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`; their existing module-valued left adjoint is
  `ProEtale.comparisonUpperStar` in the publicly imported
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`,
  `Scheme.Hom.imageι`, `Scheme.Hom.toImage`, `Scheme.Hom.toImage_imageι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` and the recorded
  `IsImmersion.instIsOpenImmersionToImageOfQuasiCompact` instance.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion` and the
  existing closed-immersion instance for `a.imageι`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `ProEtale.openImmersionLowerShriek`, its adjunction and exactness instances.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`,
  `Scheme.proEtaleSheafDirectImage` (definitionally `ProEtale.lowerStar`),
  `Scheme.proEtaleSheafInverseImage` and the constant coefficient maps.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded etale-sheaf
  vocabulary. Module local constancy is `Scheme.IsLocallyConstantSheaf` from
  `WeilConjectures.ConstructibleSheaf.Defs`, the existing module-valued form cited in
  this dependency's record (its primary declaration is the set-valued form).
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `AlgebraicGeometry.pointedEtaleStalk`,
  specialized explicitly to `ModuleCat …`.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `Scheme.IsLocallyConstantProEtaleModuleSheafOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`:
  `Scheme.geometricRingModuleStalkFunctor`, `Scheme.finiteCoefficientModuleStalkFunctor`.
- The only additional statement dependency is the already landed
  `def-weil-pbc-proetale-modules`, whose recorded module is
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`. Its already published companion
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison` supplies
  `ProEtale.finiteCoefficientIntrinsicRealization` and
  `ProEtale.finiteCoefficientIntrinsicComparison`. The former is concretely defined as
  fixed-module-presheaf realization followed by module sheafification; the latter
  composes it with the specified comparison. No new node or dependency repair is needed.

The unbounded derived functor and its canonical unit are
`CategoryTheory.Functor.rightDerivedFunctor` and `rightDerivedFunctorUnit` from
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`, publicly
available through the two `SixFunctors.…Derived.UpperLowerStar` imports.
`CochainComplex.singleFunctor` and `HomotopyCategory.quotient` give the degree-zero input.
The proof modules from the reviewed split are imported, including
`OpenClosedRecollement`, `ProEtaleRingedOpenClosed`, `ConstantLeftModuleInverseImage`,
`ExactFunctorDerivedFunctor`, `ProEtaleLisseOrigin`, `ProEtaleComparisonStalk`,
`ConstantRingModuleSheaves`, `ProEtaleWeaklyEtaleLocalization`,
`LocalizedModuleExactForSystems`, `ComparisonDirectImage`, `ComparisonPullbackExact`,
and `ProEtaleExtensionZeroComparison` in their recorded `Sheaf` module paths.
Mathlib's Noetherian topology, adjunction mates, affine morphisms, exact derived
factorization and `Module.Flat.of_projective` provide the matched proof leaves.

### Edge cases and semantic checks

- Empty S: no point is required or chosen. Every module sheaf on the empty site is
  zero; all comparisons, including both derived units, are the zero-object isomorphisms.
- Empty X: the same argument applies. No nonempty covering or point hypothesis is added.
- Zero coefficient ring: there is no `[Nontrivial Λ]`; every module is zero, hence finite
  projective and flat, and all functors/comparisons remain meaningful.
- Identity stratum: the closure and its canonical closed map are kept, rather than
  assumed definitionally equal to X. The equation on j is compatible with the standard
  identity/closure isomorphisms.
- Nonreduced strata: `a.image` uses the kernel ideal and retains the scheme-theoretic
  structure; it is not replaced by the reduced closure.
- Nonseparated Noetherian X: no separation hypothesis appears. Only the closed map g
  must be qcqs in the proof, which follows because it is a closed immersion.
- Varying ranks and disconnected strata: the local-constancy predicate permits varying
  local models; finite projectivity is checked separately at all geometric points.
- Arbitrary M in clauses 1 and 3: no hypothesis from the special sheaf L leaks into them.
- Exact canonical derived arrow: the assertion uses the named derived unit in D(X),
  not a map chosen to be invertible or only a family of cohomology isomorphisms.

### Searches

All remote searches used the prescribed `batch2/msearch.py N5
lem-sfb-proetale-locally-closed-generator-comparison` wrapper.

- LeanFinder, query: `Etale to proetale inverse image commutes with extension by zero
  along locally closed immersions and preserves finite projective locally constant
  sheaves`. The search did not supply a theorem combining the three clauses.
- Loogle, query: `AlgebraicGeometry.ProEtale.lowerStar,
  AlgebraicGeometry.ProEtale.comparisonUpperStar`. Result: 0 hits, unknown identifier
  `AlgebraicGeometry.ProEtale.lowerStar` in its Mathlib index. These are project names,
  not Mathlib matches.
- Mathlib grep through msearch, query:
  `locally.closed.*[Cc]omparison|[Cc]omparison.*locally.closed|generatorComparison`.
  Result: 0 hits.
- LeanSearch, query: `Comparison of locally closed generators commutes with extension
  by zero from the etale to proetale site`. Eight hits concern site-local object
  properties, the small etale topology, locality of etale ring maps, stalk germs,
  Zariski/etale topology and condensed left Kan extension. None states this comparison.
- `rg` in the upstream `lean/WeilConjectures` and in `lean/Sheaf`, for the item id,
  `locallyClosedGeneratorComparison`, and `locallyClosed.*[Cc]omparison`: no upstream
  declaration of the item. Side hits include
  `etale_locallyClosed_extension_comparison` (an etale factorization comparison) and
  `finiteDuality_locallyClosed_comparison` (exceptional adjoints). Their complete
  statement regions were read: neither gives this item's exactness, finite-projective
  local-system pullback and all-sheaf natural comparison together.
- Targeted source reading found the already defined canonical intrinsic coefficient
  realization, the recorded independent-universe local-constancy predicate, and the
  recorded module-stalk functor. These are reused with no private copies.

No statement correction, new node, unusable dependency, or STATEMENT-DISPUTED issue was
found. The original natural-language statement, proof and proof dependencies are kept.
The earlier worker's stage-1 preflight refusal does not by itself prevent stating this
reviewed split in stage 2.

### Validation

The module compiled cleanly through `batch2/scompile.py` on the live server, both as a
sandbox module and under its intended library name. After adding the recorded proof
imports, the module again compiled without errors or warnings. The final import and
node-record packet is checked by the prescribed dry run before delivery. No local Lean
compile, global build, live-file edit, or direct Git operation was used.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
