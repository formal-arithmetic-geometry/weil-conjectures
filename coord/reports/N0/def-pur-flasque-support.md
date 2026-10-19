## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtalePairFlasque` defines
`AlgebraicGeometry.ProEtale.IsFlasqueForOpen` and the actual canonical comparison
`finiteSupportedClosedComparison`. It states, with `sorry` proofs, the section formula,
left exactness, invertibility of that comparison with quasi-compact open complement,
the cokernel criterion for pair-flasqueness, and the counterexample without
quasi-compactness. The companion dependency module supplies the supported-kernel
construction through the compatible finite-coefficient star interface. All definition
data are actual categorical constructions. Every theorem has only `sorry` as proof.
No node statement, statement dependency, or proof dependency was changed.

Clause-by-clause reading:

- Schemes X, Z, U are `Scheme.{u}`. Closed immersion is `[IsClosedImmersion s]`,
  open immersion is `[IsOpenImmersion j]`, and complementary images are
  `IsCompl (Set.range s) (Set.range j)` in the left-exactness and comparison statements.
  The kernel depends only on j, so its definition and section formula do not need
  redundant choices of Z or s. Likewise the pair-flasque predicate depends only on j.
- The finite commutative coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ]`
  and `[Finite Λ]`. The coefficient category is `ModuleCat.{u + 1} Λ` and all sheaves
  are `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`. These are all constant-ring
  module sheaves, as used by the recorded constant-coefficient interfaces, without
  any constructibility predicate. The site retains its object universe u+1 and
  morphism universe u; no universe equality was imposed. No field, characteristic,
  finite-type, nonzero-ring or noetherian restriction is added to the construction.
  The allowed finite coefficient ring A from the conventions is a specialization;
  its name does not impose extra arithmetic hypotheses on an arbitrary finite Λ.
- Underived inverse/direct images are `upperStar` and `lowerStar` from
  `FiniteCoefficient.UpperLowerStar.Defs`, with their actual
  `upperStarLowerStarAdjunction`. The recorded `Scheme.proEtaleSheafInverseImage`,
  `Scheme.proEtaleSheafDirectImage` and `Scheme.proEtaleSheafAdjunction` are those same
  constructions. Constant-scalar ModuleCat-valued sheaves are the standard presentation
  of modules over the constant coefficient sheaf: the finite-coefficient realization
  and intrinsic realization interfaces identify them with the ring-sheaf presentations.
- The dependency's `finiteSupportedSections Λ j` is the kernel of the natural
  transformation `(upperStarLowerStarAdjunction ... j).unit` in the functor category.
  Functor-category kernels are objectwise kernels, so this is exactly G_Z, with the
  canonical action on morphisms induced by naturality. `finiteSupportedSectionsι`
  is its kernel inclusion. Its naturality supplies the restriction/morphism squares.
- `finiteSupportedSections_sections` asserts injectivity of the sectionwise inclusion
  and identifies its range with `{m | M.obj.map projection.op m = 0}`. Here `projection`
  is `(MorphismProperty.Over.mapPullbackAdj ... j ...).counit.app V`, whose definition
  is `Over.homMk (pullback.fst _ _) ...`. Thus it is exactly the restriction
  V ×[X] U → V, not a merely unspecified kernel arrow. This records both the explicit
  supported sections and the inherited restrictions.
- `finiteClosedUpperShriek Λ s j` is literally
  `finiteSupportedSections Λ j ⋙ upperStar (ModuleCat Λ) s`. Its object and morphism
  formulas are s^{-1}G_ZM and s^{-1}(G_Zf), exactly s^!_0 of the dependency.
- `finiteSupportedSections_leftExact` states `PreservesFiniteLimits` for each of G_Z
  and s^!, the categorical left-exactness condition for these additive module-sheaf
  functors. It assumes the open-closed pair but does not assume quasi-compactness.
- `finiteSupportedClosedComparison` is `Functor.whiskerLeft` of G_Z and the closed
  adjunction unit. Its target is literally `finiteClosedUpperShriek ... ⋙ lowerStar ... s`.
  Thus it is the specified natural comparison G_Z → s_*s^!, rather than an arbitrary
  isomorphism. `finiteSupportedClosedComparison_isIso` states `IsIso` of this natural
  transformation and adds exactly `[QuasiCompact j]` for this positive clause.
- `exists_finiteSupportedClosedComparison_not_isIso` records the unrestricted
  comparison's failure, with affine X, a closed immersion, a complementary open
  immersion that is not quasi-compact, and a sheaf where the actual component is not
  invertible. Its only nonzero-coefficient condition is `[Nontrivial Λ]` for this
  counterexample clause. The node's proof explicitly permits any nonzero finite Λ.
- `IsFlasqueForOpen` is exactly `Epi` of the open adjunction unit. The theorem
  `isFlasqueForOpen_iff_isZero_cokernel` uses the categorical sheaf cokernel and
  `IsZero`. Neither declaration asserts objectwise surjectivity.

Dependency declarations read and used:

- `def-exc-proetale-sections-with-support`: attached upstream
  `AlgebraicGeometry.ProEtale.sectionsWithSupport` and `closedUpperShriek`, read in
  `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion` (also confirmed with
  `scompile.py --source`). Their original signatures are general sheaf-valued kernels
  and their composite with closed upperStar. The compatible replacement is explained
  below; it states their finite constant-module specialization.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding with surjective stalk maps.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, the open immersion of locally ringed spaces.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and its quasi-compact import; `AlgebraicGeometry.QuasiCompact` is used only where
  the node asks for it. No locally-of-finite-type hypothesis is imposed.
- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, `Ring` and its `ringCommRing` instance. The
  general finite coefficient parameter is the node's explicit broader scope.
- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `Scheme.proEtaleDerivedCategory`, read through its constant-ring-sheaf definition;
  the underlying site is `Scheme.ProEt.topology` on `X.ProEt`.
- `def-weil-pbc-proetale-modules`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`,
  `finiteCoefficientIntrinsicRealization`; its reexported `ProEtaleFiniteModules`
  defines `FiniteCoefficientModules` and `finiteCoefficientRealization`.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`,
  `finiteCoefficientPullback`, `finiteCoefficientModuleDirectImage`,
  `finiteCoefficientRealization` and `finiteCoefficientUnrealization`; these retain
  the same canonical fixed-ring star operations and the coefficient identifications.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`
  and `proEtaleSheafAdjunction`; their full relevant signatures/docstrings were read.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.

The recorded proof-dependency modules for weakly-etale localization, exact constant
inverse image, module-sheaf limits/colimits, and immersion limit preservation are
imported without `public`. The unstated closed-essential-image proof dependency has
no recorded module; its mathematical content is named in the comparison proof
plan. It is not needed to type any of these statements. No import cycle was added.

Edge cases checked before drafting: Z empty makes j an identity, so the unit has
zero kernel and pair-flasqueness is automatic. Z=X makes the open empty, so its
pushforward is zero, the supported kernel is the original sheaf, and s^! agrees
with ordinary closed restriction (identity when s is identity). Pair-flasqueness
is again automatic. The zero coefficient ring and zero module sheaf are allowed
throughout the definitions and positive theorems; only the genuine failure example
requires nontrivial coefficients. No quasi-compactness or surjectivity on sections
was used for the section formula or left exactness. No claim that every
non-quasi-compact pair fails is made. The affine product-ring example in steps 5--7
was read, including its distinction between locally finite support and globally
finite support on affine objects.

Searches actually run:

- `msearch.py leanfinder`, query “Pro etale module sheaf sections supported on a closed
  subscheme kernel open adjunction unit pair flasque epimorphism”: eight unrelated
  etale-locus/module-generator results, no matching definition.
- `msearch.py loogle`, query `IsFlasque, sectionsWithSupport, closedUpperShriek`:
  zero hits, unknown identifier `IsFlasque`.
- `msearch.py grep`, query `sectionsWithSupport|closedUpperShriek|[Ff]lasque` in
  `CategoryTheory`: zero hits.
- `msearch.py leansearch`, query “A sheaf is flasque for a complementary open
  immersion if the unit of pullback pushforward is an epimorphism”: service unavailable
  (Internal Server Error), not a negative search result.
- Direct Mathlib `rg` in Topology/Sheaves and CategoryTheory/Sites found
  `TopCat.Sheaf.IsFlasque`, whose full definition requires every topological-open
  restriction to be epic. It is not this single-unit, pro-etale sheaf-epimorphism
  predicate. There was no supported-kernel or closedUpperShriek match in Mathlib.
- Direct `rg` in upstream WeilConjectures, including the exact node-id search with
  `grep -rn`, and `dag/lean_names_upstream.json`: no declaration for this node id or
  pair-flasque predicate. The generic supported-section declarations were found in
  `Derived.ClosedImmersion`, already attached to the dependency; they were reused
  as the mathematical construction and required the interface repair below.
- Direct `rg` in the project's `lean/Sheaf` and side upstream modules found related
  support/ordinary flasque material, but no pair-flasque definition. A final declaration
  name search across project, upstream and Mathlib found none of the new names.

Source checks: the current node statement and all seven proof steps were read,
including its existing stage-1 correction of unrestricted comparison. The local
blueprint markdown path is absent from this checkout. Stacks Tags
[03DA](https://stacks.math.columbia.edu/tag/03DA),
[09BN](https://stacks.math.columbia.edu/tag/09BN), and
[09AH](https://stacks.math.columbia.edu/tag/09AH) were opened directly; they confirm
module-sheaf kernels/exactness, open restriction, and the quasi-compact-complement
scope. This delivery makes no further statement correction and reports no dispute.

Validation: both delivered Lean modules compiled separately in dependency order
using `scompile.py N0 def-pur-flasque-support`, with no errors or warnings. Both
files bind universes and variables explicitly with `autoImplicit false`; all lines
are at most 100 characters. The required delivery dry run is the final check.

## Dependency modules

`def-exc-proetale-sections-with-support` owns
`Sheaf.AlgebraicGeometry.ProEtaleSupportedSections`. The attached legacy
`Derived.ClosedImmersion` imports `ProEtale.UpperLowerStar.Defs`, whereas the
recorded operations and inverse-image dependencies use
`ProEtale.FiniteCoefficient.UpperLowerStar.Defs`. The first combined compile failed
locally and the server confirmed the same error: the environment already contains
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. Importing the smaller finite-coefficient
star module and supplying the dependency's exact construction resolves this.

Under section 1(B), only this dependency's `lean` record changes. The module defines
`finiteSupportedSections` as the actual kernel of the natural open adjunction unit
in the functor category, `finiteSupportedSectionsι` as its canonical inclusion, and
`finiteClosedUpperShriek` as its composite with closed inverse image. Functor-category
limits are objectwise, so its objects and induced kernel maps are precisely the
node's construction; no comparison or adjunction property is added to that dependency.
No theorem or data is postulated in the dependency module. Its `lean.note` records
the collision and the meaning of the replacement. No new node is introduced.

## Second reading by N0

Independent second reader: I did not author the module. I read the shared node,
its seven proof steps, both delivered modules, the dependency node being repaired,
and the recorded coefficient/site/operation declarations. No mathematical mismatch
was found, so I retained the Lean and node records without changes. This reading
adds this report section only.

The node's objects, hypotheses, and conclusion clauses, matched individually:

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary scheme X, closed immersion s:Z→X, complementary open j:U→X | `{X Z U : Scheme.{u}}`, `[IsClosedImmersion s]`, `[IsOpenImmersion j]`, and `hPair : IsCompl (Set.range s) (Set.range j)` in the two pair theorems. The ranges are the underlying maps on points. Exact; no reducedness, noetherian, separation, finite-type, or base-field hypothesis. |
| Finite commutative ring Λ | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. Exact. No characteristic or nonzero-ring assumption in any definition or positive statement. The conventions' lifted `PurityFiniteSetting.Coefficient` is a permitted specialization, not a new hypothesis. |
| All module sheaves on the small pro-etale sites | `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`, and the corresponding categories for U and Z. Exact fixed-scalar presentation of the constant-ring modules; no constructibility predicate. |
| Identified underived inverse/direct images and their unit | `upperStar`, `lowerStar`, and `upperStarLowerStarAdjunction` of the finite-coefficient interface. Exact canonical Kan-extension/sheafification and precomposition operations, rather than chosen unrelated functors or maps. |
| G_Z M = kernel of the open unit | Dependency `finiteSupportedSections Λ j := kernel (upperStarLowerStarAdjunction ... j).unit`, taken in the functor category. Exact, including objectwise kernels. |
| Supported sections on V are precisely those vanishing on V×_X U | `finiteSupportedSections_sections` asserts injectivity of the canonical inclusion and equality of its range with `{m | M.obj.map projection.op m = 0}`. Exact realization as a submodule, allowing the usual canonical identification of a categorical kernel with this subtype. |
| Restriction maps inherited from M | `finiteSupportedSectionsι` is a natural transformation of sheaves; each component is a sheaf morphism. Its restriction naturality gives exactly the inherited maps, under the injective section identification above. Exact. |
| Induced action on morphisms of module sheaves | The functor-category kernel supplies the canonical kernel action induced by naturality of the same unit. Its inclusion is natural also in M. Exact real construction; no unspecified map or postponed functor law. |
| s^! M = s^{-1}G_Z M, and likewise on morphisms | `finiteClosedUpperShriek Λ s j := finiteSupportedSections Λ j ⋙ upperStar ... s`. Exact composite on objects and morphisms; this is the dependency's s^!_0. |
| Both functors are left exact, without quasi-compactness | `finiteSupportedSections_leftExact` states `PreservesFiniteLimits` of each functor, under the closed-open pair hypotheses only. Exact categorical left-exactness formulation for these module-sheaf functors. |
| The specified comparison is the closed adjunction unit on G_Z | `finiteSupportedClosedComparison` is `Functor.whiskerLeft (finiteSupportedSections Λ j)` of the closed adjunction unit. Exact direction G_Z→s_*s^!, with its actual naturality. |
| The comparison is a natural isomorphism when j is quasi-compact | `finiteSupportedClosedComparison_isIso` adds exactly `[QuasiCompact j]` and asserts `IsIso` of that natural transformation. Exact; this is not merely existence of an abstract isomorphism. |
| Without quasi-compactness there can be failure, even for an affine base and nonzero finite coefficients | `exists_finiteSupportedClosedComparison_not_isIso` quantifies over X,Z,U,s,j and a sheaf M, requires `IsAffine X`, the closed-open pair, `¬ QuasiCompact j`, and noninvertibility of the actual comparison component. `[Nontrivial Λ]` occurs only here. Exact and justified for each nonzero finite Λ by the node's explicit example; it does not assert failure for every non-quasi-compact pair. |
| Pair-flasqueness means that the open unit is epic as a sheaf map | `IsFlasqueForOpen Λ j I := Epi (...unit.app I)`. Exact. Z and s are absent because the predicate only depends on j, and every closed-open pair supplies this j. |
| Equivalent criterion: the sheaf cokernel is zero | `isFlasqueForOpen_iff_isZero_cokernel` uses `IsZero (cokernel (...unit.app I))` in the module-sheaf category. Exact; neither statement demands surjectivity on every site's section module. |

Definitions of kernels and the comparison extend to arbitrary scheme morphisms;
this adds no hypothesis to the stated closed-open-pair assertions. In particular,
the definition does not require quasi-compactness merely to form its data.

Dependency and source reading:

- I opened `def-exc-proetale-sections-with-support` and the full signatures of
  upstream `sectionsWithSupport`, `sectionsWithSupportι`, and `closedUpperShriek`
  in `Derived.ClosedImmersion`; I also fetched its current published source with
  `scompile.py --source WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion`.
  The old construction is the same objectwise kernel/induced-kernel-map functor and
  its closed inverse-image composite. The delivered dependency uses a kernel in
  the functor category, which canonically gives the same construction. The old
  module reaches legacy star operations, whereas the item's recorded inverse-image
  and coefficient dependencies reach the finite-coefficient star interface. The
  worker's documented duplicate-syntax import collision is an interface defect,
  not a reason to alter the mathematical notion. The section 1(B) replacement is
  justified and its `lean.note` explains both the defect and the exact replacement.
  Only its `lean` record differs from the shared dependency node. No new node exists.
- I read the actual finite-coefficient star declarations in the shared framework,
  and `coord/pefw-upstream-framework.md`. `lowerStar` evaluates by pullback on site
  objects; `upperStar` is the canonical sheaf pullback. The recorded
  `Scheme.proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`, and
  `proEtaleSheafAdjunction` are the corresponding constructions. I checked
  Mathlib `MorphismProperty.Over.mapPullbackAdj`: its counit is explicitly
  `Over.homMk (pullback.fst _ _) ...`. Thus the section formula uses the projection
  to V from the fibre product, not an arbitrary arrow.
- I opened `finiteCoefficientRealization`, its equivalence theorem and inverse,
  `finiteCoefficientPullback`, `finiteCoefficientModuleDirectImage`, and
  `finiteCoefficientIntrinsicRealization` with its exact-equivalence theorem.
  These identify the fixed-scalar `ModuleCat` sheaves with the ring-sheaf
  presentations recorded by the dependency nodes. They impose no constructibility
  condition. I also checked `Scheme.proEtaleDerivedCategory`'s underlying site and
  constant ring sheaf, `ringedSiteModules := SheafOfModules`,
  `PurityFiniteSetting.Ring` and its lifted `Coefficient`, and Mathlib's closed
  immersion, open immersion and quasi-compact morphism interfaces. No private copy
  of these notions is introduced.
- The local blueprint markdown and Stacks checkout are absent. I therefore read
  the official Stacks `.tex` sources at
  [proetale.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/proetale.tex)
  (`lemma-open-immersion`, `lemma-ses-associated-to-open`, and
  `lemma-closed-immersion`) and
  [sites-modules.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/sites-modules.tex)
  (`lemma-abelian`, alongside the module pullback/adjunction paragraphs).
  The first two pro-etale passages assume arbitrary schemes; the short exact
  sequence specifically assumes a quasi-compact open immersion. The closed
  inverse image commutes with limits without that assumption. The module passage
  gives the abelian category and exact forgetful functor. These support the exact
  hypotheses used here and the node's already reviewed scope correction. The
  affine product-ring counterexample is an agent argument, as the node records;
  I checked its finite-support quotient construction and both vanishing inverse
  images against the corresponding source facts. No new statement correction,
  `statement_change`, or citer audit is introduced by this stage-2 delivery.

Edge cases:

- Z empty / j an isomorphism: the open unit is invertible, its kernel is zero,
  and pair-flasqueness is automatic. The section formula also gives zero support.
- Z=X / U empty: the open direct image is zero, the kernel is M, and s^! is
  ordinary inverse image (the identity if s is the identity). Pair-flasqueness
  is again automatic. The same signatures permit the entirely empty scheme.
- The zero module sheaf and the zero coefficient ring remain allowed throughout
  all definitions and positive assertions. Only the failure example needs
  nontrivial coefficients, exactly as in the node's proof. No characteristic,
  n>0, arithmetic invertibility, or finiteness of a site object is imposed.
- All universes are bound explicitly. Schemes use u; coefficient modules use
  u+1 as in the dependency interfaces, while the site's object/morphism universes
  retain their published sizes. There is no independent smaller test-object or
  index universe, equality of site universes, or nonemptiness assumption. There
  is no index-set binder to exclude an empty family. The counterexample can use
  a small field and a countable product already at the smallest scheme universe.

Independent searches (using different query words from the worker):

- `msearch.py ... leanfinder`: “A module sheaf is relatively acyclic for an open
  subset if its restriction adjunction unit is epic; kernel of this unit consists
  of sections vanishing on that subset”. Eight hits on module generators,
  quasicoherence and abelianness; none defines this pair-specific predicate or
  the complete supported-section statement.
- `msearch.py ... loogle 'CategoryTheory.Epi, CategoryTheory.Sheaf'`: twelve hits,
  including `Sheaf.Hom.epi_of_presheaf_epi` and locally-surjective criteria;
  these are general epimorphism facts, not the pair-flasque definition.
- `msearch.py ... grep 'relativeFlasque|supportedAway|supportKernel|flabby'`:
  zero Mathlib hits. Direct `rg` searches in Mathlib, upstream WeilConjectures,
  the shared framework and `lean/Sheaf` found ordinary topological flasqueness
  and the already recorded upstream support dependency. I opened
  `TopCat.Presheaf.IsFlasque` and `TopCat.Sheaf.IsFlasque`: they require epic
  restrictions for all pairs of topological opens and are not this condition on
  a single pro-etale adjunction unit. Searches for the new declaration names
  found no collision in those read-only sources.
- `msearch.py ... leansearch`: “The kernel of the open restriction unit defines
  sections supported on a closed subscheme of the pro etale site”. Service
  unavailable (Internal Server Error), recorded as unavailable rather than a
  negative result. LeanFinder, Loogle and direct text searches were available.

H5/H6/H8/H9 checks: all four new definition data are actual categorical terms
(the kernel, its inclusion, the composite and the whiskered unit), and the
pair-flasque predicate is the actual `Epi` proposition. Every theorem proof is
only `sorry`, and its docstring gives the relevant node proof steps with sources.
All declarations carry their owning blueprint id. Both node `lean.statement`
strings occur verbatim as the primary signatures; only `lean` differs from each
shared node. There are no unbound variables, file-local notation or private
constructions, and every Lean line is at most 100 characters.

Second-reader validation: `scompile.py N0 def-pur-flasque-support` compiled both
sibling modules separately and successfully, including each library-form module,
with no errors or warnings. The dependency and item library-form compiles took
3.3 s and 4.2 s respectively under the prescribed 60-second limit. No global build
or direct mutation of either read-only checkout was performed.
