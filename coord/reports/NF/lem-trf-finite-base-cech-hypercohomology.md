## Worker report

The module `Sheaf.TraceFormula.FiniteBaseCechHypercohomology` states
`AlgebraicGeometry.Etale.exists_finite_base_cech_hypercohomology`, with one `sorry`.
All other declarations are explicit constructions or types of compatible presentation data;
none selects an object from an unproved existence statement. The main theorem's docstring
reproduces all seven proof steps of the DAG, including the unreplaced exact rows, the
nonadditive functorial resolution, the signed cone-total comparison, finite injective totals,
module-valued Leray, the shifted spectral sequence, and the base-restriction roof.

Hypothesis and clause correspondence (all auxiliary names below are in
`AlgebraicGeometry.Etale`):

- A commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`. Schemes are
  `Z Y : Scheme.{u}`, and the finite surjection is `(p : Z ⟶ Y) [IsFinite p] [Surjective p]`.
  There is no noetherian, separatedness, invertibility, or field hypothesis.
- The coefficient category is `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  This is precisely the module-valued encoding prescribed by the recorded
  `def-kun-rgamma-unbounded`, not abelian sheaves with forgotten coefficients. The existing
  `Scheme.etaleConstantModuleFunctor_isEquivalence` identifies this encoding with sheaves
  of modules over the constant ring sheaf. No new category or inverse image is defined.
- The integer lower bound is `(a : ℤ)`, and
  `K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))` with `[K.IsGE a]`
  is the standard t-structure condition. All inverse images are
  `(upperStar (ModuleCat Λ) f).mapDerivedCategory`, induced by exact inverse image.
- `finiteCechProjection p q` is the augmentation of `(Arrow.mk p).augmentedCechNerve`.
  Its domain is Mathlib's wide pullback of `q.len+1` copies of `p`, hence exactly `Z_q`.
  `finiteCechBaseMap` is Mathlib's morphism of augmented Čech nerves induced by the actual
  Cartesian square `pullback h p`; it gives `Z'_q → Z_q`. The nerve on `pullback.fst h p`
  is canonically `Y' ×_Y Z_q`, with the same projections, rather than a different cover.
- `FiniteCechResolvedModel.diagram` is an actual augmented cosimplicial cochain diagram.
  `pointIso` identifies its augmentation object with `RΓ(Y,K)`, and `columnIso` identifies
  column `q` with `RΓ(Z_q,p_q* K)`. Here and throughout `RΓ` is exactly
  `Etale.rightDerivedGlobalSections (ModuleCat Λ) T`.
  `columnMap` prescribes every simplex map, so both cofaces and codegeneracies are
  compatible. `augmentationMap` prescribes every augmentation as canonical restriction.
- `belowPoint` and `belowColumns` say that every representative has internal degrees at
  least `a`. `finiteCechBicomplex` uses Mathlib's `alternatingCofaceMapComplex`, then extends
  the Čech degree by zero from ℕ to ℤ. Thus Čech degree is nonnegative, the horizontal
  differential is the alternating sum of cofaces, and `finiteCechTotal` uses the existing
  total differential `δ + (-1)^q d`. Only `0 ≤ q ≤ n-a` can contribute to degree `n`, so
  each diagonal is finite, including an empty diagonal for `n<a`.
- `augmentation` is a chain map and `augmentationComponent` specifies it as augmentation
  into the `q=0` diagonal summand. `augmentationQuasiIso` is the promised augmentation
  quasi-isomorphism. Conjugating its localized map by `pointIso.inv` gives exactly the
  displayed `RΓ(Y,K) → Tot` in the derived category of Λ-modules.
- `FiniteCechSpectralConvergence` specifies the column filtration degreewise as the finite
  supremum of canonical summand images. The page `E` starts at 1. Its first page is
  the cohomology of column `q`; applying `DerivedCategory.homologyFunctor` to `columnIso`
  and using the existing `homologyFunctorFactors` identifies it with
  `(Etale.cohomology (ModuleCat Λ) Z_q j).obj (p_q* K)`.
  The page support condition is `q<0 ∨ j<a`, with `q,j : ℤ`; negative allowed `j` remain.
  `G n` is precisely the image filtration on total cohomology and is finite for every `n`.
  The equations for `eD`, the alpha colimit, initial graded projection and page
  differential bind the exact couple to this filtration and to `E`.
  `X.ConvergesTo L H` gives convergence, and the last clause explicitly gives stationary
  terms, zero incoming/outgoing differentials, and identification with `G`'s graded pieces.
  The augmentation quasi-isomorphism and `pointIso` canonically identify this abutment
  with `H^{q+j}(Y,K)`; it is not a different cohomology theory.
- Naturality in coefficients is the first quantified conclusion, for each `v : K ⟶ L`
  with the same lower bound. The point and columns are prescribed as the functorial maps
  on RΓ, and the last equality is the natural augmentation square.
- Arbitrary base restriction is `∀ (Y' : Scheme.{u}) (h : Y' ⟶ Y)`; `M'` has the actual
  pullback cover and coefficient `(upperStar (ModuleCat Λ) h).mapDerivedCategory.obj K`.
  `FiniteCechResolvedRoof` gives three maps of actual augmented diagrams
  `D → target ← middle → D'`. The inverse isomorphisms are expressly the localized
  backward maps, including on the total; they are not unrelated column choices.
  Both intermediate diagrams have the same internal lower bound. The first equation
  identifies the augmentation-object roof with restriction along `h`; the second
  identifies every column with restriction along `g_q`, followed by the canonical
  coefficient identification. `finiteCechBaseCoefficientIso` is the composite of the
  two existing pullback-composition isomorphisms for the Cartesian equality.
  The final equation is exactly the required square in `D(ModuleCat Λ)`.
  No forward, final, or column restriction map is assumed or asserted invertible.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite` (and the
  imported underlying-map declaration `AlgebraicGeometry.Surjective`).
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is exactly
  `SheafOfModules`; the equivalent module-valued-sheaf interface above is the recorded
  derived-sections interface. `EtaleConstantRingModuleEquivalence` gives the bridge.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryPlus`, `mapDerivedCategoryNatIso`,
  `mapDerivedCategoryCompIso`. We use the ambient exact derived functor at the specified
  standard lower bound, equivalently its restriction to D⁺.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.TStructure`:
  `DerivedCategory`, `DerivedCategory.Q`, `homologyFunctor`, `IsGE`, `TStructure.t`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.condition`; `Mathlib.AlgebraicTopology.CechNerve` supplies
  the already-existing iterated fibre products and all their maps.
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`:
  `Scheme.etaleModuleSheaves_grothendieckAbelian`; the category is Grothendieck abelian,
  with the ModuleCat-valued counterpart supplied by the existing sheaf instance.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedGlobalSections`, `Etale.cohomology`. Their full signatures use
  the coefficient category with morphism universe `u+1`, as our Λ-module category does.
- The existing filtration/subquotient/exact-couple APIs are imported from
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
  `WeilConjectures.CategoryTheory.ExactCoupleConvergence`; the latter's current published
  source was read with `scompile.py --source`. Proof-dependency imports are retained for
  the augmentation criterion, mapped totals, filtered pages, cone comparison,
  functorial injective resolutions, K-injectives and double-complex spectral sequences.
  Proof dependencies without a published declaration were not invented or imported.

Edge cases checked before and after writing: the zero ring and zero complex; `a=0`, `a<0`
(including negative cohomology), and `a>0`; total degrees below `a`; Čech degree zero;
empty schemes (a surjection onto the empty scheme has empty domain); identity covers;
identity base restriction; arbitrary nonflat/nonfinite `h`. No case is excluded by the
binders. The integer reindexing changes neither the Čech sign nor the total degree.

Searches made:

- `msearch.py ... leanfinder "finite surjective Cech hypercohomology descent bounded below
  module sheaves natural restriction"`: eight hits, about coherent-site local
  surjectivity, module sheafification, and Mayer–Vietoris; no descent theorem.
- `msearch.py ... leansearch "Cech hypercohomology finite surjective morphism bounded below
  complexes"`: eight hits including `CochainComplex.cm5b`, surjective scheme morphisms
  and unrelated group cochains; no match.
- `msearch.py ... loogle "CechNerve, rightDerivedGlobalSections"`: zero hits (unknown
  identifier `CechNerve`).
- `msearch.py ... grep "CechNerve|cechNerve|hypercohomology" CategoryTheory`: five hits on
  formal-coproduct Čech comparison, not finite-surjective hypercohomology.
- `rg` in Mathlib found the existing Čech nerve and alternating-coface complex, used here.
  `rg` in upstream `WeilConjectures/SixFunctors/Etale` found derived sections, Leray and
  exact pullback; its GlobalSections module explicitly lists the general derived
  restriction transformation as a TODO. Our restriction is the explicit unit–Leray
  composite, using those existing constructions.
- `rg` / node-id grep across upstream `WeilConjectures` and `lean/Sheaf` found no existing
  theorem. `NearbyFiniteBaseDescent.lean` mentions this node only as a proof input.
  Other Čech modules concern open covers, other coefficient categories, or cone
  comparison. The upstream declaration index was also consulted. No existing definition
  is copied: each helper assembles existing constructions for this node's own diagram.

Validation: the prescribed `scompile.py NF lem-trf-finite-base-cech-hypercohomology <file>`
compiled both the sandbox and library form cleanly, with no warnings or errors. There is
exactly one postponed theorem proof. No node statement correction, dependency repair, or
new independent notion was needed. Only the item's `lean` field changes.

## Second reading by NF

Author's separate second pass, with the original node JSON and complete module open;
no second agent was started, as the dispatch brief requires. The maintainer supplies the
independent delivery review.

I matched each hypothesis and clause using the correspondence above. In particular I
checked that `pointIso` does not forget the Λ-action, the nerve has `q+1` factors, the
augmentation is fixed on cochain components, and every simplex map is pinned to canonical
restriction. I checked the finite filtration bounds for negative `a`, and that the exact
couple is tied to filtration-step inclusions and graded projections rather than an
arbitrary convergent spectral sequence. The abutment is transported by the prescribed
augmentation and point comparison. I also checked that the base-change roof is made of
actual augmented diagram maps before totalization, and that its backward point, column,
and total inverses invert those very maps. The coefficient transport follows the
Cartesian equality in the correct direction. No isomorphism of column restriction is
claimed. This second pass added the explicit coefficient-naturality clause so that
"natural augmentation" is represented as well as the requested base naturality.
No mathematical mismatch or disputed statement remains.
