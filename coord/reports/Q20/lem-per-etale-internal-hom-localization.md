## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization` states
`AlgebraicGeometry.Etale.etale_internalHom_localization`. All theorem proofs are
`sorry`; all definition data are explicit. The original node statement is unchanged.

Clause-by-clause rendering:

- Arbitrary scheme X and commutative coefficients: `X : Scheme.{u}`,
  `A : Type (u + 1)` and `[CommRing A]`. The fixed-scalar sheaf encoding is exactly
  the dependency's `DerivedCategoryModule A X`, namely ordinary derived categories
  of `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- Closed i and complementary open j: `[IsClosedImmersion i]`,
  `[IsOpenImmersion j]`, and `hij : Set.range i.base = (Set.range j.base)ᶜ`.
- The actual supported inverse image is `perEtaleClosedSupport A i j`, defined as
  `perEtaleSupportKernel A j ⋙ upperStar (ModuleCat A) i`; the kernel is the
  functor-category kernel of the restriction adjunction unit. This includes the
  induced maps and their A-actions. Its additivity is a separately named theorem.
- Inverse images are `perEtalePull A i` and `perEtalePull A j`, which abbreviate
  `upperStar.mapDerivedCategory`, so are applied termwise, not derived tensor
  pullbacks with an extra hypothesis.
- Closed direct image `perEtaleClosedPush A i` is `lowerStar.mapDerivedCategory`.
  Its exactness for arbitrary A is the upstream instance
  `Etale.preservesFiniteColimits_lowerStar_of_isFinite` (closed immersions are finite). Ri! is the ordinary
  `perEtaleClosedSupport.rightDerivedFunctor`, computed on K-injectives; on D+
  this is the right derived functor specified in the node.
- The support adjunction `a` is existentially supplied, not assumed. Its counit
  is fixed by the equality with the kernel inclusion after the canonical closed
  unit. Therefore arbitrary adjunction rescalings are excluded.
- K is in `DerivedCategory.Bounded`, N in `DerivedCategory.Plus`. Their full
  inclusions form `perEtaleBoundedPlusPairs`. The conclusion is quantified over
  every pair of such objects, with no numerical bound fixed.
- The closed endpoint is `perEtaleClosedHom`, exactly i_* RHom(i*K,Ri!N).
  The middle is `perEtaleHom A X`, the existing `Etale.derivedHom` uncurried.
  The open endpoint is `perEtaleOpenHom`, exactly Rj_* RHom(j*K,j*N).
- eC identifies the closed endpoint with RHom(i_*i*K,N), and eO identifies
  RHom(j!j*K,N) with the open endpoint. Their components must equal
  `perEtaleClosedHomComparison` and `perEtaleOpenHomComparison`. Both comparisons
  are real constructions using tensor evaluation and the canonical adjunctions.
  The tensor comparison transports the existing K-flat pullback comparison
  through `leftDerivedUpperStarIsoMapDerivedCategory`; it adds no assumption.
- The first arrow is eC followed by contravariant precomposition with the actual
  closed unit; the second is contravariant precomposition with the actual open
  counit followed by eO. Thus these are exactly the arrows specified by the node.
- `δ` is a natural transformation from the open endpoint to the shift by `(1 : ℤ)`
  of the closed endpoint; `Triangle.mk ... (δ.app ...) ∈ distTriang _` states
  distinguishedness. eC/eO are natural isomorphisms on D^b(op) × D+; the two
  precomposition maps are natural in both arguments by adjunction naturality and
  bifunctoriality of Hom. The natural transformation δ supplies naturality of
  the last arrow as well. No arbitrary choice of connecting maps per object occurs.
- No constructibility, finite Tor amplitude, `[Finite A]`, field, noetherian,
  separatedness, dualizing complex, or exceptional-adjoint existence hypothesis
  occurs. Ordinary unbounded ambient derived categories are used throughout.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.Etale`, `smallEtaleTopology`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: `DerivedCategoryModule`;
  Mathlib's `DerivedCategory.Bounded`, `DerivedCategory.Plus`, and their `ι`.
  The current source of DerivedCategories was read via `scompile.py --source`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`. In particular the coefficients are ModuleCat A.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  `openImmersionLowerShriek`, `openImmersionLowerShriekUpperStarAdjunction`;
  Derived.OpenImmersionLowerShriek: its existing derived adjunction.
- Mathlib.CategoryTheory.Triangulated.Pretriangulated: `Triangle`, `distTriang`.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses: dependency's imported
  ordinary-etale `Etale.derivedHom` and `derivedTensorHomAdjunction` from
  WeilConjectures.SixFunctors.Etale.Derived.Hom. No copy of internal Hom is made.
- The published proof-dependency modules are imported without `public` (some
  already transitively available through the public statement imports). The
  sheaf closed internal-adjunction prerequisite has no recorded module yet, so
  it has no import. The exactness and additivity helpers needed to type this
  item are stated here as parts of its own supported-Hom construction.

Source check: read the local ILO PDF at PDF page 319 / printed page 313, which
contains the displayed triangle in XVII 7.6.10; read Stacks etale-cohomology.tex,
`lemma-sections-with-support-acyclic` (09XQ) and preceding support construction.
The docstring reproduces all seven DAG proof steps with named dependencies,
including bounded and bounded-below models, the closed and open comparison,
and descent/naturality. The helper exactness and additivity theorems each have
source and complete proof descriptions and share this owning DAG statement.

Edge cases checked before writing: empty X; empty closed or empty open part;
identity closed/open immersion; zero K or N; the zero ring; positive and mixed
characteristic. Empty parts reduce to the zero term and the remaining Hom
identity. No nonemptiness or nontriviality binder excludes these cases. K can
have any finite cohomological support and N any lower bound. The site has object
universe u+1 and arrow universe u, while coefficient modules have universe u+1;
these universes are not forced equal. The universe convention is the recorded
fixed-scalar étale interface, not an independent too-small module universe.

Searches (2026-10-18 UTC; logs also in searches.jsonl):

- msearch leanfinder: "Derived internal sheaf Hom closed open localization
  distinguished triangle arbitrary commutative coefficients": eight generic
  sheaf/cohomology hits, no localization statement.
- msearch loogle: `AlgebraicGeometry.Etale.derivedHom`: no Mathlib hit (the name
  is upstream); read the upstream definition directly and used it.
- msearch grep: `localizationTriangle|internalHomLocalization|closedSupport`
  in CategoryTheory: no hits.
- msearch leansearch: "Derived internal Hom closed open localization triangle
  for etale module sheaves": eight hits, mainly generic triangulated localization
  and Scheme.Modules.Hom; none gives the statement.
- rg in upstream WeilConjectures and lean/Sheaf for the item id, internal Hom,
  localization triangles, closed support and kernel adjunctions. Found generic
  derived Hom, exact pullback, open-closed triangles and finite-coefficient
  closed adjoint/support triangles. None states this arbitrary-coefficient
  internal-Hom triangle with the required endpoint comparisons. Existing
  supportedKernel is abelian-group-valued; formalClosedSupportSheaves is for
  pro-etale condensed module objects. Neither is a duplicate of this constant
  ModuleCat A étale construction.

Validation: required scompile.py checks of both sandbox and module names passed,
4.5/4.3 seconds in the final import-complete run, no errors or warnings. A
separate printed-signature probe confirmed that the full theorem explicitly
quantifies A with only CommRing A. Probe commands were removed from the module.
No statement correction or disputed assertion.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer FIX

The sorry'd helper `perEtaleClosedDirectImage_exact` duplicated the proved upstream instance
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite` (module
`WeilConjectures.SixFunctors.Finite.Exact`, recorded in sk-lem-pbc-finite), which applies to
closed immersions via Mathlib's `IsClosedImmersion → IsFinite` instance. The helper is removed,
the module is imported publicly and the declaration list is updated. The statement is unchanged.
