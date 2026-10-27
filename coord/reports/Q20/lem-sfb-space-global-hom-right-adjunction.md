## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGlobalHomRightAdjunction` states
`AlgebraicGeometry.AlgebraicSpace.globalHomRightAdjunction`, with `sorry` as its
entire proof. Six helper definitions construct the specified canonical comparison
and its source and target bifunctors. No theorem is proved and no data are sorried.

Source checked: `literature/stacks-project/spaces-duality.tex`,
`lemma-iso-global-hom` (Tag 0E59), and `equation-sheafy-trace` immediately preceding
it. The current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, (3),
provides the enclosing supporting route; this item is not a unit statement.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; spaces are the existing `AlgebraicSpace S`.
  `Y : Over S` and `e : Y.left ≅ Spec (.of A)` present the affine target over that
  base. This allows every commutative ring `A : Type u`, `[CommRing A]`, and every
  base structure on Spec A; it does not impose an algebra structure absent from
  the node. `f : X ⟶ schemeSpace Y` is the given morphism.
- `hqc : CompactSpace (Point X.obj.obj)` says every open cover of the underlying
  space has a finite subcover. `hqs : X.IsAbsolutelyQuasiSeparated` is the
  existing absolute diagonal criterion, independent of whether S is separated.
- Module categories are the existing `SmallModules`, equivalent to modules on
  the original small etale site, with unchanged section universe u. All spaces'
  `HasDerivedCategory.{w}` binders specify the common localization convention
  already required by the tensor comparison. There is no equality of site object
  and arrow universes on the original etale site: the existing equivalent small
  affine skeleton supplies the small ringed site.
- `DerivedQCoh` is the full subcategory of the unbounded `DerivedModules` with
  quasi-coherent cohomology. Its predicate uses the original etale module
  `SheafOfModules.IsQuasicoherent`, transported by `smallModuleEquivalence`.
  It is not the derived category of the category QCoh.
- `T : QCohDirectImagePresentation f` supplies the restriction of the canonical
  `derivedDirectImage f`, with `T.comparison` identifying every object and map.
  `a` and `adj : T.functor ⊣ a` are precisely the chosen right adjoint and
  adjunction. This is a presentation of the functor mentioned in the statement,
  not an assumption of a different direct image or arbitrary comparison arrow.
- `X.derivedHom ⋙ affineDerivedSections A Y e X f` is exactly internal derived Hom
  followed by unbounded scalar-valued derived global sections. The former uses
  K-injective resolutions; the latter right derives Hom(O,-) with scalar action
  `affineGlobalScalar`, obtained by pullback of regular functions on affine charts.
  On Y this is the action identified with A by `e` and the Gamma-Spec isomorphism.
  The result is in ambient `DerivedCategory (ModuleCat.{u} A)`; internal Hom is
  not required to have quasi-coherent cohomology.
- `globalHomDirectImageCup` is the adjoint of the canonical pullback tensor
  comparison followed by tensor of the geometric counits.
  `globalHomDirectImageInternal` transposes cup followed by Rf_* of evaluation.
  `affineGlobalHomDirectImageMap` first applies the specified derived sections
  compositor (source-to-target orientation, i.e. inverse Leray), then sections of
  that internal comparison. These definitions give the precise equation-sheafy-trace
  construction rather than choosing an arbitrary map on derived Hom objects.
- `globalHomRightAdjunctionMap` postcomposes that comparison with the supplied
  `adj.counit.app F`. `T.comparison.hom.app P` contravariantly transports the
  first Hom argument, and `T.comparison.inv.app (a.obj F)` transports the second.
- `∃ d : globalHomRightAdjunctionSource ... ≅ globalHomRightAdjunctionTarget ...`
  says natural isomorphism in both P and F. The first conjunct specifies every
  component as exactly `globalHomRightAdjunctionMap`, for all P and F.
- The second conjunct quantifies every `j : ℤ` and every cohomology class `x`.
  Both identifications are the already constructed, representative-normalized
  `affineGlobalHomCohomology`. The equation is Rf_* of its source morphism, then
  the canonical `rightDerivedFunctor.commShiftIso j`, then the shifted counit.
  The two T comparisons only express the full-subcategory presentation. Thus it
  is exactly the formula `epsilon_F[j] ∘ Rf_*u` in the node.
- No properness, flatness, boundedness, perfectness or Noetherian assumption is
  made. The K-flat pullback appears solely in the construction of the relative
  cup and is the existing normalized derived tensor pullback.

Dependency declarations read and used:

- Mathlib `AlgebraicGeometry.Scheme` and its morphisms, `DerivedCategory`,
  `HasDerivedCategory`, `CochainComplex.IsKInjective`, and `DerivedCategory.isIso_iff`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `schemeSpace` via the
  enlarged-site construction, and the existing etale structure sheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent general-site abbreviation for Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with the
  same Mathlib quasi-coherence predicate used by `derivedQCohProperty`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly exposes the
  general `derivedInternalHomOfUniverses`; `AlgebraicSpace.derivedHom` uses that
  exact ringed-site construction, not the ordinary-module specialization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, used by the representative
  characterizations underlying the tensor and Hom-cohomology comparisons.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`: the existing
  right-derived Hom(O,-) construction; its scalar enhancement here is the landed
  `affineDerivedSections`, not an independently defined global-sections functor.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `DerivedQCoh`, `derivedDirectImage`, `QCohDirectImagePresentation`, `derivedHom`,
  `derivedDualityModel` and `smallModuleDirectImage`.
- `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `spaceDerivedAdjunction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison`:
  `SingleComplex.derivedTensorComparison`, normalized on K-flat representatives.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineDerivedSections`.
- `Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors`:
  `affineDerivedSectionsComposition`, fixed by the ordinary chart projections and
  right-derived computation maps.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalHomCohomology`:
  `affineGlobalHomCohomology`, fixed by the cocycle formula on representatives.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- Proof-only imports retain the recorded interfaces `SpaceCotangentRingMap`
  (canonical ringed-topos geometry), `RingedSiteGlobalHomDirectImage`
  (`globalHomDirectImage`, cup/evaluation/Leray and cohomology formula), and the
  upstream right-derived triangulated module (canonical commutation with shifts).
  The final detection lemma is Mathlib `DerivedCategory.isIso_iff`.

The seven added stmt_deps already exist with landed Lean records. They name the
exact derived-space, affine-sections, tensor, cohomology and absolute
quasi-separatedness interfaces used in the signature or its canonical map. No
node statement, proof, proof dependency, or existing dependency record is changed.
No new node or dependency module is needed.

Edge cases checked: the zero ring (empty affine target), empty source, zero
complexes, arbitrary unbounded complexes in both variables, positive/zero/negative
j, and nonseparated base S. None is excluded. At f = identity the tensor/counit
construction and the chosen adjunction still apply; the statement permits all
chosen right adjoints, rather than requiring the canonical identity right adjoint.
The Hom complex and scalar global sections remain unrestricted in every case.

Searches for an exact existing theorem, repeated for this delivery:

- msearch leanfinder: `Global derived Hom adjunction for the right adjoint of
  derived pushforward on quasi coherent complexes of algebraic spaces`.
  Eight hits: ordinary scheme/sheaf pullback-pushforward adjunctions and counit
  formulas. None is the derived right-adjoint global-Hom theorem for spaces.
- msearch loogle: `DerivedCategory, Adjunction` returned no hits (unknown
  identifier Adjunction); the corrected quoted query `"DerivedCategory",
  "Adjunction"` returned zero hits.
- msearch grep: `[Gg]lobal[Hh]om.*[Aa]dj|[Rr][Hh]om.*[Aa]dj|[Aa]dj.*[Rr][Hh]om`
  in Mathlib AlgebraicGeometry returned zero hits.
- rg in upstream `WeilConjectures/AlgebraicGeometry` and CategoryTheory found
  `GlobalHomAdjunctionIso` and `MixedGlobalHomAdjunctionIso`: scheme-only
  constructions, with different endpoints; these cannot state the algebraic-space
  result. The exact node-id search in WeilConjectures returned no match.
- rg in `lean/Sheaf` found `SpaceAffineGlobalTraceAdjunction` (only target O_Y),
  `SpaceAffineHomComparison` (base-change comparison), and the general ringed-site
  comparison. Their definitions are used; none states this right-adjoint theorem.
- Full-name searches across Mathlib, WeilConjectures and Sheaf found no collisions
  with any of the seven declarations introduced by this module.

Validation: scompile.py checked the module against the live server library in both
sandbox and final module contexts, with no errors or warnings (4.2 s and 4.0 s).
There is one postponed named theorem, with the complete DAG proof in its docstring.
No statement dispute or source correction was needed.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
