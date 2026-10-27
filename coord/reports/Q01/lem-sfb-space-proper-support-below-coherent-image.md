## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceProperSupportBelowCoherentImage`
states `AlgebraicGeometry.AlgebraicSpace.properSupport_below_coherent_image`.
Its only proof is `sorry`. No definition or theorem has been duplicated.
The natural-language statement, proof and source are unchanged.

Source read: `literature/stacks-project/spaces-perfect.tex`,
`lemma-direct-image-coherent-bdd-below` (Tag 0D0R), lines 1220 onward.
This is the source's specialization S = Y, with properness only of each
cohomology support. Its truncation proof is reproduced step by step in the docstring.

Hypothesis and conclusion correspondence:

- The Noetherian scheme is `(Y : Scheme.{u}) [IsNoetherian Y]`.
  Mathlib's class is locally Noetherian plus quasi-compact. Locally Noetherian
  schemes have quasi-compact intersections of affine opens, so the node's
  quasi-separatedness follows; this does not require separatedness.
- `X : AlgebraicSpace Y` is the existing fppf-sheaf algebraic space over Y.
  `schemeSpace (Over.mk (𝟙 Y))` is Y as an algebraic space over itself.
  The binder `f : X ⟶ schemeSpace (Over.mk (𝟙 Y))` is its structure morphism:
  the representable sheaf h_Y is terminal on schemes over Y. Thus all such
  morphisms are the unique structure morphism; this binder supplies no
  arbitrary additional geometric map or compatibility hypothesis.
- `hf : MapIsLocally (@LocallyOfFiniteType) f` is precisely local finite
  type on every compatible pair of étale scheme charts, using the existing
  chart-test definition. There is no quasi-compactness, separatedness or
  properness hypothesis on f or X.
- Universe u is explicit. Both `HasDerivedCategory.{w}` binders specify
  localization universes, rather than geometric assumptions. The actual
  module categories are `X.SmallModules` and the analogous category for Y.
  Their defining small étale ringed models retain the original section-ring
  universe and are equivalent, by the specified restriction equivalence,
  to the existing small étale module categories. `G : X.DerivedModules`
  is an object of the unbounded derived category, not a complex chosen up
  to an unspecified comparison and not the derived category of QCoh.
- `hcoh` quantifies over every integer q and requires the inverse-equivalence
  image of H^q(G) to satisfy Mathlib `SheafOfModules.IsFinitePresentation`.
  This existing predicate is local finite presentation by finite free module
  sheaves; it implies `IsQuasicoherent`. Since f is locally of finite type
  over the locally Noetherian Y, every étale chart of X is locally Noetherian.
  Over a Noetherian affine chart R, finite R-modules are finitely presented;
  conversely finitely presented R-modules are finite. The associated
  quasi-coherent sheaf has B tensor_R M sections on affine étale charts.
  Hence this is exactly the node's coherent predicate, also on a non-qc X.
  The same reasoning on Y identifies the conclusion's predicate with coherence.
  This uses the shared predicate employed in the published algebraic-space
  coherent-module modules, not a new definition of coherence.
- `hbelow : ∃ b : ℤ, ∀ q : ℤ, q < b → IsZero (H^q(G))`
  gives exactly one lower cohomology bound. The zero object is tested in the
  small module category; the equivalence preserves and reflects it.
- For each q, `hsupport` first requires `IsClosed (moduleSupport ...)` on
  the original module topos. Its second conjunct supplies `Z : AlgebraicSpace Y`
  and `i : Z ⟶ X` with the existing representable-closed-immersion predicate.
  Every étale scheme chart of Z is `IsReduced`, and
  `Set.range (mapPoint i.hom.hom) = moduleSupport ...` fixes its point set.
  These conditions describe exactly the reduced induced closed subspace,
  uniquely up to its canonical isomorphism; no arbitrary supporting thickening
  or larger proper closed subset replaces the actual support.
  `MapIsProper (i ≫ f)` requires its map to Y to be separated, of finite type,
  and universally closed, using the recorded algebraic-space predicates.
  Z may depend on q, as required; no common proper support is assumed.
- The functor in both concluding clauses is the existing `derivedDirectImage f`:
  the canonical compatible-chart module direct image, conjugated by the specified
  equivalences and derived by K-injectives. The definition is a universal right
  derived functor, equivalent to the arbitrary-quasi-isomorphism implementation
  recorded in `def-sfb-right-derived-functor`; no arbitrary replacement functor
  or stronger resolution hypothesis is added.
- The first concluding conjunct requires finite presentation (therefore the
  specified coherence) of every H^q(Rf_*G), transported to Y's original modules.
  The second is the existence of a lower bound with all smaller cohomology zero.
  No upper bound, finite interval, uniform support, or conclusion about properness
  of f is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `Modules`, `IsRepresentableWith`, and regular-function `structureSheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsProper` (and its separated, finite type, universally closed constituents).
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `...HomologySequence`: `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice sheafification instances; `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`, `SheafOfModules.IsFinitePresentation`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  its normalized `ModuleDirectImageModel` with specified chart projections.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its normalized unit;
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
- Newly cited already-landed dependency `def-sfb-space-derived-module-calculus`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`, `DerivedModules`,
  `derivedDirectImage`, `smallModuleDirectImage`, K-injective-resolution instance;
  its recorded small-model equivalence is used to interpret all cohomology sheaves.
- Newly cited already-landed dependency `def-trf-scheme-algebraic-space`:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, `schemeSpace`.
- Newly cited already-landed dependency `def-pc-reduced-scheme`:
  `Mathlib.AlgebraicGeometry.Properties`, `IsReduced`.
- Newly cited already-landed dependency `def-sfb-proper-curve-moduli`:
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`,
  `AlgebraicGeometry.AlgebraicSpace.mapPoint`. This is the induced map on
  field-valued point classes used in `Set.range (mapPoint i.hom.hom)`
  in the proper-support hypothesis. Its owning module is publicly imported.

These four additions to stmt_deps name existing landed declarations required to
state the given objects; no node statement correction is necessary. There are no
new nodes or dependency repairs. The metatheoretic size convention has no Lean
object and is rendered by the explicit universes and the existing small models.

Proof imports retain the recorded Grothendieck-abelian theorem, negative vanishing,
standard t-structure and truncation comparison. The bounded proper-support
coherent-image proof dependency currently has no Lean record and hence no module
to import; it is not used to define the present statement and is not restated here.

Edge cases checked before writing: G = 0, X empty, empty supports of zero
cohomology, f the identity, a negative lower bound, and infinitely many nonzero
positive cohomology modules. The empty reduced closed subspace gives a proper
empty support. A non-quasi-compact disjoint union is permitted, with a different
proper support in each degree. The statement imposes no finite upper bound and
no fixed common closed subspace. The localization universe w is explicit and
there is no equality imposed between scheme object and morphism universes.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query "Derived direct image of bounded below
  coherent complex with proper cohomology supports on an algebraic space has
  bounded below coherent cohomology": eight abstract derived-category bounds
  and t-structure hits, none the algebraic-space proper-support theorem.
- `msearch.py ... loogle '"coherent", "directImage"'`: zero hits.
- `msearch.py ... grep 'proper.*support|support.*proper|coherent.*directImage|coherent.*pushforward'
  AlgebraicGeometry`: three hits, two in Modules/Tilde (affine quasi-coherent
  underived pushforward) and one in Morphisms/Basic; none the theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for proper/support and
  coherent direct images, plus the literal item id: scheme proper-support
  higher-direct-image and bounded-image results are narrower, and algebraic-space
  module-support/operations/derived-module definitions supply the needed notions
  but no matching theorem. Read `AlgebraicSpaceDerivedModules`,
  `AlgebraicSpaceSmallRingedModel`, `AlgebraicSpaceClosedCoherentModules`,
  `AlgebraicSpaceEtaleChartSupport` and `AlgebraicSpaceMorphismProperties`.
  The coherent-module files already use `IsFinitePresentation` on locally
  Noetherian spaces. No new coherence or proper-support predicate is introduced.

No STATEMENT-DISPUTED issue or source fault was found.

## Returned delivery repair

H2, returned immutable head `9fda7a37265c`: added the already-landed owning node
`def-sfb-proper-curve-moduli` directly to `stmt_deps` for
`AlgebraicGeometry.AlgebraicSpace.mapPoint`, used in the support range equality.
Added its direct public module import and the dependency declaration entry above.
The theorem signature and mathematical statement remain verbatim those reviewed
in the returned head. Compared the retained packet with the current main node:
main has no Lean record and the original fifteen statement dependencies; the
packet retains its three previously accepted landed dependencies and adds this
fourth dependency. The delivery wrapper rebases the packet on current main.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
