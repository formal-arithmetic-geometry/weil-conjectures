## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatIsomorphismDenseOpen states
AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_of_flat_isIso_over_schematicallyDense_open.
Its sole proof is `sorry`. No definition, additional theorem, new node, dependency repair,
or statement correction is introduced.

I read the node's statement, source and all five proof steps, every statement dependency's
statement and Lean record, and the recorded declarations and docstrings. The withdrawn
CompactObject example module contains no declarations; its node now points to the upstream
WeilConjectures.CategoryTheory.CompactObject. The new module follows the current module
header and public-section conventions instead. There is no repair note for this item.
I checked the local Stacks spaces-more-morphisms.tex, lemma-zariski (Tag 0879): its
three numbered assumptions are exactly the operative assumptions below.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the same arbitrary universe `u` is used by
  `{Y T V : AlgebraicSpace S}`. No finiteness, separation, reducedness, or nonemptiness
  condition is imposed on the base or these spaces. The fixed library's algebraic spaces
  are the full subcategory of fppf sheaves with representable diagonal and an etale atlas.
- The morphisms are `(g : Y ⟶ T) (j : V ⟶ T)` in that full subcategory.
- Separatedness of g is `hsep : MapIsSeparated g`, exactly the recorded predicate that
  its relative diagonal is representable by closed scheme immersions.
- Flatness is `hflat : MapIsFlat g`, the recorded test on compatible etale scheme charts.
- Local finite type is `hlft : MapIsLocally (@LocallyOfFiniteType) g`, using that same
  chart test, with Mathlib's scheme local finite-type predicate. This is NOT the finite
  type predicate, which would additionally impose quasi-compactness of g.
- The quasi-compact open immersion j is `hj : IsRepresentableWith (fun _ _ p ↦
  IsOpenImmersion p.left ∧ QuasiCompact p.left) j.hom.hom`. This means all scheme base
  changes are quasi-compact open immersions. It is equivalent to the stated affine
  etale chart criterion: quasi-compactness is etale-local on the target and is checked
  over affine targets. For the reverse implication cover any scheme test by the inverse
  images of an etale scheme atlas; those covers admit finite refinements over each affine
  test. This is the existing formulation used in the schematic-closure theorem.
- The map `Y ×_T V → V` being an isomorphism is
  `hiso : IsIso (Limits.pullback.snd g.hom j.hom)`. This is the actual sheaf fibre product,
  not a supplied abstract object or arbitrary comparison. The recorded fibre-product
  theorem says it is an algebraic space, so the full-subcategory interpretation agrees.
- Schematic density is `hdense`. For every target etale chart U and two regular functions
  a,b, equality after pullback along every W in V.EtaleSite with a scheme morphism
  p to U over T implies a=b. The equation
  `W.obj.hom ≫ j.hom.hom = yoneda.map p ≫ U.obj.hom` expresses precisely 'over T';
  `(Scheme.Γ.map p.left.op).hom` is the actual regular-function restriction.
  These are exactly all charts of `V ×_T U`. The normalized direct image of
  def-trf-space-etale-module-functors is the limit of sections on ALL such charts.
  Its projections jointly detect equality; therefore this clause is sectionwise
  injectivity of `O_T → j_* O_V`. It does not replace schematic density by topological
  density, nor choose a map with an injectivity assumption. This sectionwise rendering
  is already used in AlgebraicSpaceQcOpenSchematicClosure.exists_qcOpen_schematicClosure.
- The conclusion `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) g.hom.hom`
  says exactly that every scheme base change is represented by an open immersion.
- No quasi-compactness of g or T, and no properness of g, is present. The initial
  quasi-compact/quasi-separated-space, ideal, finite generation, and blowup conventions
  are background definitions in the node: no such object occurs in Tag 0879's
  hypotheses or conclusion, so no artificial ideal or blowup binders are introduced.

Dependency declarations used/read:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, IsEtale, IsAlgebraicSpace, EtaleSite, etaleForget,
  structurePresheaf, structureSheaf and Modules. Structure-sheaf sections are ordinary
  global regular functions on the chart schemes.
- def-weil-size-convention is a convention-only record: explicit universe `u` realizes it.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion, used inside the recorded separatedness predicate.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally, MapIsFlat,
  MapIsSeparated; I also read the local-finite-presentation and finite-type definitions.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh (background convention).
- WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup (background convention,
  the scheme construction cited for the node's unused space-blowup convention).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: ModuleChart,
  moduleChartScalar, ModuleDirectImageModel (especially its projection and isLimit),
  moduleDirectImage, moduleTensorPullback, moduleTensorAdjunction and moduleTensorSection.
  These justify the sectionwise direct-image interpretation; no second definition is made.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback, etale_fibreProduct_isScheme.

Plain proof imports retain every currently stated proof dependency not already imported
publicly: AlgebraicSpaceFlatProperFpLocality.flat_proper_fp_locality,
AlgebraicSpaceIdealClosedSubspaceCorrespondence.ideal_closedSubspace_correspondence,
SpaceOpenImmersionEtaleLocal.isOpenImmersion_of_etale_cover,
ChartwiseEtalePermanence.chartwise_etale_permanence, and Mathlib's
IsOpenImmersion.of_flat_of_mono in Morphisms.FlatMono. Scheme etaleness is publicly
available through the recorded chart-property imports. The three proof dependencies
lem-sfb-space-flat-finite-presentation-dense-open,
lem-sfb-space-flat-pullback-schematic-density, and
lem-sfb-space-flat-monomorphism-representable have no recorded declarations in the read
snapshot: no imports can yet be added for those proof-only inputs. Their exact intended
uses remain in the docstring; no missing statement dependency requires a new module.

Edge cases checked before writing:

- Empty T: all spaces mapping to it are empty; the assertion includes this case.
- Empty V: schematic density forces every target chart's regular-function ring to
  be trivial, hence T empty; density is not silently treated as vacuous.
- V=T with j an isomorphism: the pullback hypothesis makes g an isomorphism, hence
  an open immersion; schematic density is the identity restriction.
- Nonreduced T: hdense detects nilpotent regular functions too, unlike topological density.
- Non-quasi-compact g or T remain allowed; hj concerns only the open inclusion.
- Non-Noetherian bases, all characteristics and all allowed universe levels are included.

Searches made (msearch tools were run with group Q02 and this item):

- leanfinder: 'A separated flat locally finite type morphism of algebraic spaces is an
  open immersion if isomorphic over a quasi compact schematically dense open'. Eight
  hits, principally IsOpenImmersion.of_flat_of_mono and scheme open-immersion facts;
  none is the algebraic-space dense-open criterion.
- leansearch: 'Flat separated morphism is an open immersion if isomorphic over a
  schematically dense quasi compact open'. Eight hits about scheme open immersions;
  no matching theorem.
- loogle: 'AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.Flat'. Four hits:
  Flat.instRespectsSchemeIsOpenImmersion, Flat.instOfIsOpenImmersion,
  descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact', and
  IsOpenImmersion.of_flat_of_mono. The last is the recorded proof leaf: schemes only,
  with additional mono and local finite presentation hypotheses that must be proved here.
- msearch grep: 'dense.*[Oo]pen|[Oo]pen.*dense|birational', restricted to
  AlgebraicGeometry/Morphisms. Three hits (Immersion and UnderlyingMap), none matching.
- rg of lean/WeilConjectures and lean/Sheaf for flat/dense/open and isomorphism-related
  names: scheme birational and flat-density results, no matching space theorem.
  The exact item id has no occurrence in lean/WeilConjectures.
- rg of AlgebraicSpace modules found the existing schematic-closure theorem's sectionwise
  density clause, reused as an expression rather than introducing another predicate.

No statement dispute or node fault was found.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
