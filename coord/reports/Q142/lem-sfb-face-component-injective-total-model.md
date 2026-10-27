## Worker report

Stated `CategoryTheory.SemisimplicialRingedTotal.face_component_injective_total_model`
in `Sheaf.CategoryTheory.FaceComponentInjectiveTotalModel`. Its sole postponed proof
is `sorry`; its docstring records all ten DAG proof steps. All helper definitions have
real data. The resolution structures and output certificate bundle precisely this
node's inputs and conclusions; no choice of a bicomplex or comparison is made from
the existence theorem. No statement correction, dependency repair, or new node.

Hypothesis and clause correspondence:

- The small coherent face diagram is the existing `F`, `D`, `R`, `h`, `P` input of
  `SemisimplicialRingedTotal.Presentation`. `SemiSimplexCategory` is the category of
  nonempty finite ordinals and injective order maps; its opposite indexes the sites.
  `S`, `A`, and `V : AugmentationPresentation P S A` give exactly the coherent
  component and total ringed augmentations and their canonical composition maps.
- `faceExact` assumes preservation of finite limits and colimits by every existing
  `P.pullback a` ordinary module functor. `augmentationExact` does the same for
  each `V.components i`. These express exactness on the abelian module categories.
  Exactness of the total pullback is deduced in the proof, not an extra hypothesis.
- The module F in the statement is called `M`. `FaceComponentResolution P M`
  records its integer cochain complex J, the map from `singleFunctor _ 0` applied
  to M, `QuasiIso` of that map, `IsZero` in every negative degree, and injectivity
  of every evaluated term, with no injectivity assumption in the total category.
- `RF`, `η`, `hRF` specify the universal right-derived pair of the actual total
  module direct image on ordinary unbounded derived categories. This is the
  interface satisfied by the existing ambient K-injective construction. They
  specify which universal pair is being computed, and do not assume a comparison
  with the face model. `Site.hasDerived` fixes the dependency's common u+1
  localization universe. There is no bounded derived category restriction.
- `FaceComponentTotalModel.bicomplex` outputs an actual functor on complexes.
  `column` identifies its p-th column, as a complex, with
  `(a_{p,*} e_p).mapHomologicalComplex` applied to J. In particular these are the
  exact stated objects A_J^{p,q}, and the vertical differential is that of J
  under the functors, rather than an unspecified map.
- `faceCoface` is an explicit formula: the augmentation pullback compositor,
  followed by the face pullback of the component counit and the given transition,
  is transposed under the target component adjunction. `horizontal` fixes d_h to
  the sum over `Fin (p+2)` with coefficients `(-1)^i`. This uses only injective
  order maps (`homOfMono (SimplexCategory.δ i)`), with the original vertex order.
  `negative_face` makes every negative horizontal degree zero.
- Totalization is the dependency's `HomologicalComplex₂.total (.up ℤ)`, hence its
  differential is exactly d_h + (-1)^p d_v. `hasTotal` supplies its diagonal
  coproducts; `finite_diagonal` identifies them with precisely p=0,...,n, using
  the actual total inclusions and the column identifications. `total_negative`
  states zero in negative total degrees.
- `comparison M J` is an isomorphism of entire objects of D(R), from Q Tot(A_J)
  to RF(M[0]). It is not merely a cohomology comparison.
- `column_naturality` fixes the bicomplex map of any chain map w to its termwise
  component direct image. `naturality` quantifies over any f, any two augmented
  componentwise injective resolutions, and every w commuting with their
  augmentations; it states QT(w) followed by c_J' equals c_J followed by RF(f[0]).
- In `augmentation`, `G`, `K : FaceNonnegativeResolution S G` and the injectivity
  hypothesis are precisely G and its nonnegative injective resolution. The
  universal quantifiers over φ and t, and the displayed extension equation,
  include every extending cochain map, not a selected lift. `faceSingleMap`
  is the actual φ[0], with the canonical single-complex/pullback comparison.
- The existential cochain map b is fixed in every integer degree by the adjoint
  of e_0(t), using the canonical `V.component` isomorphism, then the inverse
  column coordinates and the (0,q) total inclusion. Thus b is exactly b_t.
- The final equality is Qr_K Qb_t c_J = Q(unit on G[0]) η RF(Qφ[0]). This is
  the canonical derived-adjoint equation before inverting Qr_K; Qr_K is
  invertible because K records its quasi-isomorphism. Exact-functor derivation
  identifies the localized ordinary unit followed by η with the unit of the
  normalized derived adjunction. This form retains all single-complex and
  localization transports and is equivalent to the equation in the node.
- There is no cover condition and no cartesian or quasi-coherence restriction
  on M or on the diagram. No extra nonzero or nonempty-coefficient assumption.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`:
  `CategoryTheory.SemisimplicialRingedTotal.Site`, `RingDiagram`, `Presentation`,
  `Augmentation`, `AugmentationPresentation`, their evaluation, transition,
  module pullback, adjunction and canonical composition fields. The declaration
  `semisimplicial_ringed_total_category` supplies such presentations. The existing
  presentation is passed as input, never privately reconstructed.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  used transparently by `Site.modules`, with Mathlib's `SheafOfModules` abelian
  structure. This and the following three statement dependencies are explicitly
  public-imported in the delivered file.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`; its full factors signature was read.
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution` was read. It uses natural degrees; here
  the theorem's already integer-indexed resolutions are bundled directly by
  their map, quasi-isomorphism, categorical vanishing and component injectivity.
  No second definition of injectivity or quasi-isomorphism is introduced.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and inversion of quasi-isomorphisms.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`:
  `HomologicalComplex₂`, its `total`, `ιTotalOrZero`, and the first-quadrant
  finite-diagonal convention; the recorded `firstFiltration` has the same total.
- Every recorded proof-dependency module is imported privately, including
  `ModulePullbackPushforwardAdjunction`, `SemisimplicialEvaluationFreeAdjoint`,
  `RingedSiteModulesGrothendieckOfUniverses`, `RightDerivedFunctorOfQuasiIsoResolutions`,
  `FirstQuadrantTotalComparison`, `ExactFunctorDerivedFunctor`, and
  `ResolvingDerivedAdjunction`, together with the Mathlib/enough-injective,
  bounded-below K-injective and K-injective Hom declarations and the upstream
  Grothendieck K-injective and right-adjoint injectivity modules.

Edge cases checked mathematically: zero rings and zero modules; degree zero
(the diagonal consists only of (0,0)); negative total degrees (all summands zero);
all finite vertex sets including [0]; the constant diagram (horizontal maps
alternate 0, identity, 0, identity); and arbitrary distinct resolutions and lifts.
The horizontal sign uses the omitted vertex's index, not a reversed face order.
No degeneracy is requested. The componentwise contraction in the proof does not
need to commute with face transitions. The common universe is exactly that of
the already recorded small ringed-site interface.

Searches (2026-10-24):

- `msearch.py leanfinder`, query “Derived augmentation pushforward for a
  semisimplicial ringed site is computed by the alternating face total of a
  componentwise injective resolution”: eight hits, on injective-resolution
  ordinary right-derived objects and alternating face complexes; none has the
  face-only ringed total comparison with canonical adjoint normalization.
- `msearch.py loogle`, query `"SheafOfModules", "rightDerived"`: zero hits.
- `msearch.py grep`, query `semisimplicial|componentwise.*injective|augmentation.*total`
  in CategoryTheory: zero hits. Direct rg of Mathlib homology and category theory
  found no matching statement.
- `msearch.py leansearch`, query “The derived direct image of a semisimplicial
  total module is the alternating face total complex of any nonnegative
  componentwise injective resolution”: eight hits, ordinary injective right
  derived functors and alternating face/coface complexes; none is this theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and the upstream declaration index
  for every new declaration name: no collision. Concept search found
  `NonnegativeDerivedTotalization` (strict cosimplicial constant-category diagrams),
  `TotalSiteInjectiveCechResolution` (simplicial constant-coefficient total injectives),
  and `SimplicialDerivedColimitComputation` (a projective derived colimit roof).
  Their full relevant interfaces were read; none states this ringed face-only
  componentwise-injective augmentation theorem. The item id has no upstream match.

Validation: the prescribed `scompile.py` compiled both the sandbox module and its
library module name cleanly (10.6 and 9.8 seconds). The initial elaboration issues
were repaired by using the actual `HomologicalComplex.singleMapHomologicalComplex`
namespace and making the column functor transparent to instance synthesis.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
