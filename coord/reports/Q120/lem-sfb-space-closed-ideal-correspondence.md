## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence` states
`AlgebraicGeometry.AlgebraicSpace.closed_ideal_correspondence`, with one named theorem
and its entire proof `sorry`. There are no new definitions and no copied constructions.
The source read is `literature/stacks-project/spaces-morphisms.tex`, lines 2215–2308:
Tag 03MB (`lemma-closed-immersion-ideals`), its proof, and the paragraph after
`definition-inverse-image-closed-subspace`. The node's three proof steps are included
in the declaration docstring, including right exactness, local units, and composition.

Hypotheses and clauses, in signature order:

- The base scheme is `(S : Scheme.{u})`; all spaces are `AlgebraicSpace S`, with arbitrary
  morphisms in this category. Universe `u` is explicit; no equality of site and section
  universes, smallness assumption, flatness, finiteness or Noetherian assumption is added.
- Closed subspaces up to isomorphism over X are exactly `ClosedSubspace X`, the existing
  subtype of `Subobject X` whose arrow is representable by scheme closed immersions.
  Ideals are exactly `QuasiCoherentIdeal X`, the existing quasi-coherent subobjects of
  `SheafOfModules.unit X.structureSheaf`. `corr` is a family of equivalences between these
  types, hence supplies both injectivity and surjectivity of the asserted bijection.
- The first conjunct identifies `(corr X C).val` with
  `kernelSubobject (moduleStructureMap C.val.arrow)`.
- In that same conjunct, `Q`, `q`, and `w` specify the quotient O_X/I: `w` says that q
  kills I and `Nonempty (IsColimit (CokernelCofork.ofπ q w))` is its complete cokernel
  universal property. The unique isomorphism `e` identifies Q with the actual
  `moduleDirectImage C.val.arrow` of the actual structure module on the subspace;
  `q ≫ e.hom = moduleStructureMap C.val.arrow` identifies the quotient maps.
  This does not substitute an arbitrary quotient: the universal property and quotient
  map specify it up to the unique normalized isomorphism. Using an existential universal
  cokernel avoids adding a nonexistent `HasCokernel` instance as a hypothesis.
- `unitIso X Y p` identifies tensor pullback of O_X with O_Y. The second conjunct fixes
  its hom to the adjoint of the already specified `moduleStructureMap p`, so this is the
  canonical b tensor a -> b p-sharp(a) comparison, not an arbitrary isomorphism.
- The third and fourth conjuncts normalize the natural identity and composition
  isomorphisms `idIso` and `compIso` on the existing `moduleTensorSection` tensors.
  For identity pullback the formula is b times the restricted section. For composition
  it is a tensor (b tensor m) -> a r-sharp(b) tensor m. The supplied chart morphism c is
  required to have underlying map `t.hom.left ≫ q.hom.left`, so it is precisely the
  composite chart. No global pure-tensor representation of arbitrary sections is assumed.
  These isomorphisms render the canonical tensor comparisons mentioned in proof step 3;
  they supply no additional geometric hypothesis or alternative pullback functor.
- The fifth conjunct supplies, for each C and arbitrary p, an actual `ClosedSubspace Y`
  and a map a whose square is `IsPullback a D.val.arrow C.val.arrow p`. Thus the inverse
  image is asserted to exist, and is the sheaf fibre product in the full subcategory.
- The sixth conjunct applies to every such pullback presentation, not just a chosen one.
  It identifies the ideal by an epimorphism q from p^*I onto `(corr Y D).val`, satisfying
  `q ≫ (corr Y D).val.arrow = idealTensorMap p (corr X C)`. The arrow of this subobject
  is monic, so this is the image-ideal factorization in module sheaves, as used by the
  existing correspondence dependency. It does not assert that p^*I injects into O_Y.
- The family `beta` has exactly the type p^*(i_* O_Z) ≅ i'_* O_Z'. The equation in the
  sixth conjunct is `p^*(i-sharp) ≫ beta.hom = unitIso.hom ≫ i'-sharp`, identifying the
  tensor pullback of the quotient map with the structure quotient map. The following
  quantification over every e with this equation proves uniqueness of beta.
- The final clause of that conjunct explicitly preserves algebra units: on every chart,
  beta takes b tensor i-sharp(1) to i'-sharp(b); in particular 1 tensor 1 goes to 1.
  Together with linearity and the quotient-map normalization this is the canonical
  structure-algebra quotient identification (multiplication is the quotient one).
- The seventh conjunct says that beta for the identity pullback square is `idIso.app`
  on the structural direct image. The last conjunct is the actual successive-pullback
  equation: `r^*(beta_p) ≫ beta_r = compIso.app ≫ beta_(r≫p)`. The final square is
  `k.paste_horiz h`, rather than an extra hypothesis about the composite square.

Dependency declarations used, with full source declarations and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `EtaleSite`, `structureSheaf`, `Modules`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`; the
  representable scheme-test condition is used by the recorded `ClosedSubspace`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, used
  through `X.Modules`, with Mathlib's existing sheaf-of-modules category and morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its use of
  `SheafOfModules.IsQuasicoherent`, used by `QuasiCoherentIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleChartTarget`, `moduleChartScalar`, `moduleDirectImageModel`, `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection`. Their
  normalized chart-limit and adjunction interfaces are used verbatim.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, the sheaf fibre-product universal property;
  its other two declarations `etaleCover_pullback` and `etale_fibreProduct_isScheme`
  were also read. The public import retains the specified fibre-product framework.
- The size convention has no Lean definiendum; the explicit universe and inherited
  site/section universes implement it.
- Existing additional notion nodes added to stmt_deps:
  `def-sfb-space-closed-subspace` (`ClosedSubspace`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`),
  `def-sfb-space-quasi-coherent-ideal` (`QuasiCoherentIdeal`, `idealTensorMap`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`), and
  `def-sfb-space-module-structure-map` (`moduleStructureMap`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`). These already landed;
  no definition node or dependency module is being created or replaced.
- Proof-only imports retain
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence`
  (`ideal_closedSubspace_correspondence`),
  `Mathlib.CategoryTheory.Adjunction.Limits`
  (`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`, read at lines 86–98),
  and the tensor node's recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
  `lem-trf-space-chart-adjunction-tensor-realization` has no recorded Lean declaration
  or module at the inspected base; it is a proof dependency only, so its planned use is
  recorded in the proof docstring without inventing or duplicating a declaration.

Edge cases checked mathematically before and after writing:

- Empty base or empty X: the equivalence and quotient universal property still apply;
  there is no nonemptiness binder or atlas choice in this statement.
- Zero ideal: the closed subspace is X, quotient is O_X, and comparisons reduce to the
  canonical tensor unit comparisons, without a nonzero-ring requirement.
- Unit ideal: the closed subspace is empty, quotient and structural direct image are zero;
  the explicit unit equation is valid in the zero algebra, where 1 = 0.
- Non-flat base change: pullback of I can lose injectivity (e.g. I=(2) on Spec Z,
  pulled back to Spec F_2); its map has zero image, and the pulled-back quotient is F_2.
  The epimorphic factorization encodes exactly this case, with no monomorphism asserted.
- Identity and two successive arbitrary morphisms: the statement includes both concrete
  coherence equations, not just a separate existence claim for each comparison.
- Arbitrary presentations: universal quantification over all pullback squares and unique
  quotient-normalized beta ensures no restriction to a selected fibre-product model.

Searches actually run:

- `msearch.py ... leanfinder` query: “Closed algebraic subspaces correspond to quasi
  coherent ideals and quotient structure sheaves commute with arbitrary tensor pullback”.
  Eight hits, including `IsClosedImmersion.overEquivIdealSheafData`,
  `Scheme.IdealSheafData.subschemeObjIso` and `subschemeFunctor`. These are scheme results,
  not the algebraic-space small-etale quotient-pullback statement.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.Scheme.IdealSheafData`.
  Twelve scheme hits, including `overEquivIdealSheafData` and
  `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion`; no exact match.
- `msearch.py ... grep` query:
  `overEquivIdealSheafData|cokernel.*[Ii]so|pullback.*[Qq]uotient`, in AlgebraicGeometry;
  then the narrower `overEquivIdealSheafData|ker_fst_of_isClosedImmersion`.
  The latter returned five hits in ClosedImmersion.lean and IdealSheaf/Functorial.lean,
  again for schemes, with the correspondence at line 180 and base change at line 80.
- Direct `rg` searches of `lean/WeilConjectures/AlgebraicGeometry`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for closed ideals and tensor pullback composition found
  the existing algebraic-space ideal correspondence, ideal/closed-subspace notions, and
  the separate ordinary-scheme tensor comparisons. The algebraic-space correspondence
  omits this node's quotient isomorphism and beta/coherence statements. A direct search
  for the item id in `lean/WeilConjectures` returned no declaration (no file to reuse).
  A more specific upstream `AlgebraicSpace*` glob had no files; the broad upstream
  directory searches were run as well. No exact existing declaration was found.

No statement correction or disputed mathematical clause. Initial elaboration found missing
chosen-cokernel/image instances at the small section universe; the final statement uses
universal cokernels and epi-mono image factorizations instead of restricting universes or
adding geometric assumptions. The only remaining sorry is the named item theorem.

## Second reading by Q120

This is a second pass by the same dispatched worker; no independent reader or sub-agent
was started. The maintainer's independent delivery review remains separate. I reread
Tag 03MB, the complete node and its three proof steps against the final signature. The
kernel clause uses the actual recorded structure map; the quotient includes its universal
property and unique normalized iso; beta uses the actual tensor functor and direct image;
its normalization, local unit formula, identity equation, and pasted-square composition
are all present. The image uses an epi onto a monic ideal, not injectivity of p^*I.
No hypothesis on p was added. The review repaired the representation of the quotient
and image to avoid unavailable instances, parenthesized the dependent beta family through
an explicit pullback-proof binder, and gave the ring type explicitly to the unit 1.
