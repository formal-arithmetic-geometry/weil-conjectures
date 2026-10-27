## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeSectionImageFlatFP` states
`AlgebraicGeometry.Scheme.Modules.relative_section_image_flat_fp`, with one `sorry`.
Its other declarations are actual definitions unpacking the maps and clauses of this
one theorem. No independent mathematical existence theorem is used to choose data.
The item's informal statement, proof, source and proof dependencies are unchanged.
Its statement dependencies gain seven already-landed definition owners, listed below.
No new nodes or dependency repairs are needed.

### Hypothesis-by-hypothesis reading

| Node hypothesis or specified object | Lean rendering |
| --- | --- |
| Any scheme S and f:Y→S | `{Y S : Scheme.{u}} (f : Y ⟶ S)`; no Noetherian or reduced hypothesis |
| Proper, flat, finitely presented | `[IsProper f] [Flat f] [LocallyOfFinitePresentation f]`; properness already supplies quasi-compactness and quasi-separatedness, so this is finite presentation |
| Nonempty geometric fibres, pure dimension one | `hfibres`, with `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, every `t : Spec (.of Ω) ⟶ S`, `Nonempty` of the actual scheme pullback, and the recorded `Scheme.IsPureDimension 1` |
| Invertible M | `(M : Y.Modules) [M.IsInvertible]` |
| f_*O_Y = O_S universally | `hO`: the section-normalized adjunction unit at the unit module for every `pullback.snd f g`; the canonical pullback-unit isomorphism identifies its target with the direct image of O. Taking the identity base change includes the original map |
| Every positive tensor power has no positive geometric-fibre cohomology | `hvanish`, quantifying `j i : ℕ`, `0 < j`, `0 < i`; `RingedSpace.moduleCohomology` is used, on the actual pulled-back line and its tensor power |
| A_j=f_*M^j finite locally free for j≥1 | `hfinite : ∀ n, ((pushforward f).obj (M.tensorPow (n+1))).IsFiniteLocallyFree`; n+1 ranges over exactly the positive integers, allowing varying rank on S |
| Canonical comparison is an isomorphism after every base change | `hbc`, the existing `moduleBaseChangeMap` at the canonical pullback square for every `T`, `g`, positive `j`. Its target uses pullback of M^j, canonically identified with M_T^j by the recorded power comparison |
| Surjective evaluation f^*A_1→M | `heval : Epi (relativeImageEvaluation f M)`; evaluation is the normalized adjunction counit |
| The graded section algebra A | `(A : RelativeSectionAlgebra f M)` uses the existing affine-basis presentation; its `sectionEquiv`, `smul`, `one`, `mul`, `restriction` specify exactly the sections, scalars, unit, products and restrictions. This is a presentation of the stipulated canonical algebra, not an arbitrary extra algebra hypothesis |
| All section multiplication maps Sym^j A_1→A_j are onto | `phi` is a morphism of the existing canonical symmetric graded algebra, `hphi` fixes its degree-one generators by actual sections, and `hsurj` says its affine section algebra maps are surjective. For a graded map this is equivalent to degreewise surjectivity, and for quasi-coherent modules the affine section test is equivalent to sheaf surjectivity. The degree-zero condition follows from hO and hence imposes no extra condition |
| Evaluation h on geometric fibres | `h`, `wh`, `hcanonical` specify the global projective-bundle evaluation, using the recorded homogeneous-fraction canonical-map predicate. `relativeImageFibreMap ... t` is its actual base change. This uses the canonical identification P(A_1)_t=P(A_1⊗Ω), supplied by symmetric algebra and relative Proj base change, rather than a new projective space |
| Kernel-defined scheme-theoretic image Z_t and h_*O=O_Z on the ambient space | `himage` uses Mathlib `h.image = h.ker.subscheme` and `h.toImage`; bijectivity of `h.toImage.app U` for every image open U is exactly its canonical structure-sheaf isomorphism. Pushing this isomorphism along the closed immersion is the stated module equality on the ambient projective bundle. No reduction or topological-image replacement occurs |
| R^i h_*O=0 for i>0 on every fibre | `hhigher`, using `(pushforward h_t).rightDerived i`, the actual derived functor on module sheaves and the unit source module |

The degree-one module is written as `f_*(M.tensorPow 1)`. The recursive convention is
`M.tensorPow 1 = M ⊗ O`, so its right unitor gives exactly the node's A_1=f_*M.
Evaluation targets `M.tensorPow 1`, and the final twist comparison targets M itself.
This retains the section algebra's literal degree-one component without silently
identifying distinct Lean types. The geometric-fibre conditions are transported through
the same canonical right unitor. All schemes, fibre fields and module sheaves have the
project's common universe u; no independent smaller field universe makes hypotheses vacuous.

### Conclusion-by-conclusion reading

| Node conclusion | Lean rendering |
| --- | --- |
| X=Proj_S A | `A.data.relProj`, the recorded canonical gluing construction |
| Flat and finitely presented over S | The first four conjuncts of `RelativeImageGeometry`: `Flat`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` of `A.data.relProjHom` |
| The symmetric quotient defines a closed immersion X→P_S(A_1) | `IsClosedImmersion (Scheme.GradedAlgebraData.relProjMap phi ...)`; the map is the actual functorial Proj map of the generator-normalized quotient |
| Evaluation defines a proper surjective S-map q | Existential `q`, `wq`, then `A.IsCanonicalMap q ∧ IsProper q ∧ Surjective q` in `RelativeImageGeometry` |
| q composed with the immersion is h | The displayed equation `q ≫ relProjMap phi ... = h` |
| q^*O_X(1)≅M | The final clause of `RelativeImageGeometry`: choose normalized `TautologicalQuotient D` for P(A_1), `Classifies D ... h` fixes its evaluated generators, and pull its line first along the quotient closed immersion and then along q, with an isomorphism to M. For a degree-one-generated quotient this restricted normalized projective twist is O_X(1); the normalized affine charts are part of D, rather than an arbitrary line |
| X_t=Z_t as a closed subscheme | `RelativeImageGeometricFibres` supplies `e : pullback X/S t ≅ h_t.image` and requires its composite with the image closed immersion to be the actual base change of `relProjMap phi` |
| q_t is h_t factored through its image | The second equation in that predicate is `q_t ≫ e.hom = h_t.toImage` |
| Arbitrary base change of the construction and comparisons | `RelativeImageArbitraryBaseChange`: supplies the section algebra B, the existing `PullbackData b` and `c` for A and Sym(A_1), the generator-normalized quotient psi, and maps q',h'. `RelativeImageBaseChangeSections` fixes every coefficient map by actual section pullback in every degree, including zero. `PullbackData.isPullback` makes its relative-Proj comparison cartesian for arbitrary g. The coefficient quotient square, q square, h square, and immersion square are explicit equations. `RelativeImageGeometry` is asserted on B with its normalized line/evaluation comparison, thereby fixing the pulled-back twist comparison on every generator |
| Isomorphisms of (Y/S,M) | `RelativeImagePairIsomorphisms` quantifies every `Y'`, `f'`, module `M'`, `e : Y' ≅ Y` over S, and arbitrary `l : e^*M ≅ M'`. It supplies the graded section-algebra iso b and symmetric-algebra iso c, the quotient and evaluation data for the new pair, their commutative quotient and immersion squares, the q and h squares, and the actual section formula using the tensor power of l. It includes automorphisms of M and the identity isomorphism, rather than only the special case M'=e^*M |

The coefficient and quotient normalizations determine the symmetric comparisons as well:
on degree one, psi is the identity under the section equivalence, so the quotient square
fixes c on all generators; scalars are already fixed by the graded-algebra interface.
The tautological quotient and its classifying isomorphism are normalized on these same
generators, which is why the twist comparisons in the naturality clauses are canonical.

### Dependencies and searches

Original dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom category.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`,
  `tensorPow`, `tensorPowAddIso` and the unit convention.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSection`, `tensorPullbackSectionAdjunction`.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`;
  its equivalent quasi-coherent affine-basis form is the already recorded
  `Scheme.GradedAlgebraData` used by relative Proj, rather than a private algebra structure.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`: `GradedAlgebraData.relProj`,
  `relProjHom`, `relProjι`, used on the recorded affine-basis data.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: the existing convention
  `IsProjectiveBundle`, whose projective bundle is precisely the canonical symmetric Proj
  used here, through `SymmetricAlgebraSheaf.gradedAlgebraData`.

Seven landed definition owners added to `stmt_deps`:

- `def-sfb-relative-section-algebra-canonical-map`: module
  `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`, `RelativeSectionAlgebra`
  and `RelativeSectionAlgebra.IsCanonicalMap`.
- `def-trf-canonical-symmetric-graded-algebra`: module
  `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`,
  `SymmetricAlgebraSheaf.gradedAlgebraData`.
- `def-sfb-module-base-change-map`: module
  `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`, `moduleBaseChangeMap`.
- `def-sc-ringed-space-module-cohomology`: module
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`, `RingedSpace.moduleCohomology`.
- `def-sc-tensor-pullback-power-comparison`: module
  `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`, `boundaryPullbackPowIso`.
- `def-sfb-tensor-power-pullback-comparisons`: the same upstream module, `boundaryTensorPowIso`.
- `def-sfb-relative-proj-iso-of-graded-iso`: module
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`, `relProjIsoOfIso`.

Other used existing interfaces are `TautologicalQuotient`, `Classifies`, `IsCanonicalMap`
from `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData`, `PullbackData` and its
`relProjComparison` from `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`,
`relProjMap` and its irrelevant-ideal condition from the functoriality module, and
Mathlib `Scheme.Hom.image`, `imageι`, `toImage` in
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`. Finite local freeness is the existing
`SheafOfModules.IsFiniteLocallyFree`; it implies quasi-coherence and uses varying finite
local rank. The proof-dependency modules with usable recorded declarations are imported
privately, including the upstream closed audit for `sk-lem-picard-cech-computes` in
`Cohomology.Affine.Leray` and `Cohomology.Affine.LerayNatural`.
`lem-sfb-projective-space-pseudocoherence-twist-test` has no recorded module or upstream
closed audit, so there is no import for that proof-only dependency yet; its use remains
in the theorem's complete proof docstring. It is unnecessary to type this statement.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: “Relative Proj of section algebra of invertible sheaf flat finitely
  presented image proper morphism”: eight hits, including `Proj`, `Proj.fromOfGlobalSections`
  and properness of finite-type Proj; none states this relative-image consequence.
- Loogle: `AlgebraicGeometry.Proj, AlgebraicGeometry.Flat,
  AlgebraicGeometry.LocallyOfFinitePresentation`: zero hits.
- Mathlib grep: `sectionAlgebra|SectionAlgebra|relativeSectionImage` in AlgebraicGeometry:
  zero hits.
- LeanSearch: “relative Proj flat finitely presented scheme theoretic image section algebra”:
  eight foundational hits (`Proj`, `Flat.mk`, `toImage_app`, `finitePresentation_appLE`,
  `fromOfGlobalSections_resLE`, `flat_iff`, `fromOfGlobalSections_preimage_basicOpen` and
  `sectionInBasicOpen`); none is the full statement.
- rg in `lean/WeilConjectures` for the item id: no match; rg for section-algebra names
  and canonical Proj interfaces: relative Proj and graded sheaf infrastructure found.
- rg in `lean/Sheaf` for `sectionAlgebra|SectionAlgebra|relativeSectionImage` found the
  existing `RelativeSectionAlgebra` via the ample criterion, and the downstream
  `LogCanonicalDeletionAlgebra` using it. Read these definitions and reused them.
- DAG search located the existing definition owners above. No new notion was introduced
  where a matching definition node already exists.

Read the current node's ten proof steps and the local Stacks sources at 068A, 0B6G,
0A1H, 0B91, 01O4 and 01O9. In particular 0B6G itself is Noetherian, whereas 0A1H/0B91
supply the stated arbitrary-base perfect-base-change input. No Noetherian assumption
was introduced. The current blueprint latest directory supplies the upper six-functor
route; this item is the independently formulated lower relative-image consequence,
not the statement of a blueprint unit.

### Edge cases and validation

- Empty S: no nonempty-base assumption or positive global rank is imposed; all geometric
  conditions are vacuous and all constructions and squares still type.
- Empty Y over a nonempty S violates the explicit nonempty geometric-fibre hypothesis;
  it is not accidentally excluded by a rank binder instead.
- Variable rank and rank zero over empty opens are allowed by `IsFiniteLocallyFree`.
- M=O is permitted when the stated acyclicity holds; the image may have dimension zero.
  No dimension condition on the image or flatness of evaluation h or q is assumed.
- Positive j and i are tested explicitly. There is no H^1(O_Y)=0 hypothesis:
  degree-zero higher cohomology remains unrestricted.
- Nonreduced and non-Noetherian S, arbitrary characteristic, nonflat base changes, identity
  base changes, and arbitrary isomorphisms of the line are retained.
- Image means the kernel-defined scheme image, never its reduced subscheme.
- All implicit variables and universes are explicitly bound; autoImplicit and
  relaxedAutoImplicit are both false.
- `scompile.py Q17 lem-sfb-relative-section-image-flat-fp .../RelativeSectionImageFlatFP.lean`
  compiles both sandbox and library forms. No global build or direct git command was run.
  Initial probes exposed namespace shadowing of scheme pullback and one nonexistent
  Mathlib import. Those were repaired by explicit `Limits.pullback (C := Scheme.{u})`
  and removing the nonexistent import; no definition or hypothesis was weakened.

No STATEMENT-DISPUTED issue or source-based statement correction is needed.

## Second reading by Q17

I reread the completed module against the unchanged node, serially in this worker,
as the dispatch brief prohibits starting another agent and assigns independent review
to the maintainer. This is a second pass, not a claim of an independent worker review.
The tables above record every hypothesis and conclusion checked. In this pass I added
explicit symmetric-quotient, evaluation and immersion comparison squares under pair
isomorphisms, including an arbitrary line isomorphism `l`, rather than limiting the
comparison to the pullback line. I also checked that `M.tensorPow 1` retains the node's
M up to its canonical right unitor, that the degree-zero hypothesis is universal without
asserting degree-zero acyclicity, and that the scheme images retain nilpotents. No
mathematical clause is changed. The only theorem has a full ten-step proof docstring
and `sorry`; all helper definitions have actual data and are listed in lean.declarations.

Delivery dry run passed preflight and per-file compilation at 633ff3ef3df; the final
docstring also lists the exact DAG dependencies used in each of its ten proof steps.
