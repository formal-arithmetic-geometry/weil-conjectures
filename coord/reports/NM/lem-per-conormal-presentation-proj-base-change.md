## Worker report

Item: `lem-per-conormal-presentation-proj-base-change`, group NM, stage 2.
Module: `Sheaf.AlgebraicGeometry.ConormalPresentationProjBaseChange`.
Main declaration:
`AlgebraicGeometry.ConormalPresentation.conormalPresentation_proj_baseChange`.

The module states the modified-blowup comparison in ILO, Exposé XVI,
the project server–the project server. The source was read directly from
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
printed pp. 229–230 (PDF pages 235–236). In particular the defining square,
the quotient by I, the degree-one generation argument, and the arbitrary
base-change proposition are all present there. The twisting-line clause is
rendered by its degree-one homogeneous-section normalization, also covering
the distinguished section (1,0) on the complement. No statement correction
was needed; no new independent notion or dependency repair is introduced.

Only the main theorem has a `sorry`. Its docstring records all twelve proof
steps of the node. Structures in its signature describe the specified
objects and comparisons by equations, rather than imposing their existence
as extra hypotheses. The first two conjuncts assert existence of those
objects for every original input and every original base morphism. No model
is selected by a definition from the postponed existence theorem.
`symmetricComparison` selects only the uniquely determined extension under
the existing symmetric-algebra universal property.

### Hypotheses and constructions

All names in this table without a namespace prefix are in
`AlgebraicGeometry.ConormalPresentation`.

| Node text | Lean rendering |
| --- | --- |
| Closed immersion i:Y→X | `Datum.X`, `Datum.Y`, `Datum.i`, and `[Datum.closed : IsClosedImmersion i]`. |
| X and Y Noetherian | `[Datum.noetherianX : IsNoetherian X]` and `[Datum.noetherianY : IsNoetherian Y]`. These give the required locally Noetherian instances too. |
| E finite locally free on Y | `Datum.E : Y.Modules` and `SheafOfModules.IsFiniteLocallyFree.{u,u,u}`. This uses the existing variable-rank notion, not a constant-rank or positive-rank hypothesis. |
| E surjects onto I/I² | `Datum.q : E ⟶ ConormalGradedAlgebra.piece i 1`, with `[Epi q]`. The recorded `piece i 1` is tensor pullback of the ideal module. |
| I is the immersion ideal | `i.ker`; its powers and their actual inclusions are `ConormalGradedAlgebra.power` and `powerInclusion`. |
| Sym(E)→gr(I) | `symmetricComparison D`, the unique symmetric extension of `D.q ≫ (ConormalGradedAlgebra.presentation D.i).inclusion 1`. |
| Aₙ is the specified fibre product | `Model.pairs`: a pair (r,b) occurs in degree n iff b is in the existing symmetric degree n, and r has an ideal-power representative whose conormal class equals the image of b. |
| No extra elements of Aₙ | `Model.injectivePair` makes the pair coordinates jointly injective. Thus the range condition specifies the fibre product, rather than only a surjection onto it. |
| Multiplication on pairs and the direct-sum grading | `Model.first` is a morphism to the actual Rees graded algebra; `Model.second U` is a ring homomorphism. `algebra : X.GradedAlgebraData` supplies the actual internal graded decomposition, scalar structure, and degreewise quasi-coherent restrictions. `second_scalars` and `second_restriction` impose the other coordinate's scalar and restriction formulas. |
| B=Proj_X A | `Model.algebra.relProj`, with the existing `relProjHom` and `relProjι`; no independent scheme is substituted. |
| P(E) over Y | `Model.closedIso`, `closedIso_over`, and `closedIso_formula` identify `pullback D.i algebra.relProjHom` with the existing canonical `SymmetricAlgebraSheaf.gradedAlgebraData D.E` relative Proj. The local maps are exactly the second projection on sections. |
| B restricts to X\Y | `complement D` is the actual open complement of the closed immersion; `Model.outside` asserts that the structural projection over it is an isomorphism. |
| Arbitrary v:X'→X with X' Noetherian | The second conjunct quantifies over every `X' : Scheme.{u}`, `[IsNoetherian X']`, and `f : X' ⟶ D.X`, and supplies `D'` and `BaseMap D' D` with `D'.X = X'` and `HEq v.f f`. There is no flatness, affineness, or finite-type assumption. |
| Y'=X'×_X Y and v_Y | `BaseMap.g` and `BaseMap.square : IsPullback D'.i g f D.i`. This permits the usual unique isomorphism from a chosen fibre product. The ideal I' is consequently `D'.i.ker`, the actual base-changed immersion ideal. |
| E'=v_Y*E | `BaseMap.moduleMap` is the adjoint pushforward form of the pullback identification; `BaseMap.pullbackModule` says its adjoint under the recorded section-normalized tensor adjunction is an isomorphism. |
| Canonical E'→I'/I'² | `BaseMap.conormalMap`, `conormal_representatives`, and `conormal_square` specify the map on ideal representatives and require the square with q and q' to commute. These fields exclude an unrelated conormal map or presentation. The existential base-change conjunct asserts such data for every original f. |
| A' and B' by the same formula | `Model D'`, universally quantified together with `Model D` in the comparison conjunct, uses precisely the same pair construction. |

### Conclusions and canonicity

| Node clause | Lean rendering |
| --- | --- |
| Natural graded map v*A→A' | `Comparison.map` gives its affine semilinear form. `scalars` specifies base-ring transport, `first_formula` applies the base ring map to Rees polynomial coefficients, and `second_formula` uses `symmetricMap`. The latter is fixed by `symmetric_scalars` and `symmetric_generators`, using the given pullback identification of E. Together with joint injectivity and the recorded restriction formulas these specify the canonical sheaf map. |
| Surjective in every degree | `Comparison.surjective_degree` says the image of the degree-n map spans the target over Γ(X',U'). This is exactly surjectivity of its scalar-extended linear map Γ(X',U')⊗Γ(X,U) Aₙ(U)→A'ₙ(U'), since pure tensors map to scalar multiples of those images. It does not incorrectly require the unextended ring map to be surjective. |
| h:B'→X'×_X B | `Comparison.h` has exactly this target; `h_fst` and `h_snd` fix both projections. `c`, `over` and `proj_formula` fix its second projection as the morphism induced by the specified graded map on every affine Proj chart. |
| Closed immersion | `Comparison.closed : IsClosedImmersion h`. |
| Isomorphism over X'\Y' | `Comparison.outside` is `IsIso` of the base-change projection of h to the open inverse image of `complement D'` in X'×_X B. |
| Canonical isomorphism on inverse-image closed subschemes | `Comparison.closedFibre` is `IsIso` of the base-change projection of h over Y'. `Model.closedIso_formula` identifies both closed fibres with P(E) and P(E'); `Comparison.proj_formula` and `symmetric_generators` fix the induced map as the canonical P(E')→Y'×_Y P(E). |
| Locally nilpotent immersion ideal | `Comparison.locally_nilpotent`: every target point has an affine neighbourhood U and an integer n>0 such that `h.ker.ideal U ^ n = ⊥`. The exponent is local, not a single global uniform bound or just pointwise element nilpotence. |
| Universal homeomorphism | `Comparison.universalHomeomorphism : (topologically IsHomeomorph).universally h`, using the recorded existing definition. |
| Degree-one twisting sheaves | `Model.twist.line` has affine identifications with the existing `Proj.twist (A.grading U) 1`. `twistRestriction` fixes their gluing by homogeneous-section-normalized restriction maps. `Comparison.lineIso` pulls back the global line along c, i.e. equivalently along h followed by the second projection. |
| Canonical line identification and complement trivialization | `NormalizedTwist` requires that the actual pulled-back homogeneous section associated to every a∈A₁ is sent to the section associated to its image, using `Proj.unitToTwist` and the actual `tensorPullbackSection`. `TwistCompatibility` and `Comparison.line_formula` impose that normalization on the global line comparison. In particular, on the complement the degree-one element t=(1,0) maps to t'=(1,0) by the two pair-coordinate formulas. Its homogeneous section is the canonical invertible section there, so this condition preserves the exact canonical trivializations, not merely the underlying line bundles. |
| Canonical comparisons | The fourth conjunct states uniqueness of c and of its normalized line identification for any two comparisons with the same input data. The pair formulas determine the underlying graded maps. |
| Respect identities | The fifth conjunct gives the identity graded map, identity Proj map, and the recorded `tensorPullbackSectionId` line identification when f, g and the module map are identities. |
| Respect composition | The final conjunct identifies the local graded map with the composite map, c with the composite Proj map, and the line isomorphism with the composite transported through `tensorPullbackSectionComp`. The hypotheses simply identify the direct base map with the composite; they are not restrictions on the original allowed base morphisms. |

### Dependency declarations used

The statement-dependency nodes and their records were read, followed by the
actual source signatures/docstrings. Current relative-Proj and tensor-pullback
sources missing from the older checkout were read using `scompile.py --source`.

- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` and `Scheme.Hom.isClosedEmbedding`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; the node's stronger global
  Noetherian input is `AlgebraicGeometry.IsNoetherian` in the same module.
- `def-amb-finite-locally-free-module`:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank` and its variable-rank companion
  `SheafOfModules.IsFiniteLocallyFree`. The latter is necessary because the
  item does not assume globally constant rank.
- `lem-pur-conormal-graded-algebra`:
  `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`, `power`, `powerInclusion`,
  `piece`, `representative`, `homogeneousClass`, and `presentation` in
  `AlgebraicGeometry.ConormalGradedAlgebra`.
- `lem-weil-pbc-symmetric-algebra-sheaf-construction`:
  `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`,
  `AlgebraicGeometry.SymmetricAlgebraSheaf.algebra`, `sections`, `restriction`,
  and `sectionMap`. Its uniquely specified extension is the existing
  `exists_quasiCoherentSymmetricAlgebra_core` in
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`.
- `def-nagata-relative-proj`:
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`,
  `AlgebraicGeometry.Scheme.GradedAlgebraData.relProj`, `relProjHom`,
  `relProjι`, `relProjFunctor_map_relProjι`, and `GradedAlgebraData.Hom`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  together with `CategoryTheory.IsPullback`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`,
  `tensorPullbackSection`, `tensorPullbackSectionComp`,
  `tensorPullbackSectionId`, and the imported existing `tensorPullback`.
- `def-weil-pbc-proj-twisting-sheaf`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`,
  `AlgebraicGeometry.Proj.twist`; and `Proj.unitToTwist` in the associated
  `Twist.UnitToTwist` module.
- `def-trf-projective-bundle-morphism`:
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`,
  `AlgebraicGeometry.IsProjectiveBundle`. Its projective bundle uses the
  existing `AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData`,
  defined in `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra` and
  publicly imported by that dependency. The same relative Proj is used here;
  no second projective-bundle construction is introduced.
- `def-weil-universal-homeomorphism`:
  `Mathlib.CategoryTheory.MorphismProperty.Limits`,
  `CategoryTheory.MorphismProperty.universally`, specialized to
  `AlgebraicGeometry.topologically IsHomeomorph` as its record prescribes.

The existing `Scheme.IdealSheafData.reesData` in
`WeilConjectures.AlgebraicGeometry.RelativeProj.Rees` supplies the first
pair coordinate, the actual powers of I with graded multiplication. The
stated proof dependencies are explicitly imported with ordinary imports
when they are not already public signature dependencies, including the
recorded arbitrary relative-Proj base change, surjective graded functoriality,
quasi-coherent symmetric algebra, affine pullback sections, kernel and sum
quasi-coherence, tensor right exactness, Nakayama, finite-type Noetherian
permanence, radical powers, homogeneous localization, and chart gluing.

### Edge cases checked

- Degree zero is included in `Model.pairs` and `surjective_degree`; the
  symmetric degree-zero submodule is range(ι)^0, and the pair formula gives
  A₀=O_X. No positive-degree-only quantification is used.
- Rank zero and varying rank are allowed. For Y=X and E=0 the relative Proj
  is empty; the line conditions on empty charts are legitimate and no
  nonemptiness or chosen frame is assumed. For rank-zero E supported on a
  proper closed subscheme, the complement can still be nonempty.
- Empty X, X', Y and empty complements are allowed; all local nilpotence
  and affine-chart conditions have the correct empty cases.
- When Y is empty the pair algebra is O_X[t]; t=(1,0) is retained by the
  first-coordinate formula and gives the complement trivialization.
- When Y=X and E is nonzero, the model is the canonical symmetric relative
  Proj. The closed-fibre comparison is the ordinary projective-bundle
  base-change isomorphism, including nonconstant rank.
- Nonflat arbitrary base changes are included; only the scalar extension
  of the graded map must be onto. No injectivity or graded-algebra
  isomorphism is asserted for a nonflat base morphism.
- No characteristic or invertibility assumption is introduced: this is the
  algebraic modified-blowup statement, independent of the later torsion
  coefficient hypotheses for Gysin classes.
- Every universe and variable is bound explicitly. Schemes, section rings,
  and modules use the common scheme universe u, while the Zariski site's
  morphism universe is u, as required by the current LocallyFree API.

### Searches and duplicate check

The preserved `searches.jsonl` contains the actual msearch results from the
interrupted work:

1. Loogle, `conormal, Proj, baseChange`: unknown identifier `conormal`, no hits.
2. LeanFinder, `Nil immersion comparison arbitrary base change Proj conormal
   presentation modified blowup symmetric algebra`: eight hits, chiefly
   `Proj.pullbackAwayιIso` and its chart formulas; no modified-blowup theorem.
3. Mathlib grep, `conormal|[Nn]il[Ii]mmersion|[Mm]odified[Bb]low` in
   AlgebraicGeometry: no hits.
4. LeanSearch, `relative Proj twisting sheaf base change nil immersion
   conormal presentation`: eight hits concerning ordinary Proj,
   presentations and immersion stability, none this fibre-product algebra
   and its nil-immersion comparison.

Local `rg` searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
`/home/ubuntu/weil-newtargets-shared/lean/Sheaf`, Mathlib, and
`dag/lean_names_upstream.json` found conormal flat-base-change lemmas,
ordinary Proj base-change results and symmetric presentations, but no
statement of this modified-blowup construction. The exact item identifier
and proposed namespace/declarations had no duplicate. The existing Rees,
conormal, symmetric, relative-Proj and twisting definitions were reused.
There is no `STATEMENT-DISPUTED` issue and no node-field correction.

### Validation

After fixing the finite-local-freeness universe parameters, making the Rees
polynomial coercions explicit, and explicitly typing the pullback scheme's
point binder, the final module compiled cleanly via the required
`scompile.py NM lem-per-conormal-presentation-proj-base-change ...` wrapper:
sandbox 17.4 seconds, library-name check 16.4 seconds, no errors or warnings.
The two unused binder warnings from the earlier draft were removed by naming
those proof arguments `_h` and `_hy`. There are no file-local instances,
notations, private declarations, or data sorries. All Lean lines have length
at most 100. Dry-run and delivery results follow below when available.

The first dry run passed server preflight and compilation (temporary commit
`6ad66d61a6`, nothing pushed). The final import pass makes every recorded
statement dependency's module a direct public import; a fresh dry run checks
that exact final packet before delivery.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
