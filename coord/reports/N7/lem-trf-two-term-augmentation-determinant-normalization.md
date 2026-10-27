## Worker report

The module `Sheaf.TraceFormula.TwoTermAugmentationDeterminantNormalization` states
`AlgebraicGeometry.exists_twoTermAugmentationDeterminantNormalization`, with `sorry`.
Its other declarations only unpack this node's exact-sequence data and conclusions.
No new independent mathematical notion, dependency replacement, statement correction,
or proof is introduced. The item's JSON changes only in `lean`.

Sources read: Stacks `duality.tex`, `lemma-determinant` (0E9Y), including its
relation-first formula, and `lemma-fundamental-class-lci` (0E9Z), including the
conormal-sequence construction; `more-algebra.tex`, `section-determinants-complexes`
(0FJI), through the kernel-normalized triangle preceding 0FJJ; `perfect.tex`,
`lemma-determinant-two-term-complexes` (0FJX) and `remark-functorial-det` (0FJY).
The newest blueprint's `lem-trf-local-term-locality.md` was also read: the item
is auxiliary to that node's long dependency route, not a blueprint unit statement.
There is no repair note for this item. The prescribed CompactObject example is
now a withdrawn module; its node record and the current module-mode convention
were read rather than reintroducing its withdrawn declaration.

Hypothesis and clause correspondence:

* The ring B and its finite projective modules are expressed by their associated
  module sheaves on an arbitrary affine scheme X (`[IsAffine X]` in the family N).
  This is the affine module/sheaf dictionary, not a global-freeness assumption:
  finite projective B-modules correspond to finite locally free sheaves on Spec B.
  Conversely taking global sections recovers the modules and linear maps. Using
  arbitrary affine X also includes every Spec B and isomorphic affine presentations.
  `HasAffineAugmentationRealizations` explicitly quantifies over B, U,V,W with
  Module.Finite and Module.Projective instances, i and p, injectivity, surjectivity,
  exactness, and the three constant-rank equations at every prime. It supplies S
  with terms equal to tilde U,V,W and maps HEq to tilde.map i,p. Thus applying N
  gives the claimed normalization for these exact ring modules, not just an
  unspecified affine model.
  The sheaf dual is Hom(-,O), and the tensor and exterior powers are the recorded
  sheaf constructions, so this is the same affine line and the same objects.
* `TwoTermAugmentationSequence.model` is the recorded `TwoTermDeterminantModel`:
  its neg and nonneg terms are U and V, its differential is i, and its ranks are
  a and a+d. The field `d : ℕ`, `rank_eq`, and `quotient_free` encode a,d≥0 and
  the quotient rank d. `projection` is p; `zero` and `exact : ShortExact` encode
  the whole short exact sequence, including injectivity and surjectivity. There
  is no chosen splitting and no global basis. Finite projectivity is precisely
  finite local freeness in this affine encoding.
* The existing `model.line` is `(exteriorSheaf U a).dual ⊗ exteriorSheaf V (a+d)`.
  `model.complex` is the actual double complex in degrees -1,0. `degreeZero` is
  the actual `[0 → W]` model. All derived objects use `DerivedCategory.Q` and
  the dependency's `schemeDerivedCategory` convention.
* T is universally quantified and `hT : T.IsCanonical` is the repaired
  determinant interface of `lem-trf-two-term-perfect-determinant`. Its model
  condition is the signed exact-cone normalization for every quasi-isomorphism;
  its pullback condition fixes pure-wedge scalar extension using the K-flat
  counit. This is the dependency's implementation of the node's affine-local
  kernel normalization and restriction condition, independently of this δ or θ.
* `IsOrderedWedge` gives exactly the displayed formula on EVERY open O, for
  EVERY relation tuple, quotient tuple, lift tuple and dual section α evaluating
  to 1 on the relation wedge. The tuple concatenation is `Fin.append` with
  relation images first; `Fin.cast rank_eq` only changes the length index.
  This includes every free localization and basis from the node. The slightly
  more intrinsic tuple formulation is equivalent: a decomposable top wedge
  admitting a dual evaluation 1 is a frame locally, so the local-basis formula
  also gives this formula. No exterior-factor permutation or extra sign occurs.
* `delta` is an isomorphism, not an unconstrained linear map. Its ordered_wedge
  field fixes all its local values. `Compatibilities.independent` says ANY
  isomorphism satisfying this formula is this same delta, expressing independence
  of bases and lifts. The formula itself quantifies over all of them.
* `augmentation`, `negative = 0`, and `zero = projection` pin q to `(0,p)` on
  the displayed double complexes. `quasiIso` asserts it really is a
  quasi-isomorphism. `degreeZeroExterior` is pinned by evaluation on the empty
  negative wedge, with no free scalar. `determinant` says the composite of the
  fixed exterior-model comparisons and det(q) is `delta.symm`. Every derived
  isomorphism whose hom is Q.map q is covered.
* `Compatibilities.scalar` quantifies over arbitrary morphisms g between affine
  schemes, hence arbitrary B→B', with no flatness assumption. The two term
  isomorphisms, quotient isomorphism, and commuting squares identify the target
  with the scalar-extended sequence. Its two exterior comparison predicates
  specify the usual scalar maps on pure wedges, including dual normalization;
  the conclusion is precisely the delta square. Its inverse is the square for
  det(q), by `determinant`. Isomorphisms of exact sequences are included by taking
  g to be the identity; its canonical tensor unit comparisons give the same
  formula. No isomorphism of term maps is required in the next clause.
* `Compatibilities.resolution` covers every chain map f over the same quotient W
  and rank d, with `f ≫ q' = q` expressed by HEq to accommodate equal quotient
  objects and their proof-indexed degree-zero presentations. It asserts that
  Q.map f is an isomorphism and states δ'⁻¹det(f)=δ⁻¹, using HEq only to transport
  the equal quotient and rank in the codomain. It does not assume f is termwise
  surjective or invertible, nor assume its derived invertibility as a hypothesis.
* No rank is positive. Both formula predicates use `Fin 0` and the actual zeroth
  exterior power; `degreeZero_normalization` explicitly evaluates the empty
  wedge via `Fin.elim0`. In particular a=0, d=0, and both zero are included.
* The geometric predicate binds a field k, a smooth p:X→Spec k, and
  `X.IsPureDimension d`. A regular presentation `C : FlatLCIPresentation` has
  an open ambient map to affine n-space, a closed immersion, regular generators
  of length c and n=c+d. These are exactly U0,V0,a,d in the node, localized on
  any chart U. Identity base change gives the original case, and B permits the
  base-change cases already in the stated adjunction system.
* The geometric inputs K, hK, H are the canonical adjunction system, its
  normalization and `FlatLCIAdjunctionCotangentNormalization`; they are bound
  as the recorded canonical data referred to by the node, not as arbitrary
  replacement maps. `Properties D F κ E` supplies the prescribed intrinsic
  cotangent system. The input V is the recorded `SmoothComparison`, whose beta
  is built from the canonical cotangent augmentation and empty-wedge exterior
  comparison. Both actual normalized comparisons are used in the conclusion.
* `SmoothConormalAugmentation` supplies the source differential map on universal
  differentials and exactness of the conormal sequence, with rank d. Its negative
  differential is exactly `(H.chart B U C).differential`, not a chosen map.
  The sequence's model and line are definitionally the chart's determinant model
  and C.line. The predicate supplies δ with the ordered-wedge formula and states
  `(K.localIso).hom ≫ pullback(theta).hom ≫ beta.hom = δ.inv`. This is precisely
  the smooth algebraic identification in the node on its chart line.
* The final two conjuncts apply `RingedSpace.moduleStalkFunctor` to this same
  equality and then `ModuleCat.extendScalars` along the stalk residue map followed
  by EVERY field extension ρ:κ(x)→L. L is any field in the common ambient universe;
  the universe is arbitrary, so extensions of every size are covered. The same
  maps, rather than separately chosen fibre maps, occur on both sides.

Dependency declarations read and used:

* `Mathlib.Algebra.Module.Projective`: `Module.Projective`; in the main statement
  its affine geometric incarnation is the recorded finite-local-freeness predicate.
* `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`, `exteriorPower`,
  and `ιMulti`; sheafification is the single existing `Scheme.Modules.exteriorSheaf`
  and its `exteriorSheafSection` (no duplicate exterior-power construction).
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
* `Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant`:
  `TwoTermPerfectDeterminantData.IsCanonical`, `TwoTermDeterminantModel.negativeMap`,
  `zeroMap`; the underlying model, `twoTermDeterminantIso`, `modelIso`, `model_mem`
  are the recorded determinant API. The complete repaired existence signature
  and docstring were read.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`;
  both occur in the reused `FlatLCIPresentation`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
* `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`,
  `linearMapEquivDerivation`; the geometric statement uses the recorded relative
  differential sheaves, their universal derivation normalization, and pullback.
* `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`: `FlatLCIPresentation`,
  `FlatLCIAdjunctionSystem`, `IsNormalized`, `IsSourceDifferentialMap`,
  `IsFlatLCIPullbackDeterminantComparison`, `FlatLCIBaseChange`.
* `Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus`:
  `IsKernelNormalizedDeterminantMap`, `kernelNormalizedDeterminantMap`, and the
  calculus theorem were read. The canonical determinant interface already pins
  sheaf determinant maps to this kernel construction; it is not copied here.
* `Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization`:
  `FlatLCICotangentChart`, `FlatLCIPresentation.determinantModel`,
  `FlatLCIAdjunctionCotangentNormalization`, its theta and chart fields.
* `Sheaf.AlgebraicGeometry.LciDeterminantDescentSmooth`:
  `SmoothComparison`, its empty-wedge normalization and `SmoothComparison.beta`.
  The recorded theorem and relation-first predicate were read in full.

The stated proof-dependency modules are imported (statement dependencies publicly,
proof-only dependencies ordinarily). The three remaining algebraic proof inputs
(projective quotient splitting, exterior scalar comparisons, and normalization
locality/equivariance) have respectively a Mathlib match or no recorded module;
there is no nonexistent module import. No circular import was introduced.

Edge cases checked: the zero ring (Spec B empty), the empty scheme, U=0 (a=0),
W=0 (d=0), both ranks zero, characteristic two, nonfree projective modules, nonflat
scalar extensions, and chain maps whose term maps are not isomorphisms. In each
case the formula uses empty wedges or local frames, never a determinant sign
coming from a permutation of exterior factors. Stalk and residue extensions do
not require choosing compatible bases. No node fault or disputed statement found.

Searches actually run with msearch.py, group N7 and this item:

* leanfinder: “The determinant of a two term augmentation to its projective cokernel
  is the inverse of the relation first wedge isomorphism”: eight projective
  resolution and chain-complex hits, none the augmentation determinant assertion.
* loogle: `ExteriorAlgebra.ιMulti, LinearEquiv`: one hit,
  `ExteriorAlgebra.liftAlternatingEquiv_symm_apply`; not this statement.
* grep: `augmentation.*[Dd]eterminant|[Dd]eterminant.*augmentation`: zero hits in Mathlib.
* leansearch: “Determinant augmentation of a two term projective resolution is
  inverse to the ordered wedge isomorphism”: eight hits about projective
  resolutions and exterior powers; no matching theorem.
* rg on `lean/WeilConjectures` and `lean/Sheaf`, searching the augmentation/determinant
  pattern and `IsRelationFirst|orderedWedge|OrderedWedge`: the completed-conormal
  consumer's proof docstring and the lci smooth-comparison API, not this statement.
  Literal node-id grep in `lean/WeilConjectures` found nothing. The matching
  smooth API was reused rather than redefined. The entire statement has no existing match.

All Lean compiles use the prescribed scompile.py server wrapper, in module mode.
Final standalone scompile.py validation passed for both the module-mode sandbox and
the intended library module, with no diagnostics. The delivery dry run follows.
An explicit-argument elaboration issue in the final affine realization was repaired
by specifying the base ring and both module arguments of tilde.map.
The first dry run exposed stale lean.statement metadata after the explicit affine
realization clause was added; the record is now regenerated verbatim from the
finished signature. This was a sandbox metadata issue, repaired before delivery.

## Second reading by N7

This is the dispatcher's single-worker delivery; no second agent was started.
I performed a separate clause audit with the node, dependency signatures, and
finished module open. Independent review remains with the maintainer as specified
in the brief. The audit found and removed an unnecessarily general ambient-scheme
quantifier from the affine assertion: N and its compatibilities now quantify only
on affine schemes, exactly the module case. The geometric assertion remains on
all presentation opens, as required. It also replaced a freely stored degree-zero
model by the explicit `S.degreeZero zero_rank`, so q's target and empty-wedge
normalization cannot vary, and added the full cotangent Properties hypothesis
which identifies the referenced canonical system. It checked that q is specified
by `(0,p)`, δ uses relations first, scalar extension has no flatness restriction,
the chain-map clause concludes derived invertibility, and the geometric equality
uses theta and the canonical smooth beta followed by the actual stalk and scalar
extension functors. No theorem is proved and no definition contains sorry.

Validation: deliver2.py --no-push printed OK at 8c171879d36: the preflight and
per-file compilation passed. The report was then updated to record these results;
the required delivery command will validate the packet again before pushing.
