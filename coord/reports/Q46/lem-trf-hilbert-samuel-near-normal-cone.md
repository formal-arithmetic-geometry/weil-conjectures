## Worker report

Stage 2, Q46, 2026-10-22. The item has no previous Lean record. The Q43 merge recorded at
coord/ledger.md:25022 is a stage-1 split (two lower theorem nodes, no Lean), not a completed
stage-2 statement. The previous worker's stale-assignment diagnosis was therefore incorrect.
There is no repair note for this item. The reviewed stage-1 statement and proof are preserved.

The module `Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone` states
`AlgebraicGeometry.HilbertSamuel.near_normal_cone`, with one postponed theorem and five
fully constructed helpers for the specific objects occurring in that statement. There are
no hollow definitions, arbitrary chosen maps, or additional postponed helper lemmas.
The only DAG addition to statement dependencies is the already landed
`def-trf-hilbert-samuel-invariant`, whose function is used directly. No new node is created.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Schemes of finite type over Q: `X C P : Scheme.{u}` and
  `p : P ⟶ Spec (.of (ULift.{u} ℚ))`, `i : X ⟶ P`,
  `[LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]`.
  ULift changes only universe size, using the canonical field structure, and allows every
  scheme universe. `[IsReduced X]` is exactly reducedness.
* Locally closed in a smooth scheme: `[IsImmersion i] [Smooth p]`.
  No closedness, separatedness or finite-type assumption on the ambient is added.
* The raw function is the existing `HilbertSamuel.localFunction`: the length over the stalk
  of its maximal-ideal-power quotient, converted to a natural number. Its lengths are finite
  under the present finite-type assumptions, including at nonclosed points.
  The existing `HilbertSamuel.function` applies `summation` iterated by the natural-valued
  transcendence degree of the residue field over the canonical ground-field embedding.
  Thus it is exactly the stated H, with no substitution of CJS's different normalization.
* Smooth closed centre: `c : C ⟶ X`, `[IsClosedImmersion c]`,
  `[Smooth (c ≫ i ≫ p)]`. The centre need not be connected, equidimensional globally, or
  disjoint from all components in advance.
* Local constancy on the centre: `hconstant : IsLocallyConstant
  (fun z : C ↦ function (i ≫ p) (c z))`. This is local constancy on the centre's own topology,
  not on an ambient neighbourhood, and does not replace it by global constancy.
* The blowup is literally `c.ker.blowup`, with its map `c.ker.blowupMap`. The node gives the
  intrinsic blowup as its primary object and the ambient strict transform as its equivalent
  description; the intrinsic object is used, without assuming a global closed ambient.
* The point over the centre: `z : C`, `y : c.ker.blowup`,
  `hy : c.ker.blowupMap y = c z`. Writing `x=c z` represents every x in C. There is no
  rational-point, closed-point or residue-extension restriction on either point.
* Nearness: `hnear : function (c.ker.blowupMap ≫ i ≫ p) y =
  function (i ≫ p) (c z)` is equality of the entire two sequences.
* R is `X.presheaf.stalk (c z)`. I is `centerStalkIdeal c z`, literally
  `RingHom.ker (c.stalkMap z).hom`. For a closed immersion this is the stalk of its defining
  ideal. A is `R ⧸ I`, k is `X.residueField (c z)` (definitionally R modulo its maximal ideal),
  and G is the dependency's `Ideal.associatedGraded I`, not a replacement graded ring.
  `centerResidueAlgebra` is the actual factor map A to k, using the existing theorem that
  a proper ideal of a local ring lies in its maximal ideal. The kernel is proper since the
  target stalk is a nontrivial local ring. It contains no postponed proof.
* Flatness is `Module.Flat A G`, with the dependency's degree-zero quotient action.
  Mathlib's `Module.Flat.rTensor_preserves_injective_linearMap` identifies this with the
  injection-preservation formulation in the node for arbitrary modules.
* `normalFibre c z` is `k ⊗[A] G`. The tensor factors are commuted relative to the node's
  `G ⊗[A] k`, through the standard canonical algebra commutor; this does not change the
  graded algebra or point. `normalFibreGrade` is the k-span of `1 ⊗ iota_n(a)` for every a
  in the actual degree-n quotient. The existential grading is on these fixed submodules,
  so it cannot choose a different grading.
* The exceptional-fibre identification is a canonical `IsPullback` square over
  `X.fromSpecResidueField (c z)`. The map out of Proj is the composite of `Proj.map φ hirr`,
  `AffineBlowup.hom` for the affine-to-stalk germ, and `c.ker.blowupι U`.
  The affine neighbourhood `U` and `hx` are existential choices of a coordinate chart;
  `hI` asserts the actual equality of the extended affine ideal with I.
  The graded Rees map φ is specified for every n and every a in I^n by
  `φ(a T^n) = 1 ⊗ iota_n(a mod I^(n+1))`. Rees monomials additively generate the Rees
  algebra, so this specifies φ uniquely, including its scalar normalization in degree zero.
  `hirr` is precisely the irrelevant-ideal condition for this canonical Proj map.
  These existential construction data and their defining formulas express the identification,
  not a new hypothesis and not an arbitrary fibre isomorphism that could move y.
* B and its algebra structure over k are existentially quantified in `Type u`.
  The submodules `𝓑`, their `GradedAlgebra` structure, and `GradedAlgebra.IsStandard 𝓑`
  give exactly a standard graded k-algebra, including B_0=k and finite degree-one generation.
* The integer e is `r : ℕ` with `1 ≤ r`. `e : normalFibre c z ≃ₐ[k]
  MvPolynomial (Fin r) B` is the algebra isomorphism. The additional equivalence of
  membership in each degree with `normalPolynomialGrade 𝓑 r n` says it is graded.
  That helper is the span of coefficient-degree-j monomials of variable degree d with
  `j+d=n`. It is the total grading, so every T_i has degree one. Using the ordinary
  polynomial grading over B would incorrectly put all of B in degree zero; that is avoided.
* The witness `t : Proj (normalFibreGrade c z)` maps to the original y under the same
  monomial-specified fibre map. The last clause requires
  `e.symm (MvPolynomial.C b) ∈ t.asHomogeneousIdeal.toIdeal` for every b in every positive
  degree `𝓑 n`. It says exactly that the homogeneous prime contains B_+ times B[T].
  Thus t lies in the closed Proj of the quotient k[T], which is the required linear subspace.
  An assertion merely about closed or k-rational points is never used.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
* `Mathlib.RingTheory.Length`: `Module.length`; `Mathlib.RingTheory.AlgebraicIndependent.Basic`:
  `Algebra.trdeg`; `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldAlgebraMap` and `Scheme.fromSpecResidueField`.
  These are also the definitions used by the imported existing Hilbert--Samuel function.
* `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`: `HilbertSamuel.function`,
  `HilbertSamuel.localFunction`, `HilbertSamuel.summation`.
* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`, `blowupι`.
* `WeilConjectures.Compactification.StrictTransform`: `AlgebraicGeometry.strictTransform`,
  imported for the node's equivalent ambient description; the primary object is the blowup.
* `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, `Ideal.associatedGradedAlgebra`, with their real ring structures.
* `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `AlgebraicGeometry.Proj`.
* `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, `TensorProduct.mk`;
  `Mathlib.RingTheory.TensorProduct.Basic`: its commutative algebra structures.
* `WeilConjectures.RingTheory.GradedAlgebra.Standard`: `GradedAlgebra.IsStandard`.
* `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.monomial`,
  `MvPolynomial.C`; the dependency's `MvPolynomial.aeval` and `MvPolynomial.algHom_ext`
  describe the existing universal property and are not reimplemented.
* `WeilConjectures.Blowup.Affine.ReesGrading`: `reesGrading`, `reesMonomial`;
  `WeilConjectures.Blowup.Affine.Functoriality`: `AffineBlowup.hom`;
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Affine`: `Proj.toSpecOfAlgebra`.

The recorded, already stated proof dependencies are imported without `public`:
ConormalGradedAlgebra; Regular; RegularLocalRing.Defs; DimensionAtPointLocalRingTrdeg;
DimensionAtPointComponents; ClosedIrreducibleDimensionTrdeg; RelativeProj.BaseChange;
RelativeProj.Functoriality. Blowup.Gluing, Affine.Defs, ReesAlgebra, Proj and Standard are
already statement imports. The two new lower inputs of Q43's split, the Bennett criterion
and additive symmetry theorem, have no Lean records, so there is no module to import yet.
No import cycle is introduced by this new terminal module.

Edge cases checked before and after writing:

* Empty X or empty C has no z, hence no instance of the pointwise assertion.
* I=0 has a Rees algebra concentrated in degree zero, so no y over this centre exists.
  In particular C=X does not falsely imply the existence of a positive-dimensional fibre.
* An invertible centre ideal has one polynomial variable in its normal fibre: r=1 is
  allowed; its projective fibre is a point. Smooth X and a smooth proper centre give B=k
  and the expected projective normal space.
* No component-avoidance assumption is added. The node's step 6 derives it locally from
  flatness and the existence of y. Reducible X and disconnected C are retained.
* Generic or nonclosed x and nonclosed y, including transcendental residue extensions, are
  retained. Their whole normalized Hilbert--Samuel sequences are compared and t is a
  general homogeneous prime, with no maximal-ideal or rationality test.
* At n=0 the polynomial grade is exactly B_0 (all variable exponents zero); at n=1 it
  includes both B_1 and the variables with degree-zero coefficients. Thus coefficient
  grading is not silently lost. The final ideal condition uses strictly positive n only.
* Characteristic zero is retained by ULift Q; the subgroup-linearity argument would not
  justify the same conclusion in positive characteristic, which is not asserted.

Searches for duplicates (2026-10-22):

* `msearch.py ... leanfinder "Hilbert Samuel constant smooth center blowup near point flat
  normal cone polynomial directrix"`: 8 hits on smoothness and standard smoothness; none
  states normal flatness plus the near-point directrix conclusion.
* `msearch.py ... loogle '"associatedGraded", "Flat"'`: 0 hits.
* `msearch.py ... grep 'Hilbert.?Samuel|normal.?flat|directrix|[Nn]ear[Pp]oint'`: 0 Mathlib hits.
* `msearch.py ... leansearch "Flat normal cone and polynomial linear vertex for Hilbert
  Samuel near points of smooth center blowups"`: 8 hits on convex flat cones and smooth
  algebra flatness, none on this theorem.
* `rg` on `lean/WeilConjectures` and `lean/Sheaf` for HilbertSamuel, hilbertSamuel, normalCone,
  normalFibreGrade and near_normal_cone: existing invariant/local-presentation material,
  conormal geometry and deformation-to-normal-cone results, but no statement of this item.
  Search for the exact node id in `lean/WeilConjectures`: no match.
* Graded-coefficient polynomial search with LeanFinder returned
  `MvPolynomial.gradedAlgebra`, `weightedGradedAlgebra`, `homogeneousSubmodule`,
  `IsHomogeneous` and totalDegree facts. All treat the coefficient ring as degree zero;
  none gives the required grading with a graded coefficient algebra. `rg` of Mathlib's
  GradedAlgebra and MvPolynomial directories confirms the distinction.
* Existing DAG records were searched and the full statement dependencies read. The
  Hilbert--Samuel invariant node already gives the needed numerical notion, so its
  declaration is reused, not given a new definition node. The five helpers only name
  the explicitly specified local objects/formulas of this very node.

Source inspection: ILO printed pp.93--95 (PDF pp.99--101), including VIII 2.3.13, was read.
The node's ten-step reviewed proof is reproduced in the theorem docstring, including its
precise lower Bennett and additive-symmetry inputs. No mathematical statement correction
was necessary, and there is no STATEMENT-DISPUTED flag.

Validation: scompile.py compiled this file as both sandbox and final module, with no
errors or non-sorry warnings (16.6 s and 16.7 s). The initial code-generation diagnostic
on the stalk ideal was fixed by marking its actual construction noncomputable; its data
was not changed or postponed. Only the final near_normal_cone theorem uses sorry.

## Second reading by Q46

The dispatcher explicitly forbids starting another agent, so this is a second pass by the
same worker, not a claimed independent review. The maintainer performs the independent
review. I reopened the node and the complete Lean file and compared the binders and every
conclusion as detailed above. In particular I checked that the Q43 delivery was stage 1,
that the normalization reuses the existing function, that r=1 is admitted, that B has a
standard grading, that total degree includes its coefficient grading, that the canonical
Rees monomial formula specifies the fibre map, and that the point's prime contains every
positive-degree coefficient. No dropped hypothesis, weakened clause or extra geometric
hypothesis was found. No changes were needed after the successful compile.
