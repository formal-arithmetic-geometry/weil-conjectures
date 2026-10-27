## Worker report

The module `Sheaf.AlgebraicGeometry.HomogeneousSliceFiniteCover` states
`AlgebraicGeometry.HomogeneousSlice.homogeneous_slice_finite_cover`. Its only theorem
has proof `sorry`; every helper definition has real data. The item's informal statement,
statement dependencies and proof plan are unchanged.

Clause-by-clause correspondence (all names below are in `AlgebraicGeometry.HomogeneousSlice`):

- The field is `k : Type u` with `[Field k]`. The vector space is `V : Type v`, with
  `[AddCommGroup V] [Module k V]`, and `b : Module.Basis (Fin (n + 1)) k V`.
  An arbitrary finite-dimensional nonzero vector space admits just such a basis, so this
  is a coordinate presentation of exactly the stated hypotheses, not a dimension restriction.
  Conversely any displayed basis forces finite dimension and nonzeroness. Its universe `v`
  is independent of the scheme/field universe `u`.
- `j : Y ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)` and `[IsClosedImmersion j]`
  render the closed immersion into projective space of lines. Its k-scheme structure is the
  composite with `Proj.toSpecZero` and `Spec.map homogeneousSubmoduleZeroEquiv`. Any given
  k-scheme immersion in the node has exactly this structure. Since this Proj is over the
  field, giving the immersion determines the source structure map.
- `coordinates k V n b` is the actual algebra equivalence
  `SymmetricAlgebra k (Module.Dual k V) ≃ₐ[k] MvPolynomial (Fin (n + 1)) k`, from
  `SymmetricAlgebra.equivMvPolynomial b.dualBasis`. Thus the theorem quantifies over
  `F : SymmetricAlgebra k (Module.Dual k V)`, not a replacement symmetric algebra.
  Its homogeneity hypothesis is membership of the image in the degree-d submodule.
- `ideal` is `Ideal.span` of the homogeneous polynomials whose normalized section is
  zero on *every* standard chart of Y. `projectiveClosedSubschemeChartFraction` supplies
  those actual sections; this is exactly the section-vanishing ideal of the node.
  Its homogeneous pieces are already closed under addition and homogeneous multiplication;
  taking their generated ideal is their direct sum. No radical or pointwise-vanishing
  replacement occurs.
- `cone` is `Spec (.of (P ⧸ ideal ...))`. `puncture` is the union of the principal opens
  of the images of the variables, i.e. removal of the common zero/vertex. On empty Y the
  ideal contains 1 and this construction is empty, as required.
- `line` is the existing `Scheme.Modules.tensorPullback j` applied to `Proj.twist ... 1`.
  This is the polynomial-Proj version of the recorded `ProjectiveSpace.twist`: that
  recorded construction is itself a pullback of this exact `Proj.twist` on the integral
  model. No second twist or invertibility notion is defined. The first conjunct states
  `line.IsInvertible` using the recorded invertible-module class.
- The existing `line.symSpec` is relative Spec Sym(L), glued from actual affine symmetric
  algebras, so its vectors are in L dual = L inverse. `bundlePuncture` removes the range of
  the existing augmentation map `line.symSpecZeroSection`. This is the node's total space
  constructed by linear transition functions, with the correct dual convention.
- The theorem produces `a : line.symSpec ⟶ cone` and
  `e : puncture.toScheme ≅ bundlePuncture.toScheme`. `IsEvaluation a` prescribes the
  structure morphism over k and all degree-one coordinate functions on the affine basis.
  `lineCoordinate` uses the canonical tensor-pullback adjunction unit and the existing
  homogeneous coordinate section `Proj.unitToTwist`. The equation
  `e.hom ≫ bundlePuncture.ι ≫ a = puncture.ι` fixes the comparison. The uniqueness
  conjunct for `a` expresses canonicity: the prescribed scalar and degree-one images
  determine every polynomial function, hence the map to this affine quotient. The
  projection to Y is `e.hom ≫ bundlePuncture.ι ≫ line.symSpecProj`, so the comparison is
  over Y by its very construction.
- `d : ℕ`, `hd : 0 < d`, `hF` and `c : kˣ` render the exact degree and unit conditions.
  `sliceIdeal` is `ideal ⊔ Ideal.span {f - C ↑c}` and `slice` its affine quotient spectrum.
  `sliceInclusion` is Spec of the actual quotient factor map, not an arbitrary immersion.
- `nonvanishing` is `j ⁻¹ᵁ Proj.basicOpen ... f`, exactly Y_f. The theorem supplies the
  puncture factorization `t` and `p : slice ⟶ nonvanishing.toScheme`. The first equation
  makes t the restriction of the actual affine quotient immersion. The second equation
  makes p the restriction of the vector-to-line map, with the *same* comparison e chosen
  before d, F and c. There is no arbitrary finite map substituted for that map.
- `p.IsFiniteLocallyFreeOfDegree d ∧ Surjective p` uses the recorded finite-locally-free
  and fibre-degree definitions, with Mathlib's scheme-surjectivity class.
- `IsNatural a e f c p` quantifies over mutually inverse graded polynomial substitutions
  fixing constants and f. On the degree-one submodule these are precisely the duals of
  the linear automorphisms of V, in the displayed basis. The equation on `gY` and j
  expresses preservation of Y as a *scheme*. The irrelevant-ideal bound `hσ` is the proof
  needed to form the existing `Proj.map`; it always holds for a graded automorphism.
  The conclusion supplies induced isomorphisms on the actual cone, bundle, slice,
  nonvanishing open and puncture, with polynomial pullback prescriptions on the cone and
  slice and commutation with the base projection, comparison e and finite map p.
  Quantifying over inverses and irrelevant-ideal proofs is a presentation of the
  automorphisms, not an additional geometric hypothesis.

All helpers belong to this node's construction: they name its displayed rings, opens,
line, coordinate identification, and normalization/naturality conditions. They do not
introduce a new independent mathematical notion. There are no new nodes or dependency
modules. No statement fault or STATEMENT-DISPUTED issue was found.

Dependencies read and used:

- `Field` (Mathlib.Algebra.Field.Defs).
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`, `Scheme.ΓSpecIso`
  (Mathlib.AlgebraicGeometry.Scheme).
- `AlgebraicGeometry.IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion).
- `Scheme.Modules.IsInvertible`
  (WeilConjectures.AlgebraicGeometry.Modules.Invertible).
- `ProjectiveSpace.twist` and its underlying `Proj.twist`
  (WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist and
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist).
- `Scheme.Hom.IsFiniteLocallyFree`, `Scheme.Hom.IsFiniteLocallyFreeOfDegree`
  (WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree).
- `projectiveClosedSubschemeChartFraction` and
  `exists_projectiveClosedSubscheme_homogeneousIdeal`
  (Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal).
- `Scheme.Modules.symSpec`, `symSpecProj`, `symSpecZeroSection`, `symCoord`
  (WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf and
  WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheafBundle).
- The recorded statement dependencies' full signatures and docstrings were read. The
  withdrawn example `Sheaf.CategoryTheory.CompactObject` now contains no declarations;
  its node points to `WeilConjectures.CategoryTheory.CompactObject`, also read.

The already stated proof dependencies are imported privately:
ProjectiveClosedSubschemeHomogeneousIdeal (also public, as its chart fractions occur in
our definitions), ProjectiveSpaceStandardCharts, FiniteFreeAlgebraSpectrum,
IsFiniteLocallyFreeOfDegreeOfEtaleCover, Mathlib's Away localization and FaithfullyFlat.Basic.
The other proof nodes have no recorded Lean declaration; no auxiliary theorem from them
is needed to type this statement. Their mathematical arguments are retained in the
main theorem's eight-step docstring. No missing *statement* prerequisite is deferred.

Edge cases checked before writing:

- n=0: P^0, a one-dimensional V; the slice is t^d=c/a over a point if a is nonzero.
- Empty Y: the degree-zero constant 1 vanishes and the cone, bundle, and all slices are
  empty. The zero-section complement definition and the affine-basis normalization still
  make sense on the empty scheme.
- Empty Y_f, including f=0 with d>0: f-c is a unit modulo I after localization on any
  cone chart, so T is empty and positive-degree finite local freeness is vacuous there.
- Nonreduced Y: ideal membership is zero in section rings, not zero at residue fields;
  neither cone nor slice passes to a radical. The Laurent calculation retains nilpotents.
- Characteristic dividing d: t^d-c/a is still monic and its quotient has the d-element
  basis. No separability, reducedness, or etaleness of p is asserted.
- Arbitrary field: no root in k is assumed. Surjectivity is on scheme points and follows
  chartwise from positive-rank faithful flatness.
- Scalar automorphisms and the identity: the graded-substitution naturality includes
  them, including when a scalar fixes f only because its d-th power is 1.

Searches (all through the prescribed `msearch.py Q11 lem-sfb-homogeneous-slice-finite-cover`):

- leanfinder: “The punctured affine cone is the nonzero tautological line bundle and a
  nonzero homogeneous level is finite locally free over its projective open”. Eight
  results, headed by `Proj.awayι`, `ProjIsoSpecTopComponent.FromSpec.toFun`, and
  `Proj.isAffineOpen_basicOpen`; these give chart infrastructure, not the theorem.
- loogle: `"Proj", "IsFinite"`. Only unrelated
  `MeasureTheory.IsProjectiveLimit.isFiniteMeasure`; no match.
- grep: `(punctured|affineCone|totalSpace|tautological)` in Mathlib/AlgebraicGeometry.
  Zero results.
- leansearch: “The punctured affine cone of a projective closed subscheme is the
  complement of zero in its tautological line bundle”. Eight results about basic opens,
  zero loci and Proj affine covers, not this comparison or cyclic finite cover.
- rg of `lean/WeilConjectures` and `lean/Sheaf`: cone/slice/tautological/total-space
  names; no existing theorem. The broad bundle search found the actual symSpec
  construction, reused here. `grep -rn` of the item id in WeilConjectures had no result.
- DAG search found the homogeneous-ideal and affine-cone-dimension nodes. The former
  supplies the reused chart fraction; the latter is only a topological dimension
  statement and cannot replace the present scheme isomorphism and finite cover.

Sources read locally: constructions.tex at the labels for Tags 01M4, 01NF, 01MS and 03GL.
The current latest blueprint unit and its direct-image proof were read for the ancestor's
role; no unit statement changes. The node's reconstruction proof is reproduced stepwise
in the theorem docstring.

Validation: `scompile.py Q11 lem-sfb-homogeneous-slice-finite-cover` compiled the single
module in sandbox mode and library mode with no error or warning. An initial nonexistent
Surjective import was removed; a coordinate-section type annotation and an expanded
projective structure map fixed elaboration without a universe restriction.

## Second reading by Q11

No second worker reading: the dispatcher's explicit brief forbids starting other agents.
The maintainer's independent delivery review is the second reading under the current
2026-10-17 direct-delivery policy. The clause correspondence above is the author's own
check, not a claimed independent review.
