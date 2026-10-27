## Worker report

Item: `lem-pur-chart-normal-differential`. Module:
`Sheaf.Paper.ChartNormalDifferential`. Main declaration:
`AlgebraicGeometry.ChartNormalDifferential.comparison`.
The module contains one theorem, whose proof is `sorry`. Its helper definitions contain
real data or explicit predicates. `Comparison` packages the conclusions of this node;
it is not an assumption on the chart. No theorem or definition of a prerequisite is
replaced, and the node copy changes only `lean`.

Sources read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/`
`sk-prop-sp-orientation-charts.proof.md`, especially Steps 1--2; Stacks `divisors.tex`,
Tags 0633--0635, labels `lemma-affine-conormal-sheaf`,
`lemma-conormal-algebra-functorial`, `lemma-conormal-algebra-functorial-flat`;
`morphisms.tex`, Tags 0473 and 08S2, labels `lemma-conormal-functorial-flat` and
`lemma-differentials-diagonal`. The inherited DAG proof's six steps are reproduced
in the theorem docstring, including the source of the difference convention.

Hypothesis and clause correspondence:

- Fixed k = algebraic closure of F_q: `D : WeilConjectures.FiniteFieldDatum.{u}`,
  with `D.k` and its existing field/closure instances. The fixed prime ell distinct
  from the characteristic is `_C : D.CoefficientDatum`; its `prime` and `different`
  fields supply precisely these conditions. `n` and `_hn : 1 ≤ n` retain the positive
  finite level. At E = Q_ell the stated coefficient ring is `ZMod (_C.l ^ n)`;
  it does not occur in this geometric assertion, so no arbitrary coefficient ring,
  extension E, or coefficient-category hypothesis is introduced.
- Affine finite-type k-scheme Y: `{Y : Scheme.{u}} [IsAffine Y]`, the structure map
  `aY : Y ⟶ Spec (CommRingCat.of D.k)`, and `LocallyOfFiniteType aY` plus
  `QuasiCompact aY`. There is no assumption that Y is smooth or reduced.
- Pure relative dimension d >= 0: `d : ℕ` and the displayed
  `SmoothOfRelativeDimension d` instance on `e ≫ p`. There is no `NeZero d`.
- The etale Y-map and h = pe: `e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y`,
  `[Etale e]`, with h consistently substituted by `e ≫ p`, where
  `p = (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)`. This eliminates the redundant
  equality binder rather than changing either map.
- Separated finite-type h: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`
  on that composite. Finite type of U over k follows by composition with `aY`;
  it is not silently replaced by finite type over another base. Affine-space
  smoothness is supplied by the existing theorem, not a new hypothesis.
- W and W_A: the actual Mathlib `pullback (e ≫ p) (e ≫ p)` and `pullback p p`,
  with `pullback.fst`, `pullback.snd`, and `pullback.diagonal`. Their diagonals'
  closed-immersion instances come from separation.
- Z = U x_A U and the specified O: `Comparison.O` is an actual open of W;
  `open_set` is the equality of its underlying set with the complement of the
  image of `pullback e e` minus the diagonal image. The morphism defining that
  image is `pullback.map e e (e ≫ p) (e ≫ p) (𝟙 U) (𝟙 U) p`.
  Thus O is uniquely fixed as an open, and `O.toScheme` has the induced structure
  sheaf. It is not an unspecified smaller neighbourhood.
- The diagonal into O: `δ`, `diagonal_factorization`, and the `closed` instance.
  The factorization fixes δ uniquely because `O.ι` is a monomorphism.
- q: `q_eq` fixes it as `O.ι` followed by the actual `e x e` pullback map.
  `square`, `cartesian`, and `etale` record the geometric square of centres.
- Both regular diagonals of codimension d: `regular_U`, `regular_A` give regular
  sequences of length d generating the actual stalk kernels. `codimension_U` and
  `codimension_A` give the stalk Krull-dimension equalities. This spells out the
  geometric regularity at centres and works at d = 0; it does not invoke the
  chapter's positive-codimension predicate at zero.
- Their rank-d normal bundles: `rank_U`, `rank_A` give conormal local freeness;
  `tU`, `tA` and `tangent_U`, `tangent_A` give the canonical normal/tangent isomorphisms.
  `IsNormalTangentIdentification` requires the symmetric-algebra isomorphism
  whose degree-one map is the specified conormal identification, and requires
  that its relative spectrum is the displayed scheme isomorphism. Projection
  and zero-section compatibility are included. The normal object is the existing
  `PurityNormalBundle.normalCone`, the relative Spec of the actual conormal algebra
  reexported by the dependency `PurityNormalProjection`, not a new cone model.
- Actual graded isomorphism c: `c` is the underlying tensor-pullback module
  isomorphism and `graded_comparison` uses the dependency's exact
  `ConormalGradedAlgebra.IsBaseChangeMap`. Its ring-sheaf adjoint and homogeneous
  maps make this an isomorphism of graded algebras, in the dependency's encoding.
  Its affine representative clause is exactly `[a] tensor r -> [q-sharp(a) r]`.
  The predicate's last two clauses fix degree zero to the structural identity
  and degree one to the existing canonical conormal pullback map. The unique-map
  theorem of that dependency prevents substitution of an arbitrary isomorphism.
- Specific relative-spectrum map: `ν` and `normal_spec`. `IsSpecMap` identifies
  the pullback of every local algebra section with c after the tensor-pullback
  unit. `normalAlgebraIso` is the counit of the existing fixed relative-spectrum
  anti-equivalence. Thus this is exactly Spec of c, including its direction.
  `normal_cartesian` says that the normal square is Cartesian, hence supplies
  precisely N_U/O isomorphic to U x_A N_A/W_A over U, with the canonical projections.
- Projection and zero section: the projection equality is the first part of
  `normal_spec`; `zero_section` is the required augmentation/zero-section equality.
- Independence of the ambient neighbourhood: `restriction`, `graded_restriction`
  give the actual graded isomorphism from the full-product diagonal to the one
  in O, using base change by `O.ι` with centre map `𝟙 U`. This includes every degree,
  multiplication, affine representatives, and degrees zero and one. `r` and
  `restriction_spec` give its actual contravariant relative spectrum;
  `restriction_zero` fixes the section. `restriction_square` is the commutativity
  witness required by the dependency API for this same factorization.
- The differential and its sign: `ωU`, `ωA`, `difference_U`, `difference_A` fix
  `da` as the class of `p2*a - p1*a`, on all ambient opens admitting the sections.
  The representative formula in `graded_comparison`, with `q_eq`, therefore
  pulls the affine coordinate difference to the difference of the two pulled-back
  coordinates on O. `IsDifferential p e de` separately fixes pullback of every
  local differential generator to `d(e-sharp a)`. Constants are fixed by its
  projection equation; the symmetric-algebra universal property then determines
  the entire map, not just its linearization at the zero section.
- Identification of the two maps: `normal_is_differential` is the equality
  `r.inv ≫ ν ≫ tA.hom = tU.hom ≫ de`. This identifies the very specified maps.
  `differential_cartesian` records invertibility after pullback to U, without
  falsely asserting that de is an isomorphism over A when e itself is not.
- Empty source and d = 0: neither a point, a positive-rank coordinate, nor
  a nonempty source is a binder. At rank zero the regular sequences at centres
  are empty, their ideals are zero, and the scalar normalization remains.

Dependency declarations read and reused (including their signatures and docstrings):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, together
  with the publicly imported `FiniteFieldDatum` and `FiniteFieldDatum.CoefficientDatum`.
  Only its finite-field and prime/level conventions enter this geometric statement.
- Mathlib pullbacks: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.diagonal`, `.map`.
- Mathlib `AlgebraicGeometry.IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `SmoothOfRelativeDimension`, and `Etale`.
  `def-weil-scheme-morphism-properties` is explicitly a collection of those
  separate notions, not a declaration to be copied.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its `over` instance;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AffineSpace.smoothOfRelativeDimension_over`, and
  `SmoothOfRelativeDimension.smooth`. The latter proofs are supplied explicitly
  to `Comparison`; no file-local or global instance is installed.
- `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`: `Presentation`, `presentation`,
  its `algebra`, `inclusion`, and the existing `piece`, `power`, `representative`.
- `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange`: `IsBaseChangeMap`,
  `existsUnique_baseChangeMap`, including its affine and degree-zero/one clauses.
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`:
  `Scheme.Modules.closedImmersion_conormal_flat_base_change`, whose canonical
  degree-one map is exactly the one in `IsBaseChangeMap`.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`:
  `affine_morphism_relative_spec`; `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`:
  `relative_spec_base_change`. The existing `VectorBundleZeroSection.antiEquivalence`
  fixes the implementation used by both normal and tangent schemes.
- `Sheaf.Paper.PurityNormalProjection`: `Scheme.Hom.purityNormalProjection`,
  publicly reexporting `PurityNormalBundle.normalCone`, `.projection`, `.zeroSection`,
  and `.algebraObject`. Their already constructed relative-spectrum model is used.
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`:
  `diagonal_isRegularImmersionOfPureCodimension`. Its documented positive-dimension
  restriction is respected: the d > 0 proof branch uses it; the d = 0 branch is
  the elementary open-and-closed diagonal calculation. There is no added hd binder.
- `WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation`:
  `IsDiagonalConormalDerivation`, `exists_diagonalConormalDerivation`;
  `DiagonalConormalAffineSections`: `diagonalConormal_affine_sections`;
  `DiagonalConormalDifferentials`: `diagonalConormal_iso_relativeDifferentials`.
  The helper predicate renders their difference convention with the existing
  ideal-power representatives; it does not introduce a second differential sheaf.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `.relativeDifferentialsDerivation`;
  `Sheaf.AlgebraicGeometry.RelativeTangentBundle`: `scheme`, `projection`,
  `zeroSection`, `algebraIso`;
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  `exists_quasiCoherentSymmetricAlgebra_core`, with the existing
  `SymmetricAlgebraSheaf.algebra` and `.inclusion`.

Searches actually performed:

- `msearch.py leanfinder`: "The normal bundle comparison of etale coordinate
  diagonals is the differential and preserves the zero section". Eight hits,
  including ring-level `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
  and unrelated manifold tangent lemmas; none states this chart theorem.
- `msearch.py loogle`: `KaehlerDifferential.map, IsEtale`. Service answered zero
  hits and reported that `IsEtale` is unknown. This is not evidence that differential
  base-change lemmas are absent; the LeanFinder hits were inspected as candidates.
- `msearch.py grep`: `normalCone|conormal|differential` in
  `AlgebraicGeometry/Morphisms`. One hit in `FormallyUnramified.lean`, concerning
  an idempotent Kaehler ideal, not the statement.
- `rg` of both project Lean trees for normal/conormal/tangent/differential names,
  and for `lem-pur-chart-normal-differential`. The latter has no declaration upstream;
  the project has the consuming orientation theorem's proof docstring. Existing
  conormal, normal, tangent, and symmetric-algebra constructions were reused.
- A final `rg` of both Lean trees for `ChartNormalDifferential`,
  `chart_normal.*differential`, `normal.*tangent.*chart`, and
  `IsNormalTangentIdentification` found no competing declaration. The two textual
  matches concern unrelated Koszul and formal-coordinate statements.

Edge cases checked mathematically: d = 0 including a two-sheet etale cover (O removes
only the off-diagonal components); empty U; empty Y; the identity chart; permutation
of two coordinates; and t -> t^m on G_m when m is invertible in k. In the last case the
normalization yields m*t^(m-1) dt, which checks the sign and the direction. A negative
morphism -identity likewise produces -dt, not an unspecified line-bundle isomorphism.
The arbitrary universe u and lifted coordinate type retain d = 0 in every universe.

Validation: the prescribed scompile.py compiled both the sandbox probe and the named
library module cleanly (10.1 s and 12.8 s). The file uses module mode,
`@[expose] public noncomputable section`, explicit universes, `autoImplicit false`,
no local notation or instances, and lines of at most 100 characters.
No statement correction or STATEMENT-DISPUTED flag is needed. No additional DAG nodes
or dependency modules are introduced; all helper declarations belong to this item and
are listed in its `lean.declarations`.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
