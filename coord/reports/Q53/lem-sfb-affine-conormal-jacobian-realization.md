## Worker report

Delivered module: `Sheaf.RingTheory.AffineConormalJacobianRealization`.
Main declaration: `Algebra.AffineConormal.exists_affineConormalJacobianRealization`.
The only postponed theorem is this declaration, with the complete eight-step node proof
in its docstring. Every definition has actual data; structures describe the conclusion
whose existence the theorem asserts. No axiom, private definition, file-local notation,
new definition node, dependency repair or statement correction is introduced.

Hypotheses and objects, read against the node:

- A commutative ring is `R : Type u` with `[CommRing R]`. No field, Noetherian,
  reducedness, smoothness or characteristic hypothesis is present.
- Every natural number `c`, including zero, and every ordered family of equations
  `f : Fin c → PolynomialRing R c` occur in `Realization.chart`.
  `PolynomialRing R c` is literally `MvPolynomial (Fin (c+1)) R`.
- The hypothesis is exactly the dependency's
  `RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f)`.
  In particular the nonzero-final-quotient condition is retained.
- `ideal f` is `Ideal.span (Set.range f)`, and `QuotientRing f` is its actual quotient.
  `presentation f` uses the quotient surjection and the canonical structure map.
- `complex f` has the recorded `Naive.conormal`, `Naive.differentials`, and
  `Naive.differential` of this presentation. They are the actual extension conormal
  module and `B ⊗_P Ω[P/R]`, with the actual differential. `Chart.conormalIso` identifies
  its negative term with `(ideal f).Cotangent`, normalized on every ideal class.
  The vector `relation f i` is precisely the class of `f i` in `I/I²`.
- `C : Coherence` and `κ : Naive.Comparison C` are the recorded standard-resolution
  representation data, not geometric hypotheses. Their existence is already stated
  by the recorded cotangent-resolution and naive-comparison nodes. This statement is
  uniform in those data, and does not choose an unspecified cotangent object.
- An affine open is represented by any `A : CommRingCat.{u}`, `[Algebra R A]`, and
  `φ : QuotientRing f →ₐ[R] A` whose spectrum map is an open immersion. The identity
  chart recovers the node's original affine assertion. All affine opens occur, not
  only localizations at one element. Coefficient rings and chart rings have the same
  allowed universe; there is no smaller test universe. The sheaf-derived universe `w`
  is independent of the module-derived universe `u+1` used by the recorded framework.

Each conclusion:

1. The indicated basis of `C` is `Chart.conormalBasis` and
   `conormalBasis_formula`. The basis of the original ambient module `V` is
   `ambientBasis`, `ambientBasis_formula`, with vectors `dx f j` defined using the
   recorded pure tensor generator. The chart bases are `negBasis` and `zeroBasis`,
   with their scalar-extension-unit normalization. `Chart.jacobian` states every
   coefficient of the conormal differential in those frames.
2. `cofactorComplex` is the existing complex in degrees minus one and zero.
   `Chart.naiveIso` identifies it with the recorded naive complex, with both nonzero
   components fixed by `naive_negative` and `naive_zero`. `cotangentIso` identifies
   the chart complex with `intrinsic C R A`, literally the recorded standard-resolution
   cotangent complex. `standardChange_formula`, `extended_negative`, `extended_zero`
   and `cotangent_normalization` pin it to the existing naive projection and standard
   resolution maps, rather than an arbitrary derived isomorphism.
3. The determinant is exactly the existing `cofactorLine c`, namely
   `Dual A (⋀[A]^c E.neg) ⊗[A] (⋀[A]^(c+1) E.zero)`.
   `DeterminantChart` supplies a finite locally free tilde model, its normalized
   complex isomorphism, and its comparison to the sheafified standard-resolution
   complex. `ringProjection_formula` and `intrinsic_normalization` fix that comparison
   to the already normalized ring cotangent comparison. `dual_normalization` and
   `line_normalization` fix the exterior line identification on its ordered generator.
   `DeterminantChart.comparison` is the actual composite of that line identification,
   the inverse `T.modelIso`, and `twoTermDeterminantIso` of the recorded functor.
   `Realization.perfect` supplies its intrinsic perfectness condition. Thus the
   determinant is that of the intrinsic cotangent complex, not an independently
   chosen line with an unconstrained isomorphism.
4. `Chart.omega` is the actual quotient of the degree-zero module by the range of
   the conormal differential, linearly equivalent to `KaehlerDifferential R A`.
   `omega_formula` sends the class of each coordinate differential to its universal
   differential. It asserts no injectivity of the conormal differential.
5. `Chart.cofactor` is the dependency's `Module.TwoTermCofactorPresentation`.
   `Chart.w` is its map composed with `omega.symm`. `Chart.Formula` gives exactly
   the displayed relation-first wedge formula, for every conormal basis and every
   lift, and uniqueness of a linear map satisfying it. In particular both changes
   of lift and changes of conormal basis leave the same map. This uses the existing
   cofactor object rather than a private copy.
6. `Chart.trivialization` is a linear equivalence to the coefficient ring;
   `Chart.orientation` sends the dual conormal top wedge tensor the ordered ambient
   top wedge to one. `augmentedJacobian` is the determinant of the matrix with the
   `f` rows followed by `a`, implemented by `Fin.snoc`, and columns in `Fin (c+1)`
   order. `Realization.jacobian` is exactly the asserted formula for every polynomial,
   reduced modulo the actual ideal and then transported to the chart.
7. `Realization.restriction` gives an actual chain map for every map between these
   affine charts over the quotient, with both components normalized on frames.
   `Chart.Restriction.intrinsic` is its commutative derived square with the actual
   `cotangentMap C (algebraSquare ψ)`. Its cofactor equation expresses scalar transport
   in the normalized line coordinates. `Realization.determinant_restriction` supplies
   a termwise sheaf pullback comparison, fixed on the actual pulled-back frames, and
   a derived comparison fixed by `CotangentPresentation.pullbackCounit` followed by
   that chain map. Its determinant equation uses the actual model and pullback maps
   of every canonical `TwoTermPerfectDeterminantData`. It is evaluated on the true
   inverse-image open, with the actual restriction map on the right.
8. `Realization.transport` handles any two regular presentations on the same affine
   algebra, including different numbers of relations. `Chart.Transport` uses the
   derived isomorphism `H.cotangentIso ≪≫ H'.cotangentIso.symm`, through their common
   intrinsic complex. It supplies good diagrams, fixes their cokernel maps to the
   identity on intrinsic Kähler differentials, and asserts that every normalized
   good-diagram determinant intertwines the two cofactor maps. An isomorphism of
   presented R-algebras is included by taking its target as the common affine algebra.
   Literally transported scalar trivializations are handled by restriction; unrelated
   scalar trivializations are compared only through their determinant lines.
9. The wedge has relations first (`Fin.snoc`), and the determinant transport is the
   dependency's kernel-first `TwoTermCofactorGoodDiagram.determinant`.
   `KoszulOrientation` and `Realization.koszul_orientation` make the sign caveat precise
   with the already recorded ordered Koszul contraction convention: for every
   determinant-normalized Koszul comparison, its paired top dual is
   `(-1)^(c*(c-1)/2)` times the conormal top dual. This sign depends only on `c` and its
   inverse is the same sign, giving the corresponding change of scalar trivialization.
   The existing, landed node `def-sc-koszul-conormal-comparison` was added to `stmt_deps`
   solely to name that convention explicitly; its file and record are unchanged.
10. `Realization.empty_relations` explicitly states the zero-relation coordinate case:
    the image of `d x₀` is the empty conormal dual wedge tensor the singleton `dx₀`
    wedge. Together with the empty conormal basis this is exactly `C=0`, `w(dx₀)=dx₀`.

Dependency declarations used:

- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`, `exteriorPower`;
  Mathlib exterior-power modules: `exteriorPower.ιMulti`, `alternatingMapToDual`,
  `pairingDual`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`;
  `Mathlib.RingTheory.Kaehler.Polynomial`: `mvPolynomialBasis` and its coordinate formula.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Sheaf.LinearAlgebra.TwoTermCofactorNaturality`: `Module.TwoTermComplex`, its
  `cofactorComplex`, `cofactorCokernel`, `cofactorLine`,
  `Module.TwoTermCofactorPresentation`, `Module.TwoTermCofactorGoodDiagram`, its
  `determinant`, and `twoTermCofactor_naturality`.
- `Sheaf.AlgebraicGeometry.LciCotangentPresentation`:
  `AlgebraicGeometry.CotangentPresentation.ringComplex`, `tildeComplexFunctor`,
  `pullbackComplex`, `pullbackCounit` and the intrinsic lci comparison framework.
  Its public `Sheaf.RingTheory.NaiveCotangentComparison` gives `Naive.Presentation`,
  `conormal`, `differentials`, `differential`, `kernelClass`, `tensorGenerator`,
  `complex`, `conormalIso`, `differentialsIso`, `Comparison.projection`.
  `Sheaf.RingTheory.CotangentResolutionCoherence` gives `Coherence`,
  `cotangentComplex`, `cotangentMap`.
- `Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant`:
  `TwoTermPerfectDeterminantData.IsCanonical`, and the retained
  `TwoTermDeterminantModel`, `twoTermDeterminantValue`, `twoTermDeterminantIso`,
  `isTwoTermPerfect`, `modelIso`, `model_mem`, `pullbackIso`, `pullback_mem`.
- `WeilConjectures.RingTheory.KoszulConormalComparison`:
  `ExteriorAlgebra.IsKoszulConormalComparison`, `koszulComparisonValue`,
  `koszulNormalDeterminant`, and the existing Koszul complexes.
- Proof imports: `WeilConjectures.RingTheory.KoszulConormalBasis`,
  `exists_koszul_conormal_basis`; `WeilConjectures.RingTheory.RegularSequenceKoszulRegular`,
  `IsRegular.isKoszulRegular`; `Mathlib.RingTheory.Etale.Kaehler`, localization of Ω.
  The Jacobi--Zariski and polynomial differential facts already enter public imports.
  `lem-sfb-cofactor-local-descent` has no recorded declaration in this read clone, so
  there is no proof-only import to add for it; it is still named in the proof docstring.

Edge checks: empty relation list; the zero ring is excluded exactly when the regular-sequence
hypothesis excludes it; an empty affine open has zero coordinate ring and is included.
For `c=1, f₁=x₀, a=x₁` the row order gives +1; swapping the equations/last differential
example to `f₁=x₁, a=x₀` gives -1. In characteristic p, `f₁=x₀^p` has zero derivative,
so the cofactor vanishes; no false injectivity or smoothness assertion is made.
The Koszul signs for c=0,1,2 are +1,+1,-1. Identities, isomorphisms, nonprincipal affine
opens, changes of basis and differing presentation sizes are all in the quantifiers.

Searches actually run through `batch2/msearch.py`:

- LeanFinder: `Affine regular polynomial quotient conormal cofactor map augmented Jacobian
  determinant` — eight hits on pre/submersive presentation Jacobians and universal
  factorization Jacobians. They give selected square minors, not this full comparison.
- Loogle: `KaehlerDifferential, ExteriorAlgebra.ιMulti, Matrix.det` — zero hits.
- Mathlib grep: `conormal.*[Cc]ofactor|cofactor.*[Jj]acobian|augmentedJacobian` — zero hits.
- LeanSearch: `Cofactor map for differentials of a regular polynomial quotient equals the
  augmented Jacobian determinant` — eight hits, including Matrix.adjugate expansions
  and PreSubmersivePresentation Jacobian identities. None gives this statement.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id, `conormal.*[Cc]ofactor`, `cofactor.*[Jj]acobian`,
  `augmentedJacobian`, `AffineConormal` and the proposed full theorem name found no
  matching theorem. AffineConormalFrame/Sections concerns affine conormal coordinates,
  not the intrinsic cofactor/Jacobian realization. Existing cofactor and determinant
  notions are imported and reused. Read the Mathlib submersive presentation signatures
  and the recorded naive/cotangent/cofactor/determinant declarations in full.

Validation uses only the prescribed scompile.py and deliver2.py wrappers. An intermediate
version exceeded 60 seconds while elaborating a large dependent structure: factoring the
actual determinant pullback morphism into its own definition and disabling unnecessary
structure auxiliary generation restored clean per-file compilation well within the same
unchanged limit. No launcher script, live file, or compiled library was edited.

No mathematical statement fault or STATEMENT-DISPUTED finding.

## Second reading by Q53

A separate reading pass by this same worker, with the node and final module open;
no independent reader or sub-agent is claimed. The independent maintainer review follows
delivery, as the dispatcher brief specifies.

I checked the ring, ordered regularity and quotient first, then every conclusion against
the fields listed above. Two substantive gaps in the first draft were repaired before
this pass: an explicit basis for the original ambient module was added (rather than
only its scalar extension), and determinant restriction was pinned to the actual K-flat
counit and canonical determinant pullback, rather than only the algebraic wedge formula.
The comparison square initially carried equality fields for its right ring map; this was
replaced by `algebraSquare ψ`, so both sides are definitionally over the same ring map.
The shifted orientation is now expressed using the existing Koszul normalization and its
rank-only sign, instead of being left only in prose. This required the one additional
landed definition dependency named above.

The cokernel is the actual range quotient, not Ω supplied as an assumption; its Ω
identification is an output with the coordinate formula. All model and line objects
are the imported ones. The maps into the intrinsic cotangent object are pinned by the
naive projection; the determinant comparison uses that same intrinsic object. The unique
cofactor is an output, not a hypothesis. General affine charts include identity charts
and algebra isomorphisms. Different presentation sizes are compared through the same
intrinsic complex and every normalized good diagram. The empty case, positive
characteristic singular case and both c=1 orientation examples agree with the node.
There are no remaining statement mismatches found in this reading.
