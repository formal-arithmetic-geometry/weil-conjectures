## Worker report

Repair of L's H3/H4 return on immutable head 77186f4711e6. The earlier packet
attached `AlgebraicGeometry.le_add_one_of_isFourierPartner`, whose input,
Fourier transform and purity predicate belong to the older pro-etale
`WeilSheaf`/`WeilComplex` presentation. That attachment is removed. This packet
states `WeilConjectures.commonStage_fourierPartner_weight_le_add_one` on the
recorded intrinsic common-stage fixed-pair category, with the recorded punctual
purity predicate and Fourier functor. No equivalence to the older category is
assumed. All new theorem proofs are `sorry`; every definition has actual data.

I read the current node, all five original statement dependencies and their
records, their declarations and docstrings, the main-20261015 upper-weight unit
and proof in full, and the newly cited landed lisse-lattice definition. The
natural-language statement, source, proof steps and proof dependencies are
unchanged. `stmt_deps` gains the already landed
`def-a1-common-stage-lisse-lattice`, used for the lisse predicates. There are no
new DAG nodes and no statement correction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The standing finite-field and coefficient hypotheses are `F : FourierSetting`:
  its `field` contains k0, its fixed algebraic closure k, q=p^a with a positive,
  and its `coefficients` contain the prime l different from p and the specified
  algebraic closure Qbar of Q_l. The finite stage containing mu_p is only the
  coefficient stage used for the explicit Artin--Schreier construction.
  `iota : F.coefficients.Qbar ≃+* ℂ` is precisely the chosen isomorphism in the
  punctual-weight definition. Universe u is explicit and arbitrary, and is the
  same convention as the recorded FourierSetting and common-stage Fourier API.
- The given arbitrary character is `ψ : AddChar F.field.k₀ F.coefficients.Qbar`
  with `hψ : ψ ≠ 1`. Field-valued additive characters take unit values
  automatically, so this is the same as the source's unit-valued character.
  `Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar`, `hΨ : Ψ ≠ 1`, is an
  auxiliary presentation character, not a restriction on ψ: every ψ has a
  uniquely specified scalar b with ψ(x)=Ψ(Tr(bx)). The trace pairing gives this
  scalar, including b=0 for the trivial character. For the given nontrivial ψ,
  b is nonzero. Thus this statement includes all ψ, including ones trivial on
  the prime subfield when p divides [k0:Fp]. It does not assume ψ=Ψ composed
  with the unscaled trace. A nontrivial Ψ exists for every prime p in Qbar;
  the theorem works for every such auxiliary choice.
- `A A' : SfAffineLineOpen F` contain U0 and U0', their morphisms j and j' to
  the actual `fourierAffineModel F PUnit`, open-immersion instances and
  `dense : DenseRange j.left.base`. Their finite-type, quasi-compactness and
  separatedness fields follow for every open of the Noetherian affine line;
  they add no restriction on the dense opens. `SfAffineLineOpen.curve` puts
  precisely the same objects into the recorded `MiddleExtensionCurve` datum.
  The only geometry supplied there is the affine line's smoothness and pure
  dimension one. The standard coordinate identifies the dual line with the
  same model, exactly as in `affineCommonStageFourierTransform`.
- M and M' are `sfCommonStageWeilSheaf` on A.U and A'.U: the full heart-carrier
  subcategories of the *actual* common-stage Frobenius fixed pairs.
  `hMlisse` and `hM'lisse` use `HasCommonStageLisseLattice` on their carriers.
  This is the already recorded lisse adic convention, including rank zero and
  with no requirement that Frobenius preserve an integral lattice.
- Nonzero is exactly `hMnonzero : ¬ IsZero M`. Arithmetic irreducibility is
  `hMirreducible`: for every Weil sheaf G and mono i:G→M, if G is lisse, then
  `IsZero G ∨ IsIso i`. Mono is taken in the Weil **sheaf heart**, not in the
  triangulated category. There is no simplicity condition among all
  constructible sheaves, geometric irreducibility or infinity hypothesis.
- `hne : SfIsConstituentNonexceptional F A Ψ hΨ ψ M` excludes each character
  line for **every a:k**, including zero. Its geometric function is ba x,
  where b is the unique trace coefficient of ψ, so its Artin--Schreier
  construction is exactly L_{ψ(ax)}. This is necessary for a outside k0: no
  Weil descent is claimed for that geometric line. The predicate says that
  there is no lisse geometric heart object G with a mono into the geometric
  carrier of M and an epi onto this rank-one line. Rank-one lines are
  irreducible, so this is precisely exclusion of that Jordan–Hölder
  constituent, including nonsplit occurrences. The arrows are in the
  geometric standard heart, without equivariance conditions.
- `w v : ℝ` and `hw`/`hv` use the recorded
  `SfIsPunctuallyPureOfWeight` with the same iota. Hence they quantify over
  every closed point and each eigenvalue of the recorded local geometric
  Frobenius after extension to Qbar, requiring norm exactly q_y^(weight/2).
  No integer-weight or semisimplicity condition has been introduced.
- `sfAffineShiftedMiddleExtension` first applies
  `qbarCurveWeilOrdinaryPushforward` to M, includes the resulting heart object
  in fixed pairs, and applies `qbarAffineWeilShift`. The ordinary pushforward
  is the right adjoint to the actual `zlWeilPull`. Its forgetful comparison
  identifies it with `qbarCurveOrdinaryPushforward`, namely ordinary j_*,
  whose sections are G(V times_C U). The shift tensors with the explicit
  arithmetic constant line [1], with its arithmetic-descent Frobenius; its
  forgetful comparison is the actual `shiftFunctor _ (1 : ℤ)`. Thus this is
  (j_*M)[1], with the induced Weil map. It is not Rj_*M.
- `sfAffineFourierTransformForCharacter` calls the *recorded*
  `commonStageFourierTransform` on the standard product projections and the
  recorded completed `fourierAdicKernel`, for the pairing bxy and shift 1.
  Since ψ(x)=Ψ(Tr(bx)), its kernel is exactly L_{ψ(xy)}. This is the same
  Fourier transform for arbitrary ψ. The comparison theorem
  `sfAffineFourierTransformForCharacter_trace` identifies it with the
  recorded `affineCommonStageFourierTransform` when ψ=Ψ composed with trace.
  The supplied compactification c is arbitrary, as in the recorded API; it
  is an implementation of Rp₂!, not a mathematical restriction.
- `hFT : Nonempty (... ≅ ...)` is the given isomorphism in the category of
  **Frobenius fixed pairs**, hence includes equivariance. It uses the shifted
  ordinary image of M on the left and that of the prescribed M' on the right.
- The conclusion is exactly `v ≤ w + 1`. There is no added nonzero,
  irreducibility or nonexceptionality premise on M'.

Dependency declarations used:

- `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`: Mathlib `AddChar` and
  the recorded `AddChar.FiniteField.primitiveChar` construction were inspected;
  the latter lands in a cyclotomic extension, so it is not mistaken for a
  character directly into the chosen Qbar. The delivered character lift is
  uniquely determined by the given Ψ and ψ, via the trace pairing.
- `Sheaf.Paper.CommonStageFourierTransform`:
  `commonStageFourierTransform`, `affineCommonStageFourierTransform`,
  `fourierAffineModel`, `fourierModelFst`, `fourierModelSnd`,
  `fourierWeilTensorFunctor`, `fourierModelWeil`, and their geometry helpers.
- `Sheaf.Paper.FourierAdicArtinSchreier`:
  `fourierAdicArtinSchreier`, `fourierAdicArtinSchreier_mem`,
  `fourierAdicKernel`, `fourierCoefficientStage`, `fourierCoefficient`.
- `Sheaf.Paper.FourierTraceFormula`: `fourierTraceBaseCharacter`, the existing
  trace-composition character, reused rather than redefined.
- `Sheaf.Paper.QbarCurveOrdinaryImage`: `qbarCurveOrdinaryPushforward`,
  `qbarCurveShiftedOrdinaryImage`, `qbarCurveOrdinaryAdjunction` and the
  imported `Scheme.MiddleExtensionCurve` datum.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlWeilPull`, `zlFrobeniusSquare`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilComplex`, and `sfCommonStageWeilForget`.
- `Sheaf.Paper.AdicPunctualWeights`: `SfIsPunctuallyPureOfWeight`, including
  its `SfPunctualEigenvalue` and actual finite-stage Frobenius definition.
- `Sheaf.Paper.CommonStageLisse`: `HasCommonStageLisseLattice`.
- Both repaired dependency modules are imported and their declarations used.
  The originally recorded ordinary-image and upstream nonexceptionality
  interfaces remain available through public imports; they are not overwritten
  by private copies. The main module also imports every presently recorded
  proof prerequisite module. The unrecorded energy and local-power statements
  are retained in the docstring's proof plan rather than invented as hypotheses.

Edge cases checked: whole-line opens and empty complement are allowed; an empty
open fails density. A zero input fails hMnonzero, while a zero partner is not
silently excluded by an extra assumption. Zero and all algebraic-closure scalars
are included in constituent exclusion; scalar a need not descend to k0. An
arbitrary ψ whose restriction to Fp is trivial is still covered by the trace
pairing scalar, without using ψ restricted to Fp as the projector character.
The explicit shift unit uses the trivial character and zero function and is
constant rank one. The characteristic helper for this construction concerns the
nonempty arithmetic affine line, not arbitrary possibly empty curves. The
ordinary-image functor itself remains general for every MiddleExtensionCurve.
Negative, zero and fractional real weights, repeated eigenvalues and
nonsemisimple Frobenius are included. There is no Frobenius-stable lattice
hypothesis. No mathematical dispute or node correction remains.

Searches made (including the retained earlier searches in searches.jsonl):

- `msearch.py`, LeanFinder: “Fourier Deligne transform upper weight bound common
  stage Weil sheaf”: eight unrelated sieve and Lie-weight results, no match.
- `msearch.py`, Loogle: `"CommShift", "rightAdjoint"`: general shift/adjunction
  declarations only; none supplies ordinary middle extension on this Weil heart.
- `msearch.py`, grep:
  `SfIsNonexceptional|qbarCurveWeilOrdinary|commonStagePullbackShift`: zero hits.
- `msearch.py`, Loogle: `"AddChar", "mulShift"`: the existing multiplicative
  scaling API and injectivity of primitive-character shifts; no common-stage
  Fourier theorem or completed character-constituent definition.
- Earlier retained LeanSearch query “Fourier partner pure lisse Weil sheaf
  weight at most w plus one”: analytic Fourier declarations only.
- `rg` in Mathlib, the upstream WeilConjectures source and `lean/Sheaf` for
  `SfAffineLineOpen`, `SfIsConstituentNonexceptional`,
  `qbarAffineWeilShift`, and common-stage Fourier-weight names found no existing
  declarations with these interfaces. The older upstream FourierWeight theorem
  was found and read, but is unusable for the reason in the return.
- Searches for lisse, shift, ordinary image and Frobenius interfaces in
  `lean/Sheaf/Paper` found and reused CommonStageLisse, QbarCurveOrdinaryImage,
  WeilIndSheafCategory and CommonStageFourierTransform. In particular the
  geometric lisse-lattice definition was not duplicated.

## Dependency modules

`def-wf-middle-extension`: `CommonStageCurveWeilMiddleExtension` publicly retains
the prior QbarCurveOrdinaryImage module. Its new ordinary Weil-heart right
adjoint supplies the missing fixed-pair ordinary image. The named existence
obligation determines the functor with its adjunction up to unique compatible
isomorphism; this is a universal-property construction, not an arbitrary map or
a mere choice of nonempty data. The forgetful theorem identifies its geometric
carrier with the recorded ordinary j_*. For the affine shift the construction
uses the existing completed Artin--Schreier sheaf for the trivial character of
the zero function: its invariant summand is canonically the constant coefficient
line, and shifting it arithmetically gives its normalized Weil structure.
Tensoring with it is actual cohomological [1], as the compatibility statement
records. The only postponed data are proofs, each named and documented under
this owning DAG node.

`def-a1-constituent-nonexceptional`: `CommonStageConstituentNonexceptional`
publicly retains the older upstream interface and supplies the definition on
the recorded common-stage heart. Its dense-open bundle is only the data already
in this node. Its character line is the explicit completed Artin--Schreier
projector for the geometric function ba x, where b uniquely represents the
actual arbitrary ψ through the finite-field trace pairing. Lisse subquotients
are tested in the actual geometric sheaf heart. This exactly expresses the
node's geometric Jordan–Hölder constituent condition and includes a=0. The
heart-membership and geometry obligations are named postponed theorems with
sources and complete natural-language proofs. No second lisse definition,
representation model or arbitrary Weil map is introduced.

Validation is by scompile.py on all three modules separately in dependency order,
then deliver2.py --no-push and the normal delivery wrapper. Only these prescribed
wrappers perform compilation, clone refresh and delivery bookkeeping. The worker
makes no changes in the shared source checkouts and runs no global build.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
