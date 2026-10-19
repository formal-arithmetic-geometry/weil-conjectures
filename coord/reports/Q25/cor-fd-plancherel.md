## Worker report

The delivery states `WeilConjectures.weilFourierTrace_plancherel` in
`Sheaf.Paper.WeilFourierPlancherel`. Its only proof is `sorry`. It uses the
reviewed `WeilConjectures.weilTraceFunction`, on the actual common-stage adic
Weil-pair category. The node's statement, dependencies, and proof are unchanged.
There is one lean-only dependency repair, `sk-def-ft`, described below. There
are no new nodes and no statement correction.

Clause-by-clause reading:

| Source hypothesis or clause | Lean rendering |
| --- | --- |
| The standing finite-field setting, q=p^a, a>=1, k0=F_q and its fixed closure | `F : FourierSetting.{u}`, with `F.field` the recorded `FiniteFieldDatum` |
| A prime l distinct from p, the fixed Qlbar, and finite E containing mu_p | `F.coefficients` and `F.extension`, including their existing field/algebra/closure instances, `different`, `finiteExtension`, and `rootsOfUnity_mem` |
| The fixed nondegenerate additive character psi | `Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar`, `hΨ : Ψ ≠ 1`; as in sk-def-char, psi is Ψ composed with Tr_(k0/F_p). This is the source's fixed prime-field character, not an assumption that the restriction of a character to F_p be nontrivial. |
| Fix the field embedding iota:Qlbar -> C | `ι : F.coefficients.Qbar →+* ℂ`; a unital ring homomorphism out of a field is injective, so no separate injectivity hypothesis is needed. No topological or continuity hypothesis is imposed. |
| Every Weil complex K on A1 | `K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different (sfFourierLine F) F.coefficients.Qbar`; these are precisely the recorded fixed pairs, not the derived category of Weil sheaves. |
| Every n>=1 | `(n : ℕ) (hn : 1 ≤ n)` |
| FT_psi(K) with Laumon's rank-one shift [1] | `sfWeilFourierTransformObj F Ψ c K`; it is the actual adic p2! of p1*K tensored with the descended arithmetic Artin--Schreier kernel shifted by one. Moving the shift into the kernel uses the canonical tensor and compact-support shift identifications. |
| The compact-support construction | `c : Compactification (sfFourierSnd F).left`, arbitrary, is the choice used to compute the already recorded R p2!. It is computational data rather than an extra geometric condition: the affine projection admits compactification. The statement covers every choice. |
| Sum over y in F_(q^n) | `∑ᶠ y : F.field.extensionPoints (sfFourierLine F) n hn, ...`; the canonical affine coordinate identifies these over-Spec-k0 points with F_(q^n), a finite set. Thus this finsum is the finite sum in the source, with no infinite-support convention used in any allowed case. |
| The complex squared absolute value of the transformed trace | `‖ι (weilTraceFunction ... (sfWeilFourierTransformObj F Ψ c K) n hn y)‖ ^ 2`, an element of R |
| The factor q^n | `(F.field.q : ℝ) ^ n` |
| The input squared-trace sum | `∑ᶠ x : F.field.extensionPoints (sfFourierLine F) n hn, ‖ι (weilTraceFunction ... K n hn x)‖ ^ 2` |
| Equality of the two displayed quantities | The theorem's `=` in R |

The declaration docstring contains the complete node proof: apply the Fourier
trace formula; remove the shift's minus sign by the norm square; expand using
complex conjugation; turn conjugates of roots of unity into inverse characters;
apply orthogonality on the difference x-x'; identify the diagonal contribution
with q^n times the input sum. No purity or weight hypothesis is added.

Dependency declarations read and used:

- `sk-def-trace`: `Sheaf.Paper.FourierTraceFunctions`,
  `WeilConjectures.classicalFiniteFieldFourierTransform` and
  `fourierTraceExtensionFintype`. Its trace clause is the public dependency
  `Sheaf.Paper.WeilComplexTraceFunction`, `WeilConjectures.weilTraceFunction`.
  I read the full signatures and the uniqueness specification
  `weilTraceFunction_existsUnique`. The trace is the alternating local trace on
  every finite-stage Weil model, descending to the common-stage pair.
- `sk-def-ft`: the closed audit names
  `WeilConjectures.FourierTransform.Defs`,
  `AlgebraicGeometry.Etale.fourierTransform`. I read its whole definition and
  docstring using `scompile.py --source`. It is retained in the dependency
  module's public imports and mixed `lean.declarations`. Its domain does not
  accept the common-stage Weil pairs, requiring the specialization below.
- The specialization uses `Sheaf.Paper.FourierAdicArtinSchreier`:
  `fourierAdicArtinSchreier`, `fourierAdicArtinSchreier_mem`,
  `fourierCoefficientStage`, and `fourierCoefficient`; these construct real
  completed integral data and rationalize at the fixed coefficient field.
- `Sheaf.Paper.CommonStageWeilShriek`, `zlComplexShriek` and
  `zlShriekFrobenius`, give compact-support image on the same fixed pairs.
  Its open/proper factors are determined by adjunction; their Frobenius
  comparisons are the actual mates, not unspecified natural isomorphisms.
- `Sheaf.Paper.WeilIndSheafCategory`, `zlFrobeniusSquare` and `zlPullComp`,
  give the normalized geometric-fibre inverse-image comparisons.
  `FiniteFieldDatum.galoisMap_projections` from
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed` gives the arithmetic descent
  equation used for the kernel's Frobenius structure.
- `Sheaf.Paper.CompletedPullbackTensorComparison`,
  `canonicalCommonStagePullbackTensor`, and
  `Sheaf.Paper.DerivedPullbackTensorHom`, `commonStageDerivedTensor`, give
  tensor of carriers and the tensor of the two existing Weil maps.
- `GeneralAlgebraicallyClosedCoefficients.shiftPair` gives the literal
  finite-stage cochain shift of the kernel, with no change of coefficient stage.
- The proof-plan imports are the published
  `WeilConjectures.WeilSheaf.FourierTrace` and
  `WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter`.
  The latter supplies `AddChar.sum_compTrace_sub_mul` and
  `sum_const_mul_eq_ite` for the audited `sk-lem-orthogonality`.
  The former's current Fourier-trace theorem is expressed in the old Weil
  category; its proof is relevant, but this delivery does not claim that it
  already proves the new fixed-pair statement.

Searches made (2026-10-18):

- `msearch.py ... leanfinder "Plancherel identity for trace functions of Fourier Deligne transforms of Weil complexes over finite fields"`: eight hits on Jacobi/Gauss sums and generic character inner products; no exact theorem for the required category.
- `msearch.py ... loogle "AddChar, fourierTransform, Complex.normSq"`: zero hits, unknown identifier `fourierTransform`.
- `msearch.py ... grep "Plancherel|sum_norm_sq_fourierTransform" Analysis/Fourier`: two analytic Plancherel hits in `LpSpace.lean` and `FourierTransform.lean`, neither a Weil-complex trace statement.
- `rg` for `cor-fd-plancherel|Plancherel|traceEnergy_fourierTransform` in the specified upstream source and `lean/Sheaf`: the old Fourier-weight comment, but no local theorem file. `scompile.py --source WeilConjectures.WeilSheaf.FourierPlancherel` found the live upstream `AlgebraicGeometry.WeilComplex.traceEnergy_fourierTransform`. I read it, `traceEnergy`, `affineLineTraceFunction`, `traceFunction`, and the full category definition. The numerical formula is identical, but `AlgebraicGeometry.WeilComplex` is bounded constructible objects in the derived category of pro-etale Weil sheaves. The recorded `sfCommonStageWeilComplex` is instead fixed pairs in the constructible derived category; `SfWeilSheafComplex.lean` explicitly distinguishes these constructions. Binding the old theorem would change K's category and bypass the reviewed trace declaration.
- `rg` for Fourier/Weil transforms in `lean/Sheaf/Paper` found the recorded `WeilFourierTransform` and `WeilFourierInversion`. These also take the old `AlgebraicGeometry.WeilComplex`; they do not provide the needed common-stage object. The already landed `FourierAdicArtinSchreier` supplies the missing kernel data and is reused, not copied.
- `rg` over the named source directories for common-stage tensor, shift, Frobenius and shriek found the exact existing operations listed above. The new definitions only compose them.

Edge cases checked before and after writing:

- n=1 is allowed. n=0 is excluded explicitly by the source and by the existing
  extension-field and trace interfaces, rather than silently given a junk field.
- The zero complex gives zero on both sides. Arbitrary shifts change signs in
  trace but do not change the norm-square identity. The single [1] shift is
  built into the actual kernel; it is not omitted.
- Characteristic two is allowed: only l differs from p. No odd-characteristic
  or sign assumption is used. Coefficient-prime primality is explicitly bound
  in the helper `sfFourierArithmeticPrime_isUnit`: merely l != p would not
  suffice for a composite integer divisible by p.
- The nontrivial-character condition is essential and is the standing
  sk-def-char convention. For a trivial character and the constant trace-one
  function, the left side is q^(3n), whereas the right side is q^(2n). For nontrivial Ψ, the induced extension characters are
  nontrivial by surjectivity of finite-field trace, including when p divides n.
- A delta input at zero has transformed absolute value one at every one of
  q^n points, giving q^n on both sides. The constant trace-one input has
  transformed trace supported at zero with magnitude q^n, giving q^(2n).
- There are no empty or infinite indexing cases for the affine line's rational
  points; these are exactly the finite extension field. No finite enumeration
  or coordinate bijection is chosen as new data.
- The field embedding need not be continuous or preserve an l-adic norm.
  Only the complex norm after iota occurs, and roots of unity map to roots of
  unity. The arithmetic and coefficient closures are the setting's fixed ones.
- The kernel construction handles the trivial character too; only the
  Plancherel theorem assumes nontriviality. All compactifications and all
  fixed-pair Weil objects are included.

The two modules compile separately in dependency order through the prescribed
`scompile.py Q25 cor-fd-plancherel ...` wrapper, within 60 seconds per file.
No source-tree edits, direct git commands, global builds, proofs, or additional
axioms were used. The sandbox is the only place written by this worker.

## Dependency modules

`sk-def-ft`: `Sheaf.Paper.CommonStageWeilFourierTransform` repairs only the
node's `lean` record. The audited general `Etale.fourierTransform` is retained
and listed as an existing declaration next to the module's helpers: it is the
exact general ordinary-etale functor, with arbitrary coefficients, schemes,
pairing, compactification, and integer shift. It does not act on the adic
common-stage fixed pairs required here. The module supplies that application's
object construction, `sfWeilFourierTransformObj`, on the existing category.
It uses actual `fourierAdicArtinSchreier` data on the arithmetic plane, the
recorded rational localization and stage inclusion, the kernel's shift by one,
and its arithmetic-descent Weil isomorphism. Tensor uses the canonical
pullback/tensor comparison and the two given Weil isomorphisms. Compact support
is exactly `zlComplexShriek`. The two postponed geometric assertions state
only properties needed by these constructions, with complete proof docstrings:
coefficient-prime invertibility on the arithmetic model, and quasi-compactness,
Noetherianity and characteristic of the arithmetic plane. All definitions have
real data. These helpers belong to the Fourier construction, as authorized by
the missing-helper rule, and introduce no separate mathematical notion.

## Second reading by Q25

This is a separate in-session rereading of both node copies and both files;
the dispatcher explicitly forbids starting other agents. The maintainer's
independent review remains the independent reading of this delivery.

I checked every row of the clause table against the unchanged source statement.
The original upstream match was rejected because its K had a different category.
The final theorem now takes precisely the fixed pairs used by the recorded
trace dependency and computes both traces by `weilTraceFunction`. I expanded
the transform definition: the first projection is p1, the second is p2, the
arithmetic section is the product of their coordinates, the integral character
is the published unique integral lift of Ψ, [1] is retained, and Frobenius is
arithmetic descent followed by tensor comparison and the shriek mates. No
unconstrained map or existentially chosen object supplies any of these data.
The use of prime-field Ψ agrees with the source's fixed trace-induced psi.
The finsum is over all rational points of the affine line, not closed points,
Galois orbits, or only points of exact degree n. The scalar is q^n in R, with
no normalization factor or missing sign. The dependency's generic ordinary
functor remains publicly imported rather than being silently replaced by the
rank-one application. During rereading I made the prime hypothesis explicit
in the arithmetic invertibility helper: a section-local unused instance would
otherwise be omitted from its elaborated signature. I checked both helpers'
source hypotheses, all namespaces and universe binders, and the unchanged JSON
fields. No remaining statement mismatch or STATEMENT-DISPUTED issue was found.
