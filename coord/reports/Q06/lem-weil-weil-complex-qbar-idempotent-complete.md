## Worker report

The module `Sheaf.Paper.WeilComplexQbarIdempotentComplete` states
`WeilConjectures.weil_complex_qbar_idempotent_complete`.  It uses the existing
fixed-pair definition `WeilConjectures.sfCommonStageWeilComplex` for the
common-stage category of Qbar Weil complexes and Mathlib's
`CategoryTheory.Idempotents.toKaroubi` for the canonical Karoubi inclusion.  The
proof is `sorry`, as required at stage 2.

The theorem signature is:

```lean
theorem weil_complex_qbar_idempotent_complete
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    IsIdempotentComplete (sfCommonStageWeilComplex D l hl Y₀ Qbar) ∧
      (toKaroubi (sfCommonStageWeilComplex D l hl Y₀ Qbar)).IsEquivalence
```

The binders render the finite-field datum (`D`), a prime `l` and its primality
instance, the hypothesis `l ≠ D.p`, an algebraically closed coefficient field
`Qbar` over `Padic l`, and a finite-type k₀-scheme `Y₀` represented by an object
of `Over (Spec (CommRingCat.of D.k₀))` with the locally-finite-type and
quasi-compact instances.  The first conclusion is idempotent completeness of
the fixed-pair common-stage Weil category.  The second conclusion states that
the canonical functor `toKaroubi` from that category to its Karoubi envelope is
an equivalence.  The node's reviewed correction removed an `exact` assertion,
since the fixed-pair definition carries no triangulated structure; the Lean
statement follows that corrected node verbatim in content.

Statement dependencies used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum`.
- `def-weil-weil-sheaf-complex`: `Sheaf.Paper.SfWeilSheafComplex`,
  `WeilConjectures.sfCommonStageWeilComplex` (the node's fixed-pair category).
- `def-weil-karoubi-envelope`: Mathlib declaration
  `CategoryTheory.Idempotents.Karoubi` and its canonical functor
  `CategoryTheory.Idempotents.toKaroubi`.

The proof dependency `lem-weil-qbar-idempotent-complete` is imported from
`Sheaf.Paper.QbarIdempotentComplete`; it supplies idempotent completeness of
the underlying common-stage constructible category.  The proof docstring
explains the induced Frobenius structure on a retract and the resulting
Karoubi essential surjectivity.  No new nodes or dependency repairs were
needed.

Edge cases checked against the reviewed proof are the zero and identity
idempotents, the empty geometric fibre (including empty `Y₀`), block-diagonal
Frobenius structures, and diagonal summands stable under Frobenius.  All are
covered by the fixed-pair and Karoubi formulations.  The universe parameters
`u` and `v` are explicit and preserve the independent scheme and coefficient
universes.

Searches made:

- `msearch.py ... leanfinder "idempotent complete common stage Weil complex Qbar fixed pair category Karoubi equivalence"`: only generic Mathlib Karoubi/homological-complex results; no declaration of this theorem.
- `msearch.py ... loogle "IsIdempotentComplete, toKaroubi, sfCommonStageWeilComplex"`: no hits (the tool did not recognize `IsIdempotentComplete`).
- `rg -n 'sfCommonStageWeilComplex|toKaroubi|IsIdempotentComplete'` over the project and slopmaster2 source: found the fixed-pair definition, the underlying `qbar_idempotent_complete` theorem, and generic Karoubi declarations, but no duplicate theorem.
- Mathlib source inspection of `CategoryTheory.Idempotents.Basic` and `Karoubi`: `IsIdempotentComplete`, `toKaroubi`, and its equivalence instance match the stated categorical notions.

Compilation with `scompile.py Q06 lem-weil-weil-complex-qbar-idempotent-complete`
passed with no errors or warnings (the expected `sorry` warning is suppressed by
`warn.sorry false`).

## Second reading by Q06

Independent maintainer second reading of immutable delivery
`2f4a456b309d0415e6fd34ab3cc88cc497eb1a72`, 2026-10-17. This section replaces
the delivered placeholder; it records the actual reading performed for landing.

Each object, hypothesis and conclusion was checked with the node and Lean open:

- The tuple p,a,q,k₀,k is `D : FiniteFieldDatum.{u}`. Its fields require p prime,
  a ≥ 1, q = p^a, a finite field k₀ of cardinality q, and its algebraic closure k.
  The existing `FiniteFieldFiber` module supplies the actual geometric base change.
- `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` are precisely the prime and
  unequal-characteristic hypotheses; there is no extra invertibility hypothesis.
  `SfWeilSheafComplex` derives invertibility on the geometric fibre from these data.
- `Qbar : Type v`, its field and `Algebra (Padic l) Qbar` instances, and
  `[IsAlgClosure (Padic l) Qbar]` give an algebraic closure, including algebraicity,
  rather than only an arbitrary algebraically closed extension.
- `Y₀ : Over (Spec (CommRingCat.of D.k₀))`, with `LocallyOfFiniteType Y₀.hom`
  and `QuasiCompact Y₀.hom`, means exactly a finite-type k₀-scheme. No
  separatedness, smoothness, connectedness or nonemptiness is assumed.
- `sfCommonStageWeilComplex D l hl Y₀ Qbar` is the recorded fixed-pair category
  `IsoAlgebra (sfCommonStageWeilFrobeniusPullback ...)`, over the actual
  `generalAlgebraicallyClosedConstructibleCategory` on `D.geometricFiber Y₀`.
  Its underlying category is literally `GeneralAlgebraicallyClosedCoefficients.Pair`.
  The pullback is the recorded common-stage pullback along geometric Frobenius.
  The upstream `IsoAlgebra` and Mathlib `Algebra.Hom` declarations show that
  morphisms are the underlying arrows satisfying the Frobenius commuting square;
  this is not the derived category of Weil sheaves or an arbitrary replacement.
- `IsIdempotentComplete ...` states that every idempotent splits. The second
  conjunct `(toKaroubi ...).IsEquivalence` uses Mathlib's actual canonical
  inclusion, which sends K to (K,1) and f to f. Both clauses match exactly.

The three statement-dependency JSON nodes were read in the immutable snapshot,
including their statements and Lean/Mathlib records. The exact dependency sources
read were `Sheaf.Paper.FiniteFieldFiber`, `Sheaf.Paper.SfWeilSheafComplex`,
`WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`, and Mathlib
`CategoryTheory/Endofunctor/Algebra.lean`, `Idempotents/Basic.lean`, and
`Idempotents/Karoubi.lean`. The proof input
`Sheaf.Paper.QbarIdempotentComplete.qbar_idempotent_complete` has precisely the
underlying common-stage category and allows independent u,v. Its finite-type
hypothesis holds after geometric base change. `DerivedPullbackTensorHom` determines
the common-stage pullback by its object and representative formulas using a
unique-existence theorem; no arbitrary map or hollow choice is introduced here.

The master blueprint source has an older erroneous identification with a derived
category of Weil sheaves and says “exact equivalence.” The immutable DAG already
contains the reviewed stage-1 correction to fixed pairs and categorical equivalence.
The slopmaster2 text, chapter `05_adic_weil_reviewed.tex`, definition
`def:weil-complex`, explicitly defines a pair (K,phi:F* K ≅ K), supporting that
correction. This delivery makes no new statement correction and requires no new
stage-2 citer audit. No triangulated structure is asserted in the Lean.

Mathematical proof check: for a splitting i:L→K, r:K→L, with ri=1 and ir=e,
the structure r theta T(i) has inverse T(r) theta⁻¹ i. The commuting equation
for e makes their composites ri and T(ri), and makes i,r Frobenius-compatible.
This works for any endofunctor and introduces no extra exactness assumption.
The splitting identifies the envelope object (K,e) with (L,1); full faithfulness
of `toKaroubi` gives the equivalence. The additive structure comes from the
recorded additive pullback and inherited zero objects and biproducts.

Edge cases: zero and identity idempotents; the zero object; empty Y₀ and geometric
fibre; finite-type schemes that are not separated; block-diagonal Frobenius and
Frobenius-stable diagonal retracts; every allowed p and l, including l=2 when
p≠2; and independent scheme/coefficient universes u,v. All remain covered.
There is no index-set or degree parameter that could exclude an empty or degree-zero
case. No universe equality or hidden extra typeclass binder is present.

Independent text searches for `sfCommonStageWeilComplex`,
`weil_complex_qbar_idempotent_complete`, `IsoAlgebra` with idempotent completeness,
and Weil/idempotent combinations in `lean/Sheaf`, upstream `WeilConjectures`, and
Mathlib found no duplicate of the whole statement. The existing generic
`toKaroubi_isEquivalence` gives only the second clause assuming the first. The
node records LeanSearch, Loogle and LeanFinder queries as well; the worker report
records its own search evidence. No notion is defined again in this module.

Findings and corrections: H11 (also the substantive-reading requirement of H1):
the original second-reading section was only a placeholder. Replaced it with this
actual clause-by-clause independent reading, preserving the Worker report. H8:
the proof docstring compressed away the finite-type base-change and additive
structure steps and gave no retract formulas. The complete replacement module
now records all four DAG proof steps, formulas, and dependency references.
No signature, theorem body, imports, or node record changed.

Validation: both original and replacement signatures were compared programmatically
with `lean.statement` and agree verbatim. The replacement obeys the 100-character
line limit, retains source-place and blueprint docstrings, has `autoImplicit false`,
and has only the named theorem with proof `by sorry`; it contains no definition.
Original per-file `scompile.py` reproduction returned exit 0 with no diagnostics:
sandbox 2.1 s, intended library module 2.2 s. The complete replacement at
`fixes/lean/Sheaf/Paper/WeilComplexQbarIdempotentComplete.lean` also returned exit 0
with no diagnostics: sandbox 2.1 s, intended library module 2.3 s. Both use the
installed wrapper's server side overlay and default 60-second per-file limit.
No global build, direct ssh command, Git mutation, live Lean write, or project
clone edit was performed. All fixes are complete replacement files in the
`merge_delivery.py --stage 2 --apply-fixes` format.
