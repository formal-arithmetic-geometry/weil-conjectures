## Worker report

The module `Sheaf.TraceFormula.AbhyankarFiniteTypeFieldHeight` states the
Abhyankar height bound for valuations of a field finitely generated over its
prime field.  The theorem is `abhyankar_finite_type_field_height`; its proof is
`sorry`, as required for stage 2.  The declaration uses Mathlib's `Field`,
`Subfield`, `IntermediateField.FG`, `Algebra.trdeg`, `ValuationSubring`,
`PrimeSpectrum`, and `StrictMono`.

The Lean rendering of each hypothesis and conclusion clause is:

* `F : Type u`, `K : Type v`, `[Field F]`, `[Field K]`, and `[Algebra F K]`
  introduce the two fields and their field extension.
* `hprime : (⊥ : Subfield K) = (algebraMap F K).fieldRange` says that the
  image of `F` is the prime subfield of `K`, which is the source's phrase
  “over its prime subfield”.
* `hfg : (⊤ : IntermediateField F K).FG` says that `K` is finitely generated
  as a field over `F`.
* `d : ℕ` and `hd : Algebra.trdeg F K = d` introduce the finite numerical
  transcendence degree appearing in the bound.
* `A : ValuationSubring K` is a valuation ring in `K`; Mathlib's structure
  includes the subring and the alternative that each field element or its
  inverse lies in it, and it has fraction field `K`.
* `n : ℕ`, `p : Fin (n + 1) → PrimeSpectrum A`, and `StrictMono p` encode a
  strictly increasing finite chain of `n` strict inclusions of prime ideals.
* The conclusion `n ≤ d + 1` is the asserted height bound, with chain length
  counted by strict inclusions.

The statement dependencies used are `Field` (the Mathlib match recorded by
`def-weil-field`), `IntermediateField.FG` from
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, `Algebra.trdeg` from
`Mathlib.RingTheory.AlgebraicIndependent.Basic`, and `ValuationSubring` and
`PrimeSpectrum` from `Mathlib.RingTheory.Valuation.ValuationSubring`.

Edge cases checked before writing include the trivial valuation ring `A = ⊤`
(which has no nontrivial prime chain), a prime field with `d = 0` (the bound is
`n ≤ 1`), the mixed-characteristic example `K = F = ℚ` with
`A = ℤ_(p)` (one strict prime inclusion), and rank-two valuations on a rational
function field (chains of length at most two when `d = 1`).  The `Fin (n + 1)`
encoding also handles `n = 0` and empty strict chains.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "Abhyankar height bound for valuation rings of finitely generated fields over the prime field"`; the eight hits concerned arithmetic heights, finite-field valuation inequalities, or rank-one special cases, with no match.
* `msearch.py ... loogle "Algebra.trdeg, ValuationSubring, PrimeSpectrum, StrictMono"`; zero hits.
* `msearch.py ... grep "Abhyankar|abhyankar|finite_type_field_height" Mathlib/RingTheory/Valuation`; zero hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` for Abhyankar, valuation height, and the item id; no existing declaration states this theorem.  The only project occurrence is a proof-dependency reference in `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`.

The cited Temkin source is `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`,
§2.1, Corollary 2.1.3(i).  The local PDF is unavailable, so the source citation
is retained from the DAG node.  No statement fault or `STATEMENT-DISPUTED` was
found.

## Second reading by Q38

I reread the node and declaration independently.  `hprime` identifies the
base field with the prime subfield, `hfg` gives finite generation, and `hd`
turns the cardinal transcendence degree into the finite integer `d`.  A
`ValuationSubring K` supplies exactly a valuation ring of `K`; its associated
prime spectrum is the set of prime ideals of that ring.  A `StrictMono` map
from `Fin (n + 1)` is precisely a finite strict prime chain with `n` strict
inclusions.  The conclusion `n ≤ d + 1` matches the node clause by clause.
No mismatch was found.


## Maintainer independent review (2026-10-18)

The immutable declaration and its recorded Lean statement agree verbatim. The
independent reader checked the Field dependency and the exact Mathlib interfaces
for prime subfields, field generation, transcendence degree, valuation subrings
(including IsFractionRing), prime spectra and their ideal-inclusion order. The
independent universes u and v impose no size equality. All hypotheses and the
finite-chain conclusion match the node; no statement correction is needed.
The zero-length chain, empty chain, trivial valuation, characteristic p and the
mixed-characteristic prime-field case are covered. Finite-chain bounds also
exclude infinite chains by selecting a finite subchain of excessive length.

Independent Loogle search `ValuationSubring, Algebra.trdeg` found zero hits;
text searches for valuation/transcendence/height and Abhyankar across Mathlib,
WeilConjectures and project Lean found no duplicate theorem. The three proof
dependency nodes have no Lean records, so they require no imports at this stage.
There is no missing statement helper or universe repair.

Temkin's cited PDF was read online at
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf : §2.1 pp. 7–8,
including Lemma 2.1.2 and Corollary 2.1.3(i). It confirms the node's specialization.

H8 corrected: the replacement module adds the exact source place and all four
DAG proof steps to the theorem docstring. Its signature and sole `sorry` proof
are unchanged. No definitions or local proofs were added.

The original immutable file reproduced cleanly with scompile.py Q38
lem-trf-abhyankar-finite-type-field-height, on the wrapper's server side overlay:
sandbox 3.5 s, library 1.7 s, exit 0, no diagnostics. The installed wrapper
currently implements server overlay compilation rather than local compilation.
The replacement file also compiled cleanly through the same wrapper: sandbox
3.5 s, library 7.6 s, exit 0, no diagnostics. No global build or direct SSH command was run.
