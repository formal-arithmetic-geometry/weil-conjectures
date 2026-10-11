## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleResiduePolynomialLift` states
`AlgebraicGeometry.residue_polynomial_lift`. It binds a commutative ring `R`, a prime
ideal `p`, a field `L` with finite (`Module.Finite`) separable (`Algebra.IsSeparable`)
extension structure over `p.ResidueField`, and an element `α` generating `L` as an
algebra over the residue field. The conclusion gives `c : R` outside `p` and a monic
`f : Polynomial R` whose coefficient map along `algebraMap R p.ResidueField` equals
the minimal polynomial of `algebraMap p.ResidueField L (algebraMap R p.ResidueField c) * α`.
The clauses `c ∉ p`, monicity, polynomial mapping, and minimal-polynomial identity are
rendered directly by the corresponding conjuncts in the theorem signature. The finite
separable field-extension hypothesis is rendered by `[Module.Finite p.ResidueField L]`
and `(hsep : Algebra.IsSeparable p.ResidueField L)`; generation is
`Algebra.adjoin p.ResidueField ({α} : Set L) = ⊤`.

Dependencies use Mathlib declarations: `Ideal.ResidueField` and `Localization.AtPrime`
for `def-weil-pbc-localization-at-prime`, `Algebra.IsSeparable` and `minpoly` for
`def-weil-pbc-separable-algebraic-extension`, `Algebra`/`Module.Finite` for
`def-pc-field-extension`, and `Polynomial` for `def-weil-polynomial-ring`.

Edge cases checked: `c` is explicitly required outside the prime ideal; the residue
field and extension may be any universe levels; the generator may be any element and
no nonzero-degree assumption is added. No exact existing project declaration or
single Mathlib theorem packages this lift.

Searches: `msearch.py leanfinder` for denominator clearing and lifted minimal
polynomials (only `Polynomial.map`, localization APIs, and minpoly scaling results);
`msearch.py loogle`/grep for `Localization.AtPrime`, residue fields, separability,
and polynomial lifting (Mathlib primitives only); `rg` over `WeilConjectures/` and
`lean/Sheaf` found no matching declaration. The theorem is therefore stated with
`sorry` as required for stage 2.

## Earlier second reading (a previous round; superseded)

The file and node were reread against the source statement. Every source hypothesis is
present: commutative `R`, prime `p`, finite separable field extension `L/κ(p)`, and a
generator `α`. The conclusion has exactly the existential `c ∉ p`, monic polynomial
`f ∈ R[T]`, and equality after coefficient mapping to the minimal polynomial of `cα`.
No mismatch was found.

## Second reading by C1

I reread the node `lem-weil-pbc-etale-residue-polynomial-lift`, its dependency
records, the source at Stacks Tag 00UD (Algebra, proof of Lemma 10.144.3), and
the Lean declaration.

The node's objects, hypotheses, and conclusion match as follows:

- A commutative ring `R` is `(R : Type u) [CommRing R]`.
- A prime ideal `𝔭 ⊂ R` is `(p : Ideal R) [p.IsPrime]`; its residue field is
  Mathlib's `p.ResidueField`, supplied by the localization-at-prime dependency.
- A finite separable field extension `L/κ(𝔭)` is `(L : Type v) [Field L]`,
  `[Algebra p.ResidueField L]`, `[Module.Finite p.ResidueField L]`, and
  `(hsep : Algebra.IsSeparable p.ResidueField L)`.  These are precisely the
  finite and separable hypotheses of Tag 00UD; no Noetherian, domain, or
  characteristic hypothesis is added.
- The primitive element `α ∈ L` is `(α : L)` with
  `hgen : Algebra.adjoin p.ResidueField ({α} : Set L) = ⊤`, exactly
  `L = κ(𝔭)[α]` in the source.
- The conclusion is `∃ c : R, c ∉ p ∧ ∃ f : Polynomial R, f.Monic ∧ ...`.
  The final equality uses `Polynomial.map (algebraMap R p.ResidueField) f` and
  equals `minpoly p.ResidueField
  ((algebraMap p.ResidueField L) (algebraMap R p.ResidueField c) * α)`,
  which is the source's minimal polynomial after replacing `α` by `cα`.
  Quantifier order and all conjunctions agree with the node.

The edge cases are covered: `c ∉ p` is explicit; no nonzero-degree assumption
or characteristic restriction is introduced; `R`, `L`, and the residue field
may inhabit arbitrary universe levels; the zero/empty-generator cases are not
silently admitted because `hgen` requires the indicated adjoin to be `⊤`.
The finite extension may have degree one, as the source permits.

I searched with `msearch.py` (LeanFinder and Loogle queries for residue-field
polynomial lifting and minimal-polynomial scaling), and with `rg` over
Mathlib, `WeilConjectures/`, and `lean/Sheaf/`.  The searches found only
primitive ingredients (`Polynomial.map`, localization and residue-field APIs,
and minpoly scaling lemmas), and no declaration of this statement.  The
recorded dependency declarations are the appropriate notions: `p.ResidueField`
and `Localization.AtPrime`, `Algebra.IsSeparable`/`minpoly`, `Algebra` with
`Module.Finite`, and `Polynomial`.

No mismatch was found, so no Lean or node statement change was needed.  The
module was compiled with
`python3 /home/ubuntu/weil-launcher/scompile.py C1
lem-weil-pbc-etale-residue-polynomial-lift
lean/Sheaf/AlgebraicGeometry/EtaleResiduePolynomialLift.lean`, with no errors
or warnings beyond the permitted `sorry` declaration warning.
