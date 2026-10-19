## Worker report

The module `Sheaf.SecTraceFormula.RationalValuationLinearResidue` states the
normalized linear-coordinate result from Temkin, Proposition 4.3.1, proof, p. 28.
It uses Mathlib's `ValuationSubring` for the valuation ring and `FractionRing`
axioms (`[Algebra (Polynomial K) F]`, `[IsFractionRing (Polynomial K) F]`) for
`K(t)`. The helper `rationalValuationIntersection` is the restriction of `O`
to `K`; `rationalValuationIntersectionMap` is its canonical inclusion into `O`;
`rationalValuationResidueMap` is the induced residue-field map. The named theorem
`rationalValuationIntersectionMap_isLocal` postpones only the elementary local-map
proof. `rationalValuationClosedCentre` is the canonical comap of the maximal ideal
along evaluation of `R[T]` at `t`, together with maximality and contraction to
`m_R`.

The hypotheses are rendered as follows. `K` and `F` are fields, `IsSepClosed K`
is separable closedness, `[Algebra K F]` and `[Algebra (Polynomial K) F]` identify
the constant and polynomial embeddings, `[IsFractionRing (Polynomial K) F]`
identifies `F` with the rational function field, and
`[IsScalarTower K (Polynomial K) F]` makes those embeddings compatible. `t : F`
and `O : ValuationSubring F` are the indeterminate and valuation subring. The
residue transcendence-degree hypothesis is the exact cardinal equation
`@Algebra.trdeg ... (RingHom.toAlgebra (rationalValuationResidueMap K F O)) = 1`.

The first conclusion is `∃ a : K, π : Kˣ, z : Oˣ`; the equation in the module is
`(z : F) = (t - algebraMap K F a) / algebraMap K F (π : K)`. Its final conjunct
states that every nonzero polynomial over `κ(R)` evaluates nonzero at the residue
of `z`, using `rationalValuationResidueMap`, which is exactly transcendence of the
residue. The closed-centre clause is universally quantified over `ht : t ∈ O`,
then assumes `rationalValuationClosedCentre K F O t ht`; it returns `a, π : R`
with `π ≠ 0`, a unit `z : Oˣ` satisfying the same normalized equation, and the
same polynomial nonvanishing condition. Thus the `t ∈ O` and maximal-contraction
assumptions apply only to the second clause.

Dependencies used from the DAG are the recorded Mathlib declarations:
`Mathlib.FieldTheory.IsSepClosed.IsSepClosed`,
`Mathlib.RingTheory.AlgebraicIndependent.Basic.Algebra.trdeg`,
`Mathlib.Algebra.Algebra.Defs.Algebra`,
`Mathlib.RingTheory.Valuation.ValuationSubring.ValuationSubring`,
`Mathlib.Algebra.Polynomial.Basic.Polynomial`, and
`Mathlib.AlgebraicGeometry.Scheme.residueField` (the last is represented in the
statement by the local-ring residue-field construction required for valuation
rings). The proof imports listed in the node are not needed by the stage-2 body;
the theorem proof is `sorry` as required.

Edge cases checked: `π : Kˣ` and the closed-clause `π ≠ 0` exclude zero scales;
`Oˣ` makes the normalized coordinate a unit; the polynomial condition includes
all nonzero polynomials and hence handles constant and degree-zero cases; the
statement does not exclude empty or trivial polynomial supports; no finiteness,
characteristic, or algebraic-closedness assumption is added to the residue field.
The unrestricted clause has no assumption `t ∈ O`, matching the source's separate
closed-centre clause.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
“Existence of a normalized linear rational function with transcendental residue
for a valuation on a rational function field” returned only fixed Laurent-series
or infinity-valuation constructions; `msearch.py ... loogle` with query
`Valuation, RatFunc` returned fixed `RatFunc` valuation declarations; grep of
Mathlib for `Gauss.*[Vv]aluation|residually.*transcend|transcend.*residue` found
only `Mathlib/RingTheory/QuasiFinite/Polynomial.lean`; grep of
`WeilConjectures/` and `lean/Sheaf/` found no declaration of this proposition.
These results do not state the translated-and-rescaled coordinate theorem, so a
new module was necessary.

## Second reading by Q15

I reread the node and the complete module. The Lean theorem has the same six
statement dependencies and keeps the source's two-part conclusion: an unrestricted
normalized coordinate followed by the implication whose hypotheses are `t ∈ O`
and maximality/contraction of `m_O ∩ R[t]`. The first part uses `Kˣ` for the
nonzero scalar and `Oˣ` for the unit coordinate; the second uses elements of the
intersection valuation ring and explicitly requires nonzero scale. The residue
condition is rendered clause-by-clause as nonvanishing of every nonzero polynomial
under the canonical residue map. No mismatch was found.

## Statement corrected

The returned H3 review identified two mismatches in the Lean rendering. The corrected
module now binds `hX : t = algebraMap (Polynomial K) F Polynomial.X`, explicitly
identifying the variable used in the rational-function coordinate with the canonical
polynomial indeterminate in the chosen fraction-field presentation. This is the
source's $K(t)$ variable, rather than an arbitrary element of the fraction field.
The closed-centre existential now has both
`π ≠ 0` and
`π ∈ IsLocalRing.maximalIdeal (rationalValuationIntersection K F O)`, rendering
$0\ne\pi\in\mathfrak m_R$ exactly. The item node's `statement_change` records the
old statement, source place, and the sole citer `lem-trf-single-valuation-semistable-extraction`;
its use remains valid because its $t$ is the polynomial indeterminate and supplies
this identification.

## Second reading by Q15

I reread the corrected node and module. The field and fraction-field hypotheses are
unchanged, and `hX` identifies `t` with `Polynomial.X` transported by the declared
algebra map. The unrestricted clause still quantifies `a : K`, a unit scale
`π : Kˣ`, and `z : Oˣ`, with the same residue-polynomial nonvanishing condition.
The closed-centre implication still assumes `t ∈ O` and the maximal-contraction
predicate; its scale now explicitly satisfies nonzeroness and membership in the
maximal ideal of the constant intersection, while `a` remains in that intersection.
No hypotheses or residue clauses were dropped. The correction directly addresses
both H3 findings from the immutable review.


## Maintainer second reading and canonical-interface repair

The immutable delivery ccf68d8fa7f5299b7b1e01391d657e57a109ef9d was read
independently against its node, all six statement dependencies, and Temkin,
Proposition 4.3.1, second stage, printed p. 28. The replacement keeps the two
conclusion clauses and the explicit indeterminate identification.

The original restriction, inclusion, locality theorem and residue-map helpers
repeat the published ValuationSubring.comap, comapInclusion,
comapInclusion_isLocalHom and comapResidueFieldMap. Their exact definitions were
read in Mathlib/RingTheory/Valuation/ValuationSubring.lean and the group clone's
Sheaf/FieldTheory/AbhyankarInequality.lean. The canonical residue algebra interface
is recorded by def-trf-valuation-comap-residue and reexported from
Sheaf/RingTheory/ValuationComapResidue.lean. The replacement imports and uses those
objects directly. They implement the valuation restriction and residue quotients
already explicitly specified in the item's statement, and the latter interface's
statement dependencies are the already cited field and residue-field nodes.
No new notion, new axiom, or extra locality assumption is introduced.

H4 is repaired by removing the duplicate constructions. The extra postponed
locality theorem without its own matching DAG statement disappears with them.
H8 is repaired by replacing the proof-name list with the six actual proof steps,
including the inverse test, the finite closed-centre residue extension, the
argument placing a in R, and the positive-scale normalization. Available recorded
proof-dependency modules are imported. The field universes are independent u and v;
all implicit variables are disabled. The record's declaration list and statement
are updated to the replacement module.

Hypothesis and conclusion audit:

- Fields and separable closedness: Field K, Field F and IsSepClosed K reuse the
  recorded field and separably-closed declarations.
- Chosen rational-function presentation: Algebra (Polynomial K) F and
  IsFractionRing (Polynomial K) F, with IsScalarTower K (Polynomial K) F for
  constants; hX identifies t with the actual image of Polynomial.X.
- Valuation ring and intersection: ValuationSubring F and O.comap (algebraMap K F).
  Mathlib supplies the local-ring and fraction-ring instances for valuation rings.
- Residue transcendence degree: the exact cardinal equation trdeg = 1 uses the
  canonical comapResidueFieldMap.toAlgebra, with no arbitrary residue embedding.
- Unrestricted coordinate: a : K, scale : Kˣ, z : Oˣ and the displayed equation;
  all nonzero residue-field polynomials evaluate nonzero under that canonical map.
- Closed centre: only this implication assumes ht : t ∈ O. The comap of m_O
  under evaluation R[T] → O is maximal and contracts under C to m_R. Since hX
  makes evaluation injective, this is precisely the prime in the node's R[t].
- Integral coordinate: a and scale belong to O.comap (algebraMap K F); scale is
  explicitly nonzero and belongs to its maximal ideal. The returned O-unit has
  the same coordinate equation and the full transcendence condition.

The original statement_change.old_statement equals the parent node verbatim.
The only actual statement/proof citer is
lem-trf-single-valuation-semistable-extraction, whose Step 5 was read: its t is
the affine-line polynomial coordinate, so hX holds. Its closed chart image gives
the maximal-centre hypothesis and its use still holds. There is no second direct
citer to audit. Other occurrences are provenance fields, not dependency edges.

Edge cases: zero scale is excluded in both clauses; z is a unit, including when
its residue is tested by constant nonzero polynomials. No characteristic or
perfectness assumption is made, and the residue field is not assumed algebraically
closed. The unrestricted conclusion does not require t ∈ O. For the trivial
valuation on constants, residual transcendence degree one forces the trivial
extension valuation; the closed-centre antecedent fails and no nonzero element of
the zero maximal ideal is demanded. The zero ring and empty fields are excluded
by Field, as in the source. There is no indexing-set or n = 0 restriction.

Independent rg searches in Mathlib, WeilConjectures, and the group's Sheaf tree
found the canonical restriction/residue helpers above, and no existing normalized
linear-coordinate theorem. The worker's semantic and type-search results were
read; fixed X-adic/infinity valuations do not state this theorem. The ordinary
derived route pivot is irrelevant to this field-theoretic statement: no dropped
dependency, pro-etale replacement, or discarded enhancement machinery occurs.

Compiler evidence is recorded in the maintainer review.md. The supplied fixes are
complete replacement module, lean record, and report files for merge_delivery.py
--stage 2 --apply-fixes. No source clone or delivery branch was edited.


## Maintainer compiler reproduction

Both per-file scompile.py invocations returned exit 0 with no diagnostics.
The immutable snapshot succeeded in both sandbox and library-path checks
(reported elapsed 357.0 s and 49.8 s, including wrapper/slot activity).
The replacement succeeded after the required side overlays were compiled,
then sandbox and library-path checks (21.2 s and 9.6 s). The replacement uses
independent universes and the canonical imported residue maps. No timeout limit
was raised and no global build was run. Detailed commands and evidence are in
review.md.
