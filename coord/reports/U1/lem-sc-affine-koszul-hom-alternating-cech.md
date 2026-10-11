## Worker report

The module `Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech` states
`AlgebraicGeometry.affineKoszulHomAlternatingCech` with all hypotheses from the
node: a commutative ring `A`, a finite sequence `f : Fin r → A`, and a cochain
complex `M` of `A`-modules.  The filtered system `D` is required degreewise to
be the additive Hom complex from the landed `shiftedKoszulComplex` at the
powers `f_i^(e+1)`.  The target `T` is a cochain complex whose degree `n` is
identified with the direct sum over Čech degrees `p` of products over strictly
increasing tuples of the localized modules
`LocalizedModule.Away (∏ i, f (t i)) (M.X (n-p))`.  The comparison morphism
`Φ : colimit D ⟶ T` is asserted to be an isomorphism in every degree and as a
complex; the module docstring records the prescribed fraction map and sign
`(-1)^(pq+p(p-1)/2)`, the differential comparison, and the `r=0,1` edge cases.
The theorem proof is `sorry`, as required for stage 2.

Dependencies used:

- `Sheaf.Paper.ShiftedKoszulAugmentation`, declaration
  `AlgebraicGeometry.shiftedKoszulComplex` (the shifted negative Koszul complex
  `I^•`).
- `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`, declaration
  `CochainComplex.HomComplex` (the additive Hom-complex used for affine module
  complexes).
- `Sheaf.Algebra.Homology.HomComplex`, declaration
  `CategoryTheory.homComplex` (the recorded sheaf-valued Hom-complex dependency;
  imported for the project notion, while the affine specialization is the
  Mathlib additive Hom-complex above).
- `Sheaf.AlgebraicGeometry.AlternatingCechComputes`, declaration
  `AlgebraicGeometry.Scheme.alternatingCechComputes` (the ordered alternating
  Čech comparison).
- `Mathlib.RingTheory.Localization.Away.Basic`, declaration
  `LocalizedModule.Away` (localization of each module term).

Edge cases checked: `r = 0` gives the empty direct sums and zero comparison
complex; `r = 1` gives the single localization term and sign one; `p = 0`
uses tuples `Fin 1 → Fin r`; arbitrary integer cochain degrees are retained,
with `n-p` in the module degree; no nonemptiness or characteristic hypothesis
was added.

Searches made: `rg -n 'KoszulHom|alternatingCech|colimit.*Hom' lean/Sheaf dag/nodes`
found no existing affine Koszul Hom comparison.  The source checkout was
searched for the node id and key terms and had no matching declaration.
`msearch.py leanfinder` for “Koszul Hom colimit alternating Cech” returned no
usable exact declaration; `msearch.py loogle` for
`CochainComplex.HomComplex, LocalizedModule.Away` returned only the generic
Mathlib HomComplex and localization declarations.  Grep of Mathlib confirmed
`CochainComplex.HomComplex` is additive-group-valued, while no
module-valued affine alternating-Čech total complex exists.  The recorded
sheaf-valued `CategoryTheory.homComplex` was read in full and is not an exact
one-point affine specialization, so the Mathlib additive HomComplex is used in
the statement.

## Earlier second reading (a previous round; superseded)

I reread the node and the module together.  The ring, finite index sequence, and
cochain complex hypotheses occur in the theorem binders.  The Koszul transition
system is represented by `D`, whose every object is fixed to the Hom complex of
the shifted Koszul complex at the corresponding power.  The target binder `T`
and the isomorphisms `eIso` give the total degree, Čech degree, strictly
increasing tuple index, product of localizing elements, and the localized module
terms.  The comparison `Φ` has both degreewise `IsIso` clauses and the complex
`IsIso` clause.  No proof was added; the only proof remains `by sorry`.  The
module compiled successfully with `lcompile.py`, and the recorded signature now
matches the declaration verbatim.

## Second reading by U1

I read the node statement, its source at `perfect.tex`, Tags 08D1 and 08D2, and
all four statement dependencies. The Lean binders render `A` as a commutative
ring, `r : ℕ`, `f : Fin r → A`, and `M` as an integer cochain complex of
`A`-modules (with the Hom complex in `AddCommGrpCat`, as supplied by Mathlib).
The existential `D` and its degreewise equation render the directed Hom system;
`T`, `eIso`, and `Φ` render the target, comparison, degreewise isomorphisms, and
complex isomorphism. I corrected the target index from `ℕ` to `Fin r`: the source
has rows only for `0 ≤ p < r`; indexing all naturals gives a spurious singleton
row for every `p ≥ r` because the empty tuple subtype has one element. The
`Fin r` index also handles `r = 0` by an empty direct sum and `r = 1` by the
single localization row. The degree shift `n - (p : ℤ)` and arbitrary integer
cochain degrees remain unchanged.

The module and declaration were searched in Mathlib, the source checkout, and
`lean/Sheaf`; no existing affine Koszul/Čech comparison was found. LeanFinder
returned only generic Hom-complex declarations, Loogle returned no match, and
LeanSearch was unavailable. The recorded dependencies were opened: the shifted
Koszul complex is `AlgebraicGeometry.shiftedKoszulComplex`, the additive Hom
complex is Mathlib `CochainComplex.HomComplex`, the project sheaf Hom complex is
`CategoryTheory.homComplex` (a different notion), and localization is
`LocalizedModule.Away`. No hollow definition or proof was introduced; the sole
proof remains `by sorry`. The revised module compiles cleanly with `lcompile.py`.
