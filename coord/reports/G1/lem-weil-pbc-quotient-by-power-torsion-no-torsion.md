## Worker report

The module `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion` states
`Ideal.eq_zero_of_annihilated_quotient_primaryComponent`, with its proof left as `sorry`.
No definition, additional node, dependency module, or statement correction is needed.

Source read: [Stacks Project, Tag 05EB](https://stacks.math.columbia.edu/tag/05EB),
Lemma `lemma-divide-by-torsion`, part (1), and its first proof paragraph. The local
`literature/stacks-project/more-algebra.tex` is absent on this machine, so the source
was read on the official Stacks website. Its hypotheses and conclusion agree with the
node. The declaration docstring contains all four expanded proof steps of the node.

Hypothesis and clause matching:

- A commutative ring R: `{R : Type u} [CommRing R]`.
- An R-module M, with no finite generation assumption: `{M : Type v}`,
  `[AddCommGroup M] [Module R M]`. Both universes are explicitly declared, independently.
- An ideal I of R: `(I : Ideal R)`.
- I is finitely generated: `(hI : I.FG)` (Mathlib's submodule finite-generation predicate).
- The submodule M[I^∞]: `Ideal.primaryComponent M I`, already defined by Mathlib as
  the supremum of `Submodule.torsionBySet R M ↑(I ^ n)` over natural n.
  `Ideal.primaryComponent_mem` identifies membership with being annihilated by one
  such ideal power. `torsionBySet` means killed by every scalar in the set, rather
  than by just one scalar. At n = 0 the ideal is the unit ideal, so only zero is
  annihilated; zero is also annihilated by I^1. Thus allowing n = 0 instead of n ≥ 1
  changes nothing. The existing definition includes the submodule structure in full.
- M' is the quotient M/M[I^∞]: `M ⧸ primaryComponent M I`, Mathlib's module quotient.
- An arbitrary quotient class: `(x : M ⧸ primaryComponent M I)`.
- Every a in I annihilates that class: `(hx : ∀ a : R, a ∈ I → a • x = 0)`.
- The class is zero, equivalently M'[I] = 0: conclusion `x = 0` for every such x.

There are no statement dependencies in the node. The module imports
`Mathlib.Algebra.Module.Torsion.PrimaryComponent`, using its `Ideal.primaryComponent`.
Its source was read at lines 33–61, including the full definition and membership
signature. `Submodule.torsionBySet` and `mem_torsionBySet_iff` were read in
`Mathlib.Algebra.Module.Torsion.Basic` at lines 170–184 and 269. This import also
provides the standard ideal finite-generation predicate and quotient module.

Edge cases checked before writing: I = 0 has M[I^∞] = M, so the quotient is zero,
including an empty generating family. I = R has M[I^∞] = 0, and the annihilation
hypothesis includes 1, forcing x = 0. The zero module and zero ring give zero
quotients. No domain, nonzero ideal, Noetherian ring, or characteristic assumption
is imposed. The exponent-zero convention was checked as above. Nothing is disputed.

Searches actually run:

- `msearch.py leansearch`: "quotient module by ideal power torsion has no ideal torsion
  when ideal is finitely generated". Service unavailable: Internal Server Error;
  recorded as unavailable, not as absence of a match.
- `msearch.py leanfinder`: "quotient of module by Ideal.primaryComponent has zero
  torsionBySet for a finitely generated ideal". Eight hits: notably
  `Module.isTorsionBySet_quotient_ideal_smul` (the different quotient M/IM, entirely
  I-torsion), `Submodule.QuotientTorsion.torsion_eq_bot` (torsion with respect to all
  non-zero-divisors), and `Module.isTorsionBySet_quotient_iff` (a criterion for the
  entire quotient to be torsion). None states this lemma.
- `msearch.py loogle`: "Ideal.primaryComponent". Twelve hits include the definition,
  its membership, functoriality, coprime torsion, and Dedekind decomposition results;
  no quotient-by-primary-component torsion vanishing statement.
- `msearch.py grep`: "primaryComponent|torsionBySet.*quotient", in
  `Algebra/Module/Torsion`. Ten hits give the definition and membership theorem and
  unrelated quotient-torsion criteria, with no statement match.
- `rg` of `WeilConjectures` for `primaryComponent|torsionBySet|quotient.*torsion|PowerTorsion`
  and for the item id found no match. The source's
  `WeilConjectures.Mathlib.Algebra.Module.Torsion` was then read at lines 125–167:
  `Submodule.powTorsion_quotient_eq_bot` handles powers of a single element,
  not all powers of an arbitrary finitely generated ideal. It cannot replace this
  node without a nontrivial argument or a restriction of the ideal.
- `rg` of `lean/Sheaf` for the same notions found only unrelated sheaf torsion
  quotient statements, no module ideal-power torsion assertion.
- `rg` of `dag/lean_names_upstream.json`, Mathlib and the project/source Lean for
  the item id and proposed declaration name found no recorded match or name collision.

Validation: the statement module is compiled on the server with `scompile.py`;
only its theorem uses `sorry`, as required for stage 2. The required `deliver2.py
--no-push` dry run is performed after compilation; delivery and second reading
remain the second reader's responsibility.

## Second reading by G1

The node was read against Stacks Project, More on Algebra, Lemma 05EB
(15.90.4), part (1). Its objects and clauses render in Lean as follows:

- A commutative ring (R) is `{R : Type u} [CommRing R]`.
- An (R)-module (M), with no finite-generation hypothesis, is
  `{M : Type v} [AddCommGroup M] [Module R M]`.
- The ideal (I) and finite-generation hypothesis are `(I : Ideal R)` and
  `(hI : I.FG)`.
- The source's (M[I^\infty]) is Mathlib's `primaryComponent M I`, the
  submodule formed from all `torsionBySet` submodules for powers of `I`.
  Mathlib permits exponent zero; this adds only zero, already included at
  exponent one, so it is extensionally the source submodule.
- The quotient (M') and its arbitrary class are rendered by
  `x : M ⧸ primaryComponent M I`.
- “(a\bar x=0) for every (a\in I)” is exactly
  `hx : ∀ a : R, a ∈ I → a • x = 0`.
- The conclusion “(ar x=0)” is `x = 0`, giving the stated vanishing of
  the (I)-torsion in the quotient.

The quantifier order and all hypotheses agree. There is no stronger ring,
Noetherian, domain, characteristic, or module-finiteness assumption, and both
universe variables remain explicit. The source proof is reflected in the
statement docstring: lift to (M), use finite generators and individual
annihilating powers, take the common exponent by the monomial argument, and
return to the quotient.

Edge cases were checked: for (I=0), `primaryComponent M I = ⊤` and the
quotient is zero; for (I=R), the hypothesis includes (1) and forces the
class to vanish; zero modules and the zero ring are covered; an empty finite
generating family is the (I=0) case; and the exponent-zero convention in
`primaryComponent` is harmless. No universe or characteristic case is
excluded.

Searches were independently checked with `msearch.py` LeanSearch (service
unavailable), LeanFinder, Loogle, grep in Mathlib, grep in `WeilConjectures`,
and `rg` in `lean/Sheaf`; all found only the definition or unrelated quotient
torsion results. The upstream `WeilConjectures.Mathlib.Algebra.Module.Torsion`
lemma concerns powers of one element and does not state this finitely generated
ideal result. No existing declaration or duplicate DAG node matches.

No mismatch was found. The module already uses the canonical
`Ideal.primaryComponent`, has no hollow definitions or extra dependencies, and
the only `sorry` is the required theorem proof. Compilation with `scompile.py`
is clean.
