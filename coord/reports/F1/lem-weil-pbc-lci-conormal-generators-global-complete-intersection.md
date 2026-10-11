## Worker report

The module `lean/Sheaf/RingTheory/ConormalGeneratorsGlobalCompleteIntersection.lean` states
`Algebra.conormal_generators_global_complete_intersection` for a field `k`, a natural number
`n`, an ideal `I` of `MvPolynomial (Fin n) k`, and a prime ideal `q` of the quotient.
The dimension-at-point value is represented by an existential natural `d` with
`topologicalKrullDimAt ⟨q, inferInstance⟩ = (d : WithBot ℕ∞)` and `d ≤ n`, rendering the
integer and bounds clause. The conormal module `I/I²` is Mathlib's `Ideal.Cotangent I`,
which has its natural module structure over the quotient `P ⧸ I`. Its localization at
`q` is `LocalizedModule q.primeCompl (Ideal.Cotangent I)` over `Localization.AtPrime q`.
The generation hypothesis is rendered by an existential family indexed by `Fin (n - d)`
whose `Submodule.span (R := Localization.AtPrime q)` is top. The conclusion is an element
`g` outside `q` for which `Localization.Away g` satisfies the project's
`Algebra.IsGlobalCompleteIntersection` definition.

The dependency declarations used are `Ideal.Cotangent` from
`Mathlib.RingTheory.Ideal.Cotangent`, `LocalizedModule` and `Localization.AtPrime` from
Mathlib localization modules, `topologicalKrullDimAt` from
`WeilConjectures.Mathlib.Topology.KrullDimension`, and
`Algebra.IsGlobalCompleteIntersection` from
`Sheaf.RingTheory.CompleteIntersectionOverField`. Polynomial rings and affine spectra are
represented by `MvPolynomial` and `PrimeSpectrum` as recorded by their Mathlib matches;
`Localization.Away` is the recorded Mathlib declaration.

Edge cases checked include `n = 0`, `d = 0`, `d = n`, the empty generator family
(`Fin 0`), and the zero quotient (handled by the global-complete-intersection definition).
The file compiled cleanly with `scompile.py`; the only proof is the required `sorry`.

Searches made: `msearch.py` LeanFinder/LeanSearch for conormal generators and complete
intersections (no matching theorem); Loogle for `CompleteIntersection` (no result);
grep in Mathlib for complete-intersection declarations (none, only a docstring mention);
`rg` in the project and source for the item and conormal/complete-intersection notions.
The existing project definition `Algebra.IsGlobalCompleteIntersection` and Mathlib's
`Ideal.Cotangent` were used rather than introducing duplicates.

## Earlier second reading (a previous round; superseded)

I reread every hypothesis and clause against the node and source. The field and polynomial ring are rendered by `MvPolynomial`; the quotient prime and its point are explicit. The dimension clause is the single natural `d` existential, with the required upper bound. `Ideal.Cotangent I` is exactly the Mathlib quotient `I ⧸ I²`, and the localization and finite generator family render the conormal hypothesis with `Fin (n - d)`. The conclusion quantifies `g ∉ q` and applies the existing global complete-intersection predicate to `Localization.Away g`. I checked `n = 0`, both endpoint values of `d`, an empty generator family, and the zero ring convention. No mismatch or statement correction was found.

## Second reading by F1

I read the node, its seven statement-dependency records, their actual declarations, and
Stacks algebra.tex, lines 35817–35835 (00S9) and 35909–35985 (00SC). The local literature
copy is absent on this machine; I fetched the Stacks project's algebra.tex from its
upstream GitHub repository into scratchpad/algebra-source.tex. Its labels and line
numbers agree with the node's source citation. There is no statement_change, no new
node, and no dependency module in this delivery.

Object, hypothesis, and conclusion checklist:

1. A field k: `(k : Type u) [Field k]`. Exact, arbitrary characteristic and universe;
   no algebraic closure, perfectness, or extra finiteness hypothesis.
2. An integer n ≥ 0 and P = k[x₁,…,xₙ]: `(n : ℕ)` and `MvPolynomial (Fin n) k`.
   Exact finite polynomial ring, using the dependency's Mathlib notion.
3. An arbitrary ideal I ⊆ P and S = P/I:
   `(I : Ideal (MvPolynomial (Fin n) k))` and `MvPolynomial (Fin n) k ⧸ I`.
   Exact; no primality, radicality, or regular-sequence assumption on I. The finite-type
   hypothesis in 00SC follows from this finite polynomial quotient, so need not be
   an additional binder.
4. A prime ideal q of S: `(q : Ideal (... ⧸ I)) [q.IsPrime]`. Exact. The point
   `(⟨q, inferInstance⟩ : PrimeSpectrum (... ⧸ I))` is that same prime, not its pullback.
   I read Mathlib's `AlgebraicGeometry.Spec` and its underlying locally ringed space:
   `PrimeSpectrum S` supplies precisely the underlying topological space used here.
5. d = dim_q(Spec S), with d an integer and 0 ≤ d ≤ n:
   `∃ d : ℕ, topologicalKrullDimAt ... = (d : WithBot ℕ∞) ∧ d ≤ n ∧ ...`.
   Exact: natural d expresses nonnegative integrality, and its coercion into extended
   dimension excludes infinity and bottom. I read `topologicalKrullDimAt`: it is the
   infimum over all open neighbourhoods, hence the dependency's minimum in this
   well-ordered dimension range. The existential dimension clause is unconditional;
   the generator hypothesis occurs only in the following implication. Equality fixes
   d uniquely, so this quantifier placement does not permit choosing an easier d.
6. If (I/I²)_q is generated by n-d elements over S_q:
   `∃ gens : Fin (n - d) → LocalizedModule q.primeCompl (Ideal.Cotangent I),
   Submodule.span (R := Localization.AtPrime q) (Set.range gens) = ⊤`.
   Exact. I read `Ideal.Cotangent` and its quotient-module instance: this is I modulo
   I², with its S-module structure. I read `LocalizedModule` and `Localization.AtPrime`:
   both use the complement of this same prime of S. Span is over S_q, not P or S.
   A family of the stated length allows repetitions and zero entries, exactly as
   generation by that number of elements does; it does not require a basis.
7. There exists g ∈ S outside q with S_g a global complete intersection over k:
   `∃ g : (... ⧸ I), g ∉ q ∧ IsGlobalCompleteIntersection k (Localization.Away g)`.
   Exact. `Localization.Away` inverts the powers of g. I read the project's
   `Algebra.IsGlobalCompleteIntersection`: a k-algebra presentation by c equations
   in n variables of dimension n-c, with the zero-ring convention, as in 00S9.
   The dependent algebra instances are the canonical quotient/localization structures.

Edge cases: `n = 0` is admitted (`Fin 0`), and the dimension conclusion forces d = 0.
Both d = 0 and d = n are admitted. In the latter case the generator family is empty;
its span is zero, so the hypothesis correctly asks that the localized conormal module
vanish. The zero conormal module is allowed and can be generated by any permitted
number of zero elements. A zero quotient has no prime ideal, hence no input q: this
is exactly the node's empty-spectrum case, not an excluded case added by Lean.
For an actual q and g outside q the localization is nonzero, but the reused predicate
also correctly includes the zero ring. The field may live in any universe u; finite
polynomials, quotients, and their localizations remain in u. No test-object universe
or unbound variable occurs.

Independent searches: msearch LeanSearch for an ideal whose conormal module is generated
by its codimension was unavailable (Internal Server Error), and I assign it no verdict.
Loogle `"Cotangent"` found Mathlib's existing conormal module and its instances, not
this theorem. LeanFinder for conormal generation by n minus local dimension found
smoothness/standard-smooth localization results, which impose different hypotheses.
The msearch grep `complete.intersection|conormal|codimension` in RingTheory found only
presentation documentation and the existing conormal-space implementation. Direct rg
in the project's lean/Sheaf and the upstream WeilConjectures sources found the reused
complete-intersection definition and different conormal/localization/smoothness lemmas;
none states this implication. A separate search of dag/lean_names_upstream.json and both
Lean trees found no collision for the delivered theorem name. No duplicate definition
or replacement dependency is needed.

Mismatch and repair: H8, the theorem docstring omitted the node's natural-language proof.
I added all eight steps, naming the height-difference, polynomial Noetherianity, Nakayama,
principal-open, dimension-monotonicity, localization-presentation, and complete-intersection
nodes at their uses. I also removed the unused `v` universe declaration. I did not change
the correct signature, its node record, any statement dependency, or the worker report.
The only proof remains `sorry`; there are no new definitions or hidden proof holes.
All five imports provide notions used by the signature, and lines satisfy the convention.

Validation: scompile.py compiled the repaired 69-line module on the server in 1.6 seconds,
exit code 0, with no errors or warnings. The recorded lean.statement remains verbatim
identical to the theorem signature; only its docstring and unused universe changed.
