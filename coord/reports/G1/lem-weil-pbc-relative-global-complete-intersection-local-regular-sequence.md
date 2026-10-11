## Worker report

The module `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence` states
`Algebra.isRegular_localization_of_relativeGlobalCompleteIntersection`, with a `sorry` proof.
Its source is Stacks Project, Algebra, Tag 00SV, assertion (1). I read the source definition
00SP and the entire proof of 00SV in `/home/ubuntu/c1-stacks-review/algebra.tex`, lines
36505–36516 and 36767–36832. No statement correction is needed: the source explicitly uses
“the presentation is a relative global complete intersection” for the specified equations.

Hypotheses and conclusion, clause by clause:

- A commutative ring `R`: `{R : Type w} [CommRing R]`, with `universe w` explicit.
- Nonnegative integers `n,c`: `{n c : ℕ}`. No inequality is assumed globally.
- The polynomial ring `P=R[x₁,…,xₙ]`: `MvPolynomial (Fin n) R`.
- The ordered equations `f₁,…,f_c`: `relations : Fin c → MvPolynomial (Fin n) R`.
  Zero-based `Fin` indices simply rename the one-based source indices, preserving their order.
- The quotient `S=P/(f₁,…,f_c)`: the literal type
  `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations)`.
- This specified presentation is a relative global complete intersection:
  `h : IsRelativeGlobalCompleteIntersectionPresentation relations`. Its definition says, for
  every prime `p : Ideal R`, that if `p.Fiber S` is nontrivial, then `c ≤ n` and
  `topologicalKrullDim (PrimeSpectrum (p.Fiber S)) = (n - c : ℕ)`. The inequality handles
  the negative expected dimension without truncated-natural subtraction losing information.
- A prime ideal `q` of this very quotient: `(q : Ideal S) [q.IsPrime]`.
- Its inverse image `q′` under the quotient map:
  `q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))`. Primality is inferred
  from Mathlib's comap-of-prime instance; there is no extra hypothesis on `q′`.
- Its polynomial local ring: `Localization.AtPrime` of that inverse image ideal.
- The equations `f_i/1` in this ring: `algebraMap P (Localization.AtPrime q′) (relations i)`.
- They form a regular sequence, in the specified order:
  `RingTheory.Sequence.IsRegular (Localization.AtPrime q′) (List.ofFn fun i : Fin c ↦ …)`.
  The module is the local ring itself. Mathlib's predicate includes both injectivity of each
  multiplication on the preceding partial quotient and nonzero final quotient.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`.
  I also read `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` and
  `MvPolynomial.algHom_ext` in Basic; this statement needs the polynomial carrier only.
- `def-weil-pbc-relative-global-complete-intersection`:
  `Sheaf.Paper.RelativeGlobalCompleteIntersection`, the new presentation predicate
  `Algebra.IsRelativeGlobalCompleteIntersectionPresentation`. The module also retains
  `Algebra.IsRelativeGlobalCompleteIntersection` for the existential ring-map clause.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`. I read the signatures and docstrings of `Ideal.ResidueField`
  and `Ideal.Fiber` in the recorded residue-field modules; the dependency definition uses
  `Ideal.Fiber`, following the project's canonical κ(p) ⊗[R] S convention.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular`, with its parent `IsWeaklyRegular` and the
  `isWeaklyRegular_iff_Fin` characterization inspected.

Edge cases checked: `c=0` gives the empty sequence; at a prime the localized ring is
nonzero, so the predicate's final nonzero condition is the correct one. `n=0` is the
polynomial ring with no variables. When `c>n`, the presentation condition permits only
empty fibres, hence a zero quotient, which has no prime `q`; no case is artificially
excluded by a global `c≤n` binder. The zero base ring and zero quotient similarly have
no prime of the quotient. Empty fibres impose no condition in the definition. Arbitrary
base rings, including non-Noetherian rings, are admitted; the Noetherian hypothesis
appears only inside the documented proof strategy. Repeated or zero equations are not
silently excluded: the dimension condition decides whether that presentation qualifies.

Searches performed for this item (logged by msearch.py in searches.jsonl):

- LeanSearch: “equations of a relative global complete intersection form a regular sequence
  at every prime”; service unavailable with Internal Server Error (no verdict).
- LeanFinder: “polynomial quotient with fibres of dimension n-c has regular defining equations
  in the localization at a prime”; eight hits concern smoothness and standard smooth
  presentations, none state this result or the presentation-specific definition.
- Loogle: `RingTheory.Sequence.IsRegular, MvPolynomial`; zero hits.
- Mathlib grep: `RelativeGlobalCompleteIntersection|completeIntersection|complete intersection`;
  one docstring hit in `RingTheory/Extension/Presentation/Basic.lean`, not this predicate
  or theorem.
- Direct rg of the source project's `WeilConjectures`, local `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for relative-complete-intersection identifiers and this
  item id: no source result and no equivalent theorem. The project has only the general
  ring-map definition and a localization existence theorem, which explicitly notes the
  general definition does not fix the displayed presentation. Direct name searches for
  the two new declaration names in Mathlib, the source, and `lean/Sheaf` found none.

The theorem docstring carries all six proof steps of the node: flat Noetherian local map,
regular field fibre by 00SC, lift by 00MG, descend by 00SU and base change by 00SS,
identify filtered colimits of local quotients by finite coefficients, and preserve
injectivity by exactness 00DB while checking the final quotient is nonzero.

## Dependency modules

`def-weil-pbc-relative-global-complete-intersection`: its existing recorded declaration
`Algebra.IsRelativeGlobalCompleteIntersection` expresses existence of some presentation.
Applying that predicate to the quotient of the specified equations does not imply those
very equations are regular: over a field the presentation `k[x]/(0)` has a ring which
admits a complete intersection presentation, but its equation `0` is not regular.
The source 00SP expressly distinguishes the specified-presentation condition, and the
DAG dependency includes both clauses. This delivery replaces the module of that node
with one containing `Algebra.IsRelativeGlobalCompleteIntersectionPresentation` for its
first clause, and the retained ring-map predicate for its second clause, now factored
through the presentation predicate. The latter has the same mathematical meaning and
name as before. Both definitions have full data and no `sorry`. Only the dependency
node's `lean` record changes, with a note explaining the missing presentation clause;
no new DAG node and no change to its natural-language statement is required.

Validation: server compilation and deliver2.py dry run are recorded in the worker's tool
outputs. No delivery is pushed and no second reading is claimed by this worker.

## Second reading by G1

I independently read the item node, both delivered modules, the four statement-dependency
nodes and their recorded declarations, the dependency definition's own spectrum/dimension
nodes, and Stacks Algebra 00SP and 00SV (definition and complete proof, in
`/home/ubuntu/c1-stacks-review/algebra.tex`, lines 36505–36516 and 36767–36832).
The source assumes commutative rings; Noetherianity is a temporary proof assumption only.
No mathematical mismatch was found. I left both modules and both node records unchanged.

The node's objects, hypotheses and conclusion, checked in order:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary commutative base ring R | `{R : Type w} [CommRing R]` | Exact; no domain, field, characteristic or Noetherian hypothesis. |
| Nonnegative n,c | `{n c : ℕ}` | Exact, with no global inequality added. |
| Polynomial ring P in n variables | `MvPolynomial (Fin n) R` | Exact recorded polynomial carrier; finite monomial sums. |
| Ordered equations f₁,…,f_c | `relations : Fin c → MvPolynomial (Fin n) R` | Exact; zero-based indexing preserves order. |
| Quotient S=P/(f₁,…,f_c) | `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations)` | Exact quotient, not an unrelated algebra. |
| This presentation is a relative global complete intersection | `h : IsRelativeGlobalCompleteIntersectionPresentation relations` | Exact specified-presentation condition of 00SP, not merely existence of another presentation. |
| Prime q of S | `(q : Ideal (… ⧸ Ideal.span (Set.range relations))) [q.IsPrime]` | Exact; prime instance is precisely the node hypothesis. |
| Inverse-image prime q′ in P | `q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))` | Exact quotient-map inverse image; primality is inferred, not added. |
| Local ring P_q′ | `Localization.AtPrime (q.comap (Ideal.Quotient.mk …))` | Exact recorded localization at complement of q′. |
| Images f_i/1 | `algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime …) (relations i)` | Exact localization structure map. |
| Ordered regular sequence in P_q′ | `RingTheory.Sequence.IsRegular (Localization.AtPrime …) (List.ofFn fun i : Fin c ↦ …)` | Both clauses: injective multiplication on each preceding quotient and nonzero final quotient. No permutation or existential choice of equations. |

Dependency-module second reading (H13): the existing definition node already contains
both the specified-presentation and existential ring-map clauses. Its old module only
provided the latter, which is unusable for this item's equations (the presentation
`k[x]/(0)` illustrates the distinction). The delivered presentation predicate quantifies
all primes p of R, guards by `Nontrivial (p.Fiber T)`, and requires `c ≤ n` together with
`topologicalKrullDim (PrimeSpectrum (p.Fiber T)) = (n - c : ℕ)`. This is exactly the source:
a nonempty spectrum has nonnegative dimension, so `c ≤ n` expresses the impossibility
of negative expected dimension without natural subtraction truncation. Empty fibres impose
nothing. `Ideal.Fiber` is the canonical κ(p) ⊗[R] T, isomorphic by tensor commutation to
the node's T ⊗[R] κ(p). `PrimeSpectrum` is the underlying space of the recorded `Spec`;
I read `Spec_carrier` in Mathlib's Scheme module. The dimension declaration is the recorded
supremum of strict irreducible-closed chains. The retained ring-map definition uses
`f.toAlgebra` and an R-algebra equivalence with a qualifying quotient, preserving the
old predicate's meaning and arbitrary independent universes u,v. The dependency's note
correctly explains why the old record was insufficient. No new definition node is needed.

I read Mathlib's `IsWeaklyRegular.regular_mod_prev`, `IsRegular.top_ne_smul`,
`isWeaklyRegular_iff_Fin`, `Localization.AtPrime`, `Ideal.Fiber`, `topologicalKrullDim`,
and the polynomial/quotient declarations. These are the dependency notions, not similarly
named substitutes. Both new definitions have complete data without sorry. The only theorem
has exactly a sorry proof; its docstring reproduces all six node proof steps, including
Noetherian approximation, the finite-coefficient colimit identification, exactness and
nonzero final quotient. All declaration source tags and blueprint ids are present.
All variables and universe names are bound; no hidden finiteness or size instance appears.

Edge cases: c=0 gives `List.ofFn` of the empty family, whose regularity means the local
ring is nonzero; a prime supplies exactly this. n=0 admits the constant polynomial ring
and is not excluded. For c>n the definition forces empty fibres, hence the zero quotient,
which has no prime q. Zero base rings and zero quotients therefore give vacuous prime
quantification. Empty spectra/fibres require no dimension equation. Repeated or zero
relations receive no independent exclusion. All characteristics and non-Noetherian bases
are covered. The fixed finite index types match the finite n,c in the node; w is arbitrary,
and no test object is restricted to an independent smaller universe.

Independent searches, with different wording from the worker (logged in searches.jsonl):

- LeanSearch: “constant codimension fibres of a polynomial quotient imply its relations are
  a regular sequence locally”; unavailable, Internal Server Error, no mathematical verdict.
- LeanFinder: “a polynomial presentation with constant fibre codimension has nonzerodivisor
  equations in every local ring”; eight standard-smooth/submersive-presentation results,
  whose Jacobian hypotheses are stronger; no exact predicate or statement.
- Loogle: `"IsRegular", "localization"`; six hits concern transport of already regular
  elements/sequences or regular local rings, not deduction from fibre dimension.
- Direct rg: `syntomic|00SV|00SP|complete.?intersection|fibre.*codimension|fiber.*codimension`
  across Mathlib RingTheory/MvPolynomial, the source WeilConjectures and project Sheaf.
  I opened `GlobalCompleteIntersectionLocalRegularSequence` (field-only hypothesis) and
  `EquationCountLocalizeRelativeGlobalCompleteIntersection` (existence of a localization,
  with its own explicit fibre condition); neither is this arbitrary-base theorem.
  The old ring-map definition is the only applicable general dependency, and lacks a
  specified-presentation predicate. Exact new-name searches of Mathlib, source, project
  and dag/lean_names_upstream.json found no duplicate. DAG search found the existing
  definition node that this dependency module correctly serves.

No statement correction or citer verdicts apply: the natural-language statements are
unchanged and agree with the source. Second reading changed only this report; the first
compile invocation used repository-relative paths and was immediately rerun from the
sandbox with both dependency modules together. Final compilation and delivery preflight
results are recorded below.

Validation: scompile.py compiled both modules together in dependency order, exit 0,
no warnings. deliver2.py --no-push printed OK: preflight passed and modules compiled;
nothing pushed by the dry run.
