## Worker report

The module `Sheaf.RingTheory.AffinoidSupremumSeminormCalculus` states
`RestrictedSeries.affinoid_supremum_seminorm_calculus` with a single `sorry` proof.
It also constructs its two defining helpers, `affinoidResidueValues` and
`affinoidSupremum`, without postponed data or existence choices. These are helpers
for the very supremum introduced by this node, listed in `lean.declarations`.
There are no new independent notions, new nodes, dependency repairs, or changes
to the mathematical statement. Only the item's `lean` field changes.

The source was opened and read at
[Bosch's primary PDF](https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf),
Section 1.4 Definition 1 and the definition before Proposition 5, Propositions 5--8,
printed pp. 22--24 (PDF pp. 23--25). It defines affinoid algebras algebraically and
defines their supremum by maximal residue absolute values. The module follows
this algebraic definition, without assuming a normed structure on the quotient.

Hypotheses and clauses, in the order of the node:

1. Complete, nontrivially real-valued nonarchimedean field: `K : Type u`,
   `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
   The field's specified absolute value is its norm. Nontriviality of that value
   is the Mathlib nontrivially normed field condition, not just `Nontrivial K`.
2. Nonzero commutative unital K-algebra A: `[CommRing A] [Nontrivial A]
   [Algebra K A]`. The hypothesis `hA` is exactly an existential number of
   variables and a surjective ring homomorphism from Mathlib's restricted-series
   subring, with `q.comp (constants K r) = algebraMap K A`. Scalar compatibility
   says this is a K-algebra map without needing another algebra instance on the
   restricted-series subring. No finite-presentation, reducedness, norm,
   completeness or continuity hypothesis is added on A.
3. Every maximal residue field is finite: the first conjunct quantifies
   `(m : Ideal A), m.IsMaximal` and asserts `Module.Finite K (A ⧸ m)`.
   Quotient rings have Mathlib's canonical quotient K-algebra structure. For a
   maximal ideal this quotient is a field; no auxiliary field is substituted.
4. Existence and uniqueness of its extending absolute value: `∃! v :
   AbsoluteValue (A ⧸ m) ℝ, ∀ c : K, v (Ideal.Quotient.mk m
   (algebraMap K A c)) = ‖c‖`. `AbsoluteValue` includes multiplicativity,
   nonnegativity, definiteness and the triangle inequality. Uniqueness ranges
   over all extending real absolute values, as in the node.
5. Supremum over maximal ideals: `affinoidResidueValues` collects the value of
   `Ideal.Quotient.mk m a` for a maximal m and an extending absolute value.
   The first conjunct proves that each maximal ideal contributes exactly one
   absolute value; ranging over all extensions therefore gives exactly the
   displayed set in the node, without an arbitrary choice of norms.
   `affinoidSupremum` is the real `sSup` of this explicit set.
6. Finite nonnegative real number: for every a the second conjunct asserts
   `IsLUB (affinoidResidueValues ...) (affinoidSupremum ...)` and
   `0 ≤ affinoidSupremum ...`. This explicitly establishes an actual real
   supremum, rather than relying on the totalized conditional-supremum value
   of an unbounded set. An `IsLUB` in the reals also excludes the empty set.
7. All positive integral powers: `∀ n : ℕ, 1 ≤ n → ... (a ^ n) = ... a ^ n`.
   This parametrizes exactly the integers n at least one.
8. Every scalar-compatible surjective presentation: the third conjunct
   universally quantifies r, q, surjectivity and the same scalar compatibility,
   then compares the supremum of a with
   `sInf {t : ℝ | ∃ f, q f = a ∧ t = MvPowerSeries.gaussNorm ... f.val}`.
   The radius is constantly one and the coefficient absolute value is `norm`.
   Thus this is precisely the infimum over all lifts in this presentation.
9. Every homomorphism B to A between nonzero affinoids: the fourth conjunct
   quantifies `B : Type w` with its own ring, nontriviality, scalar structure,
   existential surjective presentation, and every `ψ : B →ₐ[K] A` and b.
   It asserts the required inequality with the same residue-supremum functions.
   Neither continuity nor boundedness of ψ is assumed.
10. Equality on every Tate algebra: the fifth conjunct quantifies every
    `d : ℕ` and every restricted series f and asserts that its supremum, using
    the scalar map `constants K d`, equals `MvPowerSeries.gaussNorm ... f.val`.
    The helper accepts a scalar ring map so this uses the exact existing Tate
    subring without constructing a competing Tate algebra or algebra instance.
11. Nilpotents: the last conjunct asserts `IsNilpotent a → ... a = 0`.
    No definiteness of the supremum and no reducedness hypothesis is asserted.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`;
  the stronger specified valued-field structure supplies this instance.
- `def-trf-restricted-series-presentation`: module
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, especially
  `RestrictedSeries.constants` with its full docstring and signature.
  Its recorded main declaration `RestrictedSeries.IsTopologicallyFinitelyPresented`
  and auxiliary `IsAffinoidQuotient` were also read. The latter includes a
  specified quotient norm and is not the algebraic affinoid hypothesis of the
  present node; its predicate is therefore not used to add those assumptions.
  The node's actual restricted-series subring and constants are reused verbatim.
- Mathlib `MvPowerSeries.IsRestricted.subring`, in
  `Mathlib.RingTheory.MvPowerSeries.Restricted`, and `MvPowerSeries.gaussNorm`, in
  `Mathlib.RingTheory.MvPowerSeries.GaussNorm`, both reexported by that dependency.
- Mathlib `AbsoluteValue` in `Mathlib.Algebra.Order.AbsoluteValue.Basic` and the
  canonical quotient algebra in `Mathlib.RingTheory.Ideal.Quotient.Operations`.
- The recorded proof dependency `Ideal.exists_le_maximal`, read in
  `Mathlib.RingTheory.Ideal.Maximal`, is imported privately for the later proof.
  The other three proof dependencies currently have no Lean record or Mathlib
  match, so they are named in the complete proof docstring, with no nonexistent
  module imports. They are not missing statement prerequisites.

Edge cases checked before writing and on the second pass: r = 0 and d = 0 are
allowed by `ℕ`, and the degree-zero Tate ring is the same restricted-series
subring over the empty variable type. Both zero elements and positive powers
of nilpotents are included; a nonreduced affinoid such as K⟨T⟩/(T²) is allowed,
with T having residue supremum zero. n = 1 is included; n = 0 is not required.
The zero quotient is excluded exactly by `[Nontrivial A]` (and `[Nontrivial B]`).
No residue values or lifts can be empty under the stated hypotheses: a maximal
ideal exists for a nonzero ring, its extension exists by the first conjunct,
and every a has a lift under each surjective q. Arbitrary characteristics and
independent carrier universes u, v, w remain allowed. Homomorphisms need not be
surjective or continuous. There is no `STATEMENT-DISPUTED` issue.

Searches, all made on 2026-10-24:

- `msearch.py leanfinder`: “The supremum of maximal residue field absolute
  values of an affinoid algebra is power multiplicative and contractive and
  equals the Gauss norm on Tate algebras”. Eight results, including
  `spectralAlgNorm_isPowMul`, `spectralNorm_unique`, `spectralMulAlgNorm`.
  These concern field extensions, not supremum seminorms on affinoid quotients.
- `msearch.py loogle`: `"spectralNorm", "pow"`. Four results concerning
  spectral norms on algebraic field extensions; no matching theorem.
- `msearch.py leansearch`: “Define the supremum of absolute values at maximal
  ideal residue fields of an affinoid algebra”. Eight results including
  `spectralRadius`, `NonarchAddGroupSeminorm.coe_iSup_apply`, and adic absolute
  values. None defines this maximal-residue supremum.
- `msearch.py grep`: `affinoid|supremum.*[Tt]ate|residue.*norm`: one unrelated
  L-series residue-class hit. `affinoid|residueSupremum|residueValues`: no hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `affinoid|supremumSeminorm|residue.*[Nn]orm|gaussNorm`, and for
  `Affinoid|affinoid|residueValues|residueSupremum`, found the restricted-series
  presentation and polynomial completed-local-ring comparison modules, together
  with unrelated residue/cohomology material. No existing declaration states
  the theorem or defines this supremum. The exact item-id search in
  `lean/WeilConjectures` found no declaration. The upstream-name index was
  searched too.
- DAG search `blueprint_refs.py search affinoid`: no blueprint-node matches;
  `rg` of DAG nodes for residue/supremum combinations located the present node
  and its consumers, but no independent definition of the same supremum.

Validation: `scompile.py Q20 lem-trf-affinoid-supremum-seminorm-calculus` compiled
the complete module in sandbox and library modes on the server. Final dry-run
validation is recorded below after the delivery check.

The prescribed `deliver2.py ... --no-push` returned `OK (dry run)`: the
preflight passed and the final module compiled in both sandbox and library
modes. A final local read-only comparison confirmed that `lean` is the only
changed node key and that `lean.statement` is verbatim from the final source.

## Second reading by Q20

This is the author's second pass with both the node and final module open,
not an independent-agent review: the assignment explicitly forbids starting
another agent. The maintainer supplies the independent delivery review.

I rechecked each numbered correspondence above against the actual signature.
In particular, the presentation hypothesis has only surjectivity and scalar
compatibility; the quotient is not assumed reduced, normed, or complete.
The maximal-residue clause asserts both finiteness and unique extension,
and the supremum is computed from precisely those quotients. `IsLUB` ensures
boundedness has not disappeared behind real `sSup`. The quotient estimate
ranges over every presentation, and contractivity ranges over every algebra
homomorphism from another presented nonzero algebra. The Tate equality uses
the existing restricted subring at radius one and includes d = 0. Positive
powers and nilpotents have the required ranges. No mismatch or statement
correction was found. The only addition during this pass was the private
import of the already recorded Mathlib maximal-ideal proof dependency.
