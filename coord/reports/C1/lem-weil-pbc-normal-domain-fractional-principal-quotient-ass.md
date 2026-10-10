# Stage 1 delivery: `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass`

## Worker report

The inherited worktree changes split the item into four steps and create one
unsplit child, `lem-weil-pbc-normal-domain-principal-quotient-associated-height`.
The item has no exact Lean declaration to attach. No source is wanted.

I read Stacks `literature/stacks-project/algebra.tex`, Lemma 031T,
`lemma-normal-domain-intersection-localizations-height-1`, lines 44061-44111,
and verified the tag against `tags/tags`. Clause (3) assumes a Noetherian
normal domain, its fraction field, and nonzero `y`, and concludes that
`A/(A ∩ yA)` has no embedded associated primes and that all its associated
primes have height one. The item's statement spells out "no embedded" as
minimality among primes containing the intersection ideal. The child takes
only the height-one conclusion of clause (1), under its precise hypotheses:
a Noetherian normal domain and a nonzero element `a`. Its associated-prime
notion is explicitly an annihilator of a nonzero quotient class.

The source proves clause (3) through height-one localizations, DVRs and
symbolic powers. The item's proof instead uses an agent-written reduction
to clause (1), recorded as such in `proof_origin`. In step 1, nonzero
`y=a/b` has both `a` and `b` nonzero; `c ∈ A ∩ yA` is equivalent to
`bc ∈ aA`, and `aA ⊆ A ∩ yA`. These are direct fraction and ideal
calculations. In step 2, multiplication by `b` gives an injective
`A`-linear map `A/(A ∩ yA) → A/aA`; its kernel and the equality of
annihilators follow from the same equivalence, without another lemma.
Step 3 applies exactly the new child's statement to the associated
prime of `A/aA` represented by the nonzero image, giving height one.
Step 4 uses `a ∈ A ∩ yA` to exclude `(0)` from any prime containing
the ideal. An intervening prime below the height-one associated prime
would make a chain of length two from `(0)`, so that associated prime is
minimal. These steps use the child's statement, not its proof, and the
new child is strictly weaker than the fractional-ideal item.

I checked B1-B10 for the new node. It has an empty proof and dependency
list while unsplit (B1), introduces its own ring, element and prime (B2),
cites the Noetherian, normal and Krull-dimension definition nodes and
defines the annihilator condition inline (B3, B7), and its JSON renders
single TeX backslashes (B4). Its source has both the correct 031T tag and
exact lemma label (B5). It is not claimed as a Mathlib leaf, so no leaf
declaration or line claim is made (B6, B8). The recorded LeanSearch,
LeanFinder and source-grep searches found the principal height theorem
`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` in
`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:109`, which assumes
minimality and does not prove that all associated primes are minimal;
`IsAssociatedPrime.map_of_injective` in
`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean:118` is useful for
the item's injection but is not the child's conclusion. I also searched
the current DAG by 031T, principal quotient, associated primes and height;
the other hits do not state the child's fact. Whole-blueprint searches for
`principal associated`, `fractional quotient`, `031T` and `no embedded
primes` found no matching imported node; the nearest blueprint ancestor
is `lem-weil-pbc-normal-constant-generic`, and `from`, `via` and
`same_as` record that relationship (B9).

I searched the read-only slopmaster2 `WeilConjectures/` tree for both
`(blueprint: <node id>)` tags and for fractional/principal quotients,
associated primes, normal domains and height-one assertions. No
declaration states either the item or the child exactly; hence neither
has a sorry-free attachment and there is no declaration to test against
the sorry map (B10). The item's `lean_audit.slopmaster2` is `none`.

For edge cases, `y=1/x` with nonzero nonunit `x` gives `A ∩ yA=A`, so the
associated-prime conclusions are vacuous; the proof explicitly covers
this. A unit `a` likewise makes `A/aA=0`. In `A=ℤ` with composite
`a`, associated primes of `A/aA` are the height-one prime divisors;
in `A=k[u,v]` with `a=uv`, they are `(u)` and `(v)`. These checks test
the child's height-one conclusion in small nontrivial cases. The child
asserts height one; minimality in the fractional case is
proved in the item's fourth step. The item does not alter its unit's or
chapter's route.

`review_split.py` passes with one new node. `check_dag.py --cycles`
reports zero cycles and seven pre-existing, unrelated reachability
warnings. No Lean build or source-tree write was performed.

## Review by C1

I read Algebra 031T (`lemma-normal-domain-intersection-localizations-height-1`) clauses (1) and (3) in `literature/stacks-project/algebra.tex`. The item states exactly clause (3), including that associated primes of A/(A intersect yA) are height one and minimal over the intersection ideal. The new child states only clause (1)'s height-one conclusion for A/aA under the same Noetherian normal domain and nonzero a hypotheses. Step 1 writes J={c:bc in aA} for y=a/b and checks aA subset J. Step 2's multiplication-by-b map A/J to A/aA is injective and preserves the annihilator of each nonzero class; I checked both kernel and annihilator equations. Step 3 cites precisely the child height-one statement. Step 4 uses a in J nonzero to exclude the zero prime below any prime containing J; a lower prime below a height-one associated prime would create a two-step chain. This direct reduction is correctly marked agent-written and uses no hidden proof of the child. For y=1/x with x a nonunit, J=A and the assertion is vacuous; unit a and reducible a are also consistent.

The child is self-contained, statement-only and unsplit, cites the Noetherian, normal, and height notions, and gives the exact 031T tag and label. Its LeanSearch, LeanFinder, and source grep show no exact Mathlib leaf; the principal height theorem needs minimality as an input. Searches of the DAG, whole imported blueprint, and read-only slopmaster2 found no equivalent declaration. The worker added the missing external report after my request. `review_split.py` passes and `check_dag.py` has no cycles, only seven unrelated existing reach warnings. Sections A-E of `coord/delivery-errors.md` are satisfied.
