## What changed

Completed and reviewed the inherited sandbox proof of
`adjoin_singleton_atPrime_principal_quotient_conditions` without changing its signature,
visibility, public imports, or existing docstring. The theorem combines height-one associated
localizations, the prime-height inequality, and Nagata quotient/localization permanence.

Added three fully proved public helper modules:
- `Sheaf.RingTheory.AdjoinQuotientSurjective`, proving the shared
  `adjoin_quotient_surjective` for an arbitrary generating set whose generators die
  in the quotient. Both the contraction module and the target import this theorem.
- `Sheaf.RingTheory.AdjoinSingletonAssociatedContraction`, proving
  `adjoin_singleton_associated_contraction`. Adjoin induction makes the quotient map surjective;
  the reversed polynomial `C r - X f` proves that its kernel is `R ∩ xR`. Associated primes
  contract through finite-module localization and the explicit quotient isomorphism.
- `Sheaf.RingTheory.AdjoinSingletonAssociatedLocalization`, proving
  `adjoin_singleton_associated_localization`. The contracted prime has height one. Its base
  localization is a DVR, and Mathlib's `bijective_rangeRestrict_comp_of_valuationRing` identifies
  it with the monogenic prime localization. Iterated localization finishes the comparison.

Proof-only imports supply these helpers, the ring-level regular-local-ring results,
finite-over-Nagata permanence, Nagata localization, analytic unramifiedness, and quotient
localization compatibility. All maps and equivalences used as data are constructed explicitly.
There is no choice of an arbitrary object from an unproved existence theorem.

Added DAG nodes for all three public helper theorems and updated the item's proof route. Read the
source proof at https://stacks.math.columbia.edu/tag/0334 (Step 5), Tag 031T, the unit record
`dag/units/sk-thm-p1.json`, and the dependency signatures. The unit's realized nodes are unchanged.
No existing statement, definition, or interface was changed; no forced adaptations were needed.

## Proved and sorry left

Closed the sole original hole:
`adjoin_singleton_atPrime_principal_quotient_conditions`
(`lem-weil-pbc-monogenic-principal-quotient-conditions`).

Also fully proved the new shared declaration `adjoin_quotient_surjective`
(`lem-weil-pbc-adjoin-quotient-surjective`) and both comparison declarations:
`adjoin_singleton_associated_contraction`
(`lem-weil-pbc-monogenic-associated-contraction`) and
`adjoin_singleton_associated_localization`
(`lem-weil-pbc-monogenic-associated-localization`). All private helpers are proved.

No `sorry` remains in any delivered module. No holes were added or split off.
The proof still depends on the existing declaration
`Ideal.associatedPrimes_fractionalPrincipalQuotient_height`
(`lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-height`), whose proof is `sorry`;
that module is imported, not modified or re-proved here. Other existing Nagata-theory
prerequisites retain their own proof dependencies. Closing this module is not a claim that
its whole transitive closure is sorry-free.

All four sandbox modules compiled together in import order. The delivery tool performs the
final compilation, axiom probe and stage-3 preflight. Standard axioms and existing imported
`sorry` dependencies are distinguished by that probe.

Edge cases: `x = 0` is excluded explicitly; injectivity proves its image remains nonzero.
If a principal quotient is zero, its associated-prime subtype is empty and both helper
statements are vacuous. The contraction and localization helpers require no Nagata hypothesis;
Nagata is used only for analytic unramifiedness. The quotient-Nagata private helper permits an
arbitrary ideal containing the generator, and does not assume the quotient is a domain until
applying analytic unramifiedness to an associated (therefore prime) ideal.

## No longer needed

Removed both duplicate private singleton quotient-surjectivity proofs:
`quotient_map_surjective` from the contraction module and `adjoin_quotient_surjective`
from the target module. Both now use the single general theorem in
`Sheaf.RingTheory.AdjoinQuotientSurjective`. No additional prior DAG node is pruned
by this repair.

Removed proof-only imports:
- `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`: its combined theorem
  `Ideal.associatedPrimes_fractionalPrincipalQuotient` and node
  `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass` are unnecessary for this proof;
  only the existing height theorem is needed, imported in the localization helper.
- `WeilConjectures.AlgebraicGeometry.Regular`: the geometric stalk theorem is unnecessary;
  the smaller `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` supplies the ring-level
  regularity and DVR results. The tool node `lem-sc-normal-dim1-dvr` remains needed.

The minimal-prime half of the fractional-quotient argument is unnecessary here:
`Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesMinimal` and
`lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-minimal` are not needed on this
route. Minimality in the localized monogenic ring follows directly from its height-one
comparison and the nonzero generator. These are local pruning claims; another target branch
may still use the listed modules.

The leading-coefficient integrality node remains needed by the contraction helper. The
finite-over-Nagata, Nagata-localization and local-Nagata-analytic-unramifiedness nodes remain
needed. No unit statement or realized unit step was pruned.

## Where the brief, the DAG or earlier work was wrong

Repair of the maintainer return: the delivered contraction helper repeated exactly
the target module's private quotient-surjectivity statement. The duplicate was real.
Directly importing the target from the contraction module would create an import cycle.
Both callers now import the shared theorem, generalized to arbitrary generating sets,
in a separate module. The duplicate declarations and proofs have been deleted.
No existing library signature, visibility, statement, or definition changes.
The previous second reading predates this repair and has been removed for the next reader.

The inherited sandbox already had compiling Lean proofs but lacked both helper DAG nodes,
the updated proof route, and the report. Its new helper docstrings described polynomial-kernel
induction and an elementwise valuation argument, while the Lean used reversed-polynomial
integrality and the maximality of valuation local subrings. Corrected those new docstrings and
recorded the actual arguments in the DAG. The existing item's statement and docstring remain
unchanged; its updated DAG records the implemented route.

LeanSearch was unavailable (Internal Server Error); this is recorded as an unavailable search,
not evidence of absence. Loogle, LeanFinder and direct Mathlib searches found the ingredients.
Whole-blueprint searches for associated contraction and associated localization found no
matching imported blueprint nodes. The source `literature/stacks-project/algebra.tex` is absent
on this machine; the corresponding published Stacks tags were read directly.

## New nodes

`lem-weil-pbc-adjoin-quotient-surjective` records the shared elementary adjoin
quotient-surjectivity theorem in `Sheaf.RingTheory.AdjoinQuotientSurjective`.
It generalizes both former private singleton helpers, has a complete proof, and
adds no hole. Its callers' proof steps and dependencies now cite this node.

`lem-weil-pbc-monogenic-associated-contraction` records the fully proved associated-prime
contraction comparison and its quotient-kernel proof. Its module is
`Sheaf.RingTheory.AdjoinSingletonAssociatedContraction`; it adds no hole.

`lem-weil-pbc-monogenic-associated-localization` records the fully proved isomorphism with
a height-one base localization, using the existing fractional-quotient height theorem and
Mathlib's valuation-ring comparison. Its module is
`Sheaf.RingTheory.AdjoinSingletonAssociatedLocalization`; it adds no hole.

All three inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`, and record their blueprint
ancestor, source, searches, full signatures, and actual proof dependencies. No change records
are needed because no existing interface changed.

## Second reading by A3

1. **Interfaces — pass.** Compared every delivered module with the repository: the three
   helper modules are new; the only existing module is the item. Its theorem signature is
   byte-for-byte identical, including universes, all typeclass hypotheses, the nonzero and
   maximal-ideal membership hypotheses, and all three conclusion clauses. Its existing
   docstring, visibility and public imports are unchanged. The diff adds proved private
   helpers, replaces the sole `sorry`, and changes only proof imports. There are no definitions
   or interface changes and no forced adaptations. Read [Tag 0334, Step 5](https://stacks.math.columbia.edu/tag/0334),
   specifically the quotient presentation and properties (2), (3)(a), (3)(b), against the item
   and both comparison statements. They retain the source's normal-domain and fraction-field
   assumptions; only the final analytic-unramifiedness argument needs Nagata.

2. **Proofs and axioms — pass, with an existing imported hole.** Compiled all four modules
   locally in dependency order using `lcompile.py`: no errors or warnings. Searched every
   delivered Lean file for forbidden declarations and holes; none occurs. In scratch copies,
   `#print axioms` checked all four public declarations and all three private helper theorems.
   `adjoin_quotient_surjective`, `base_mem_principal_iff`,
   `adjoin_singleton_associated_contraction`, `nagata_of_equiv`, and
   `adjoin_local_quotient_nagata` use exactly `propext`, `Classical.choice`, `Quot.sound`.
   `adjoin_singleton_associated_localization` and
   `adjoin_singleton_atPrime_principal_quotient_conditions` also use `sorryAx`; the former
   calls the existing, still-open
   `Ideal.associatedPrimes_fractionalPrincipalQuotient_height`. No new hole was added.
   Equivalences are built from quotient kernels, localization lifts and proved bijectivity;
   no data is selected from an unproved mere-existence theorem. Scratch copies were removed.

3. **New statements and search — pass.** No statement is split off with `sorry`.
   The shared surjectivity theorem handles arbitrary commutative algebras: the proof lifts a
   quotient representative and uses exactly the four adjoin-induction cases. For an empty
   generator set only constants remain; for the unit ideal the quotient is zero. The
   contraction helper proves the genuinely smaller comparison: its kernel argument treats
   `r = 0` separately and uses `x ≠ 0` to reverse the polynomial and cancel `x`. Localization
   contraction uses Noetherianity of the adjoin, and restricting the annihilator then
   transporting across the explicit quotient equivalence preserves the prime. The
   localization helper contracts to a height-one base prime, constructs a local map and an
   injective map to the fraction field, applies the valuation-ring maximality theorem, and
   composes the iterated-localization equivalence. Tested the nontrivial example
   `R = Z`, `x = 2/3`: `S = Z[1/3]`, `J = (2)`, and the comparison is with `Z_(2)`.
   For `x = 1/2`, or `x = 1`, the generator is a unit, so a maximal ideal containing it
   cannot exist; zero principal quotients have no associated primes. The excluded `x = 0`
   case is essential to the height-one comparison. Independent LeanFinder search using
   contraction/annihilator and quotient-kernel wording returned the existing localized
   finite-module contraction lemma already used, but no whole comparison theorem. Loogle
   `Algebra.adjoin, Function.Surjective` returned three different maps, not this quotient
   map. A more specific query using `Ideal.Quotient` was rejected as an unknown identifier
   and is not evidence of absence. Direct searches of Mathlib, the upstream source and
   `lean/Sheaf` found no duplicate public helper or fractional monogenic comparison.

4. **Route, imports and pruning — pass.** The target really combines three separate
   arguments; it is not one application of a renamed target. Minimality follows from
   height one and the nonzero generator, so the fractional-quotient minimality module is
   unnecessary. Regularity uses the ring-level regular-local-ring results rather than the
   larger geometric module. The final quotient is finite over the base, localized, and then
   treated by the proved local-Nagata analytic-unramifiedness theorem. All added imports in
   the existing item are plain proof imports. The new helpers' public imports supply types
   or instances used in their signatures; in particular `Ideal.Quotient.Operations` supplies
   `Algebra R (S/q)`, and a scratch trial replacing it with `Quotient.Basic` failed at that
   signature, so it was retained. The two old direct proof dependencies absent from the
   new item's `proof_deps` are the combined fractional-quotient-associated-primes node
   (pruned here) and leading-coefficient integrality (still used transitively by the
   contraction helper, hence not pruned). `## No longer needed` accounts for both and for
   the removed imports. Read `dag/units/sk-thm-p1.json`: none of its realized statement or
   step nodes is bypassed or changed. Pruning is wholly below that unit route.

5. **DAG — pass after metadata repair.** Read all four delivered node files against the
   Lean. Every `proof_deps` equals the union of the proof steps' `uses`; the item changes
   only `proof`, `proof_deps`, `proof_origin`. Each new node has its source, chapter, unit,
   ancestor path, creation record, searches, full Lean statement and module, and no new
   `sorry`. The contraction node cites leading-coefficient integrality and shared quotient
   surjectivity; the localization node cites contraction, fractional-quotient height and
   the normal dimension-one DVR result. The target cites localization and the Nagata
   permanence results actually applied. Corrected the contraction node's copied
   `proof_origin`: it had mentioned valuation local-subring maximality, which belongs to
   the other helper, and now names the reversed-polynomial kernel proof, localization
   contraction and annihilator transport. Added the independent contraction search to
   that new node's search record. The localization helper's valuation map is local by
   `Localization.localRingHom`; its denominator images are nonzero by injectivity, exactly
   the hypotheses required by the Mathlib comparison.

Second reading changed only the contraction node's proof-origin/search metadata and this
report. The Lean proofs were correct and were retained. One original hole is closed, zero
holes are added, and all three new public helper statements are proved; the existing imported
height theorem remains open.
