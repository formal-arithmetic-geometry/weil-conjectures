## What changed

The statement and public imports of `Sheaf.RingTheory.NagataUniversallyJapanese` are
unchanged. Its proof now chooses a finite-variable polynomial presentation of the finite
type algebra, proves the polynomial ring Nagata by induction on the number of variables,
and applies `finite_over_nagata_is_nagata` to the surjective presentation map. A
surjective ring map is finite because its target is generated as a module by 1.
The resulting Nagata domain is N-2 by the zero-prime quotient argument.

Four new modules make the reduction explicit:

- `Sheaf.RingTheory.NagataDomainN2` proves the zero-prime argument, transporting N-2
  across the quotient-by-zero isomorphism with `isN2_of_finite_domain_extension`.
- `Sheaf.RingTheory.PolynomialNagata` proves Noetherianity and the prime-quotient
  reduction. It contracts a prime `q` to `p`, obtains the Nagata domain `R/p`, and
  proves that `R[X]/q` is generated over it by the image of `X`, by induction on
  polynomials. The canonical quotient algebra map is injective.
- `Sheaf.RingTheory.MonogenicNagataDomainN2` splits on algebraicity of the generator.
  In the transcendental case, evaluation is injective and surjective. Polynomial N-2
  and ascent along the resulting finite domain isomorphism prove the result.
- `Sheaf.RingTheory.AlgebraicMonogenicNagataDomainN2` states just the algebraic
  monogenic case, with a complete proof in words from Stacks 0334, Step 4. This is
  the only new hole. It assumes an injective map of domains, one generator and a
  nonzero polynomial relation; these are strictly more restrictive than the item.

The existing node's proof and proof dependencies now follow the implemented route.
All new declarations have nodes. Source read: the local Stacks `algebra.tex`, label
`proposition-nagata-universally-japanese`, Steps 1--4 and claim (***) at the end of
Step 4; the node's previously cited source and all its dependency signatures were read.
The unit `sk-thm-p1` and its realized statement/steps are unchanged: this is a reduction
below the unit level.

The same universe as the original item is retained throughout. The induction covers
zero variables, so finite type maps needing no generators are included. No domain
assumption is imposed on the original base or on the intermediate polynomial rings.
The polynomial prime quotient and its contracted base quotient are domains. The new
algebraic lemma permits the zero generator, a generator already in the base image,
inseparable extensions, and a nonnormal Nagata base. In its proof only the integral
closure is required to be normal.

## Proved and sorry left

Closed the item's one direct hole:
`isUniversallyJapanese_of_isNagataRing`
(node `lem-weil-pbc-nagata-universally-japanese`).

The following new declarations have complete Lean proofs:
`isN2_of_isNagataRing_domain` (node `lem-weil-pbc-nagata-domain-n2`),
`isNagataRing_polynomial` (node `lem-weil-pbc-polynomial-nagata`), and
`isN2_of_monogenic_nagata_domain` (node `lem-weil-pbc-monogenic-nagata-domain-n2`).
The two private helpers `isNagataRing_of_surjective` and
`isNagataRing_mvPolynomial` are also proved.

Added exactly one hole:
`isN2_of_algebraic_monogenic_nagata_domain`
(node `lem-weil-pbc-algebraic-monogenic-nagata-domain-n2`). Its entire public theorem
proof is `by sorry` in its own module. There are no holes in definitions or inside
any of the combining proofs. No hole remains in the item's module.

This is a decomposition, not an unconditional proof or a claimed net hole reduction:
one original hole closed and one strictly smaller hole added. Existing dependencies
`finite_over_nagata_is_nagata`, `isN2_polynomial`, and
`isN2_of_finite_domain_extension` remain assumptions through their existing named
proof holes, as intended in stage 3. The new algebraic lemma records the remaining
normalization argument instead of restating the universally Japanese conclusion.

All five modules compile together through `lcompile.py --all` in dependency order.
The delivery dry run is the final validation; no delivery is pushed by this worker.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.RingTheory.IsN1AdjoinSingleton`.
- `Sheaf.RingTheory.JapaneseDomain` (its definitions remain publicly available through
  `Sheaf.RingTheory.NagataRing`).
- `Sheaf.RingTheory.PolynomialRingN2` (used in the new monogenic proof module instead).

Kept `Sheaf.RingTheory.FiniteOverNagata`, which the proof actually uses. Added proof
imports of the polynomial-Nagata and Nagata-domain modules ; the Mathlib finite-module and polynomial-equivalence tools are already
available through retained imports.

The root no longer needs direct proof edges to the algebraic-element definition,
polynomial N-2, finite generation of algebraic field extensions, field extensions,
integral closures, finitely generated modules, module-finiteness transitivity,
normality of integral closure, normal rings, integrality transitivity, normal-Nagata
monogenic N-1, finite type Noetherianity, or Noetherian rings. The relevant edges now
belong to the new case-specific nodes, matching the implemented separation of steps.
The polynomial and normal-Nagata normalization results remain mathematically needed
in the remaining algebraic case or the completed transcendental case. They are not
claimed as globally obsolete. No existing node or entire module is claimed to be
unnecessary to the complete normalization argument; global pruning claimed: none.

The second reading also removed redundant proof imports, verified by recompilation:
`Mathlib.RingTheory.Finiteness.Basic` from the root, Nagata-domain and monogenic
modules; `Mathlib.RingTheory.Noetherian.Basic` from the Nagata-domain module;
`Mathlib.RingTheory.Ideal.Quotient.Operations` from the Nagata-domain and polynomial
modules; `Mathlib.RingTheory.Polynomial.Basic` from the monogenic and polynomial
modules; and `Mathlib.Algebra.MvPolynomial.Equiv` from the root.
These APIs remain available through the retained imports. No public import was removed.

For exact bookkeeping, the old root proof edges removed are:
`def-weil-algebraic-element`, `lem-weil-pbc-polynomial-ring-n2`,
`lem-weil-pbc-algebraic-generators-finite-extension`, `def-pc-field-extension`,
`def-weil-pbc-integral-closure`, `def-weil-finitely-generated-module`,
`lem-weil-pbc-finite-module-over-finite-algebra`,
`lem-weil-pbc-integral-closure-finite-extension-normal`, `def-weil-pbc-normal-ring`,
`lem-weil-pbc-integral-transitive`, `lem-weil-pbc-normal-nagata-monogenic-n1`,
`lem-weil-pbc-finite-type-algebra-noetherian`, and `def-weil-pbc-noetherian-ring`.
These are removals of direct root edges, not claims that their modules are globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The source's Step 4 introduces normality of the original
base although the proof only uses normality of its integral closure; the existing
node already explains this, and the new algebraic statement correctly avoids that
extra hypothesis.

The original plan's last step used a chain of arbitrary monogenic algebras. A finite
polynomial presentation followed by a surjective finite map gives a shorter Lean
implementation of that step, using the existing finite-over-Nagata theorem.
The polynomial-prime-quotient proof still implements the original quotient reduction;
the transcendental and algebraic domain cases are not bypassed.

LeanSearch returned HTTP Internal Server Error for the recorded new-node queries.
Those searches are recorded as unavailable, not as successful searches with no match.
Loogle, LeanFinder, source grep and blueprint searches were performed. None provides
Nagata/Japanese ring theory already proving the new results.

## New nodes

`lem-weil-pbc-nagata-domain-n2`, module `Sheaf.RingTheory.NagataDomainN2`:
the zero-prime specialization of the Nagata definition, with a complete Lean proof
using the existing finite-domain ascent statement.

`lem-weil-pbc-polynomial-nagata`, module `Sheaf.RingTheory.PolynomialNagata`:
the one-variable Nagata assertion, proved from Noetherianity, the existing finite-over-
Nagata result and the monogenic-domain N-2 result. Its prime quotient construction and
single-generator proof are written in Lean.

`lem-weil-pbc-monogenic-nagata-domain-n2`, module
`Sheaf.RingTheory.MonogenicNagataDomainN2`: claim (*) of Stacks 0334, proved by
splitting into algebraic and transcendental generators; the latter branch is complete
from the existing polynomial N-2 and finite-domain ascent declarations.

`lem-weil-pbc-algebraic-monogenic-nagata-domain-n2`, module
`Sheaf.RingTheory.AlgebraicMonogenicNagataDomainN2`: the remaining algebraic case,
claim (**) of Stacks 0334. Its hypothesis is a nonzero polynomial relation over the
base; clearing denominators identifies this with algebraicity over its fraction field.
The source's integral-closure and normal-Nagata monogenic N-1 argument is recorded in
its docstring and its proof steps. This is the delivery's only new sorry.

No definition or existing statement changed, so no change record is required.

## Second reading by S2

1. **Existing statements and visible data: PASS.** Compared every delivered module
   against the repository using file diffs and the declaration-signature parser.
   Only the root already exists; its theorem signature is byte-for-byte unchanged,
   and the parser reports no statement changes. Its public imports are unchanged.
   Four modules are new. No definition was introduced or changed; no change record
   is necessary. The existing node changes only `proof`, `proof_deps`, `proof_origin`.
2. **Proof and axioms: PASS, conditional on the named open statements.** Compiled
   all five modules in dependency order using `lcompile.py --all`, with no errors
   or warnings. Scratch copies with `#print axioms` checked all five public theorems
   and both private helpers; their only axioms are `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The sole literal sorry in the delivered sources is
   the entire named theorem `isN2_of_algebraic_monogenic_nagata_domain`. There is
   no axiom declaration, unsafe/opaque/extern/implemented_by, hollow definition,
   or arbitrary data witness extracted from an unproved existence theorem.
3. **Split statements: PASS.** Read the algebraic theorem, its full docstring proof,
   and its node, and independently read Stacks Tag 0334, Steps 1--4 and claim (***)
   at https://stacks.math.columbia.edu/tag/0334 (the local literature file is absent
   on this machine). Its normality and finiteness argument is valid without a
   normal base; algebraicity is not mistaken for integrality. Tested the argument
   on `x = 0`, a base-image generator, a field base, and `A = Z`, `B = Z[1/2]`
   with generator `1/2` (nonmonic relation `2X - 1`); it also covers inseparability.
   This hole is a genuine restriction to injective algebraic monogenic domain
   extensions, strictly smaller than the original finite type assertion, rather
   than a renamed root. Independent LeanFinder query used “finite normalization
   of a one-generator domain algebra satisfying a polynomial relation”; Loogle
   used integralClosure and Finite; grep searched normalization/Japanese/Nagata
   and the integral-adjoin result, plus `rg` throughout the two Lean source roots.
   Monic/integral generation results do not cover the algebraic case, and the
   upstream finite-normalization theorem assumes a field base. No existing
   declaration closes this remaining general Nagata-base case in a few minutes.
4. **Top-down route, imports, pruning and unit: PASS after cleanup.** The root's
   finite polynomial presentation, induction, finite quotient and zero-prime
   argument is a real reduction. The polynomial-prime-quotient proof constructs
   the contracted algebra and proves its generator assertion; the monogenic
   proof closes the transcendental case using existing N-2 polynomial ascent.
   All retained statement imports are public and all proof-only imports plain.
   Removed nine redundant Mathlib proof-import lines and recompiled the full set.
   `No longer needed` now lists all thirteen removed old root proof edges exactly.
   The `sk-thm-p1` realized statement and steps were read and are untouched; this
   reduction occurs strictly below their level. No global pruning is claimed.
5. **DAG agreement: PASS.** Read all five node records against the declarations
   and proof bodies. Every proof-dependency list equals the union of step uses.
   The root records the finite-variable induction and quotient route, the other
   proved nodes record their actual reductions, and the remaining hole records
   its mathematical plan and source. The polynomial Noetherian step uses a
   dependency already matched to Mathlib. New nodes have the required source,
   creation, searches, blueprint ancestry, unit/chapter and Lean records.

Second-reading changes: removed the nine redundant proof imports listed above;
updated the root theorem's obsolete six-step proof docstring to the implemented
polynomial-presentation route and corrected its Stacks proposition number to
10.162.15 (Tag 0334); made direct-edge pruning explicit in this report. No proof
term or statement was changed. The result remains a decomposition: one original
hole closed, one strictly smaller hole added, zero claimed net hole reduction.
