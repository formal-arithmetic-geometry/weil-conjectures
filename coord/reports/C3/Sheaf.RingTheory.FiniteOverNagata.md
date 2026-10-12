## What changed

Proved `finite_over_nagata_is_nagata` in
`Sheaf.RingTheory.FiniteOverNagata`, with its statement unchanged.
A proved private helper `finite_nagata` handles a finite algebra in arbitrary universes;
the public theorem applies it to S and to every R/I.
For a prime q, Lean constructs p as its contraction, proves the scalar tower for the
canonical injective map R/p -> S/q, and transfers module finiteness to R/p.
`IsNoetherianRing.of_finite` supplies both required Noetherian assertions, and the
existing `isN2_of_finite_domain_extension` supplies the N-2 assertion.
Added the proof-only import `Sheaf.RingTheory.N2AscendsFiniteDomainExtension`.
Updated the item's node proof and dependencies to this route. No definitions or
statements changed, and no unit statement or realized unit step is bypassed.

Read Stacks algebra.tex Tags 032T and 032I, including the finite case of 032I,
from the local Stacks review copy. The argument is the source's contracted-prime
argument with its existing finite-domain N-2 lemma reused.
Searches through msearch (LeanFinder, Loogle, grep) found no Mathlib Nagata theorem;
local rg found the existing N-2 ascent declaration, whose complete signature was checked.
The helper is universe-polymorphic, so both S : Type v and R/I : Type u are covered.
The zero ring, I = top, and S with no prime ideals are covered: prime quotients alone
require domains; no Nontrivial assumption is added to either R or S.

## Proved and sorry left

Closed the one original hole: `finite_over_nagata_is_nagata`
(node `lem-weil-pbc-finite-over-nagata-nagata`).
`finite_nagata` is a proved private helper, with no sorry.
No sorry remains in the item's module and no holes were added or split off.
The proof uses the existing holed theorem `isN2_of_finite_domain_extension`
(node `lem-weil-pbc-n2-ascends-finite-domain-extension`); this delivery does not claim
its transitive axioms are already sorry-free.
The final module compiles cleanly with lcompile.

## No longer needed

Removed the redundant direct proof import `Sheaf.RingTheory.JapaneseDomain`;
it remains publicly available through `Sheaf.RingTheory.NagataRing`.
Removed trial imports of `Mathlib.RingTheory.Noetherian.Basic`,
`Mathlib.RingTheory.Ideal.Quotient.Operations`, and `Mathlib.RingTheory.Finiteness.Basic`:
all are available through the retained public statement imports.
No public import was changed.

The item's direct proof dependencies no longer separately include
`lem-weil-pbc-finite-dimensional-domain-is-field`, `def-pc-field-extension`,
`lem-weil-pbc-field-degree-multiplicativity`, `def-weil-pbc-integral-closure`,
`def-weil-pbc-japanese-domain`, `lem-weil-pbc-finite-algebra-is-integral`, or
`lem-weil-pbc-integral-transitive`. These are encapsulated by the existing N-2 ascent
node, whose proof uses them; they are not claimed to be pruned from the global closure.
No entire module is known to become unreachable from the targets.

## Where the brief, the DAG or earlier work was wrong

The original four-step plan is mathematically sound, but expands an argument already
stated by `isN2_of_finite_domain_extension`. Reusing that theorem eliminates duplicate
formalization of its fraction-field and integral-closure steps.
No incorrect statement, source error, or tool failure was found.

## Second reading by C3

1. **Visible contract: pass.** Compared the entire delivered module with the
repository using diff, and compared the existing theorem signature byte for byte.
`finite_over_nagata_is_nagata` still quantifies over arbitrary universe-u R and
universe-v S, assumes only commutative rings, an R-algebra structure, module
finiteness and `IsNagataRing R`, and concludes both `IsNagataRing S` and the
Nagata property of every ideal quotient of R. The original docstrings and both
public imports are unchanged. The only added declaration is a proved private
helper; there is no definition change or change record needed.

2. **Proof and axioms: pass, relative to the existing open dependency.** Independently
compiled the delivered file through lcompile: exit 0, no warnings. Compiled a
scratch copy with `#print axioms finite_nagata` and
`#print axioms finite_over_nagata_is_nagata`: both report exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The use of the already-open
`isN2_of_finite_domain_extension` accounts for the outstanding proof dependency;
this is not an unconditional sorry-free target proof. No sorry occurs in the
module, and there is no axiom, unsafe, opaque, implemented_by, extern, or hollow
definition. No data is selected from an unproved existence statement.

3. **Split statements and edge cases: pass.** No new holed statement or split node
is delivered. Read the complete signature of `isN2_of_finite_domain_extension`:
its domain, Noetherian, finite-module, fraction-field and injectivity hypotheses
are supplied for A = R/p and B = T/q. The private helper is a real proof of the
finite-algebra assertion, not a holed restatement. A prime q contracts to a prime
p without injectivity of R -> T; the quotient-map injectivity lemma is exactly for
p = q.comap. R and T themselves need not be domains or nontrivial. If R or T is
the zero ring, there are no prime ideals to check; I = top gives the zero quotient,
and I = bottom is also included. Universe-polymorphism covers both applications
of the helper without specializing S to the universe of R.

4. **Route and pruning: pass.** Read the local Stacks algebra.tex proofs labelled
lemma-quasi-finite-over-nagata (032T, lines 45703--45717) and
lemma-quasi-finite-over-Noetherian-japanese (032I, lines 45202--45231).
The contracted-prime argument agrees with 032T hypothesis by hypothesis; the
finite-domain assertion reused from 032I is precisely its needed N-2 step.
Checked Mathlib's `Ideal.quotientAlgebra` and
`Ideal.algebraMap_quotient_injective` in Ideal/Quotient/Operations.lean:
they construct the canonical map R/p -> T/q. The scalar tower proof establishes
agreement of its composite with R -> T/q by extensionality and rfl.
`Module.Finite.of_restrictScalars_finite` transfers the existing finite
R-module structure of T/q to R/p using that tower;
`IsNoetherianRing.of_finite` supplies Noetherianity for T and R/p.
Repeated searches with LeanFinder (quotients and module-finite algebras remaining
Nagata), Loogle (`"IsNagataRing"`), grep (universally Japanese, Nagata ring,
finite Japanese), and rg in upstream and local RingTheory found no shorter
existing Nagata theorem. No unnecessary proof imports remain: the N-2 ascent
import is used, and JapaneseDomain is publicly available through NagataRing.
All seven removed direct proof-dependency nodes appear under No longer needed;
none is claimed to disappear from the global import closure. Read
`dag/units/sk-thm-p1.json`, including its realized statement and all four realized
step lists: neither this node nor any removed dependency is a realized unit
step. This is a reduction below the unit level and preserves its route.

5. **DAG agreement: pass.** The node changes only proof, proof_deps and proof_origin.
Its first step matches the helper's Noetherian and contracted-prime glue, its
second cites the existing N-2 ascent declaration, and its third matches the two
helper applications to S and R/I. Verified proof_deps is exactly the union of
step uses. The finite-algebra-Noetherian node's Mathlib match is exactly
`IsNoetherianRing.of_finite`, used twice here. The original statement, lean
signature record, source, chapter and unit remain unchanged; no new node needs
validation.

**Changes made in this second reading:** added this independent review and repeated
search, compilation, signature, dependency and axiom checks. No Lean or node repair
was necessary. One original hole is closed, zero holes added, zero split off;
the existing imported N-2 ascent hole remains open.
