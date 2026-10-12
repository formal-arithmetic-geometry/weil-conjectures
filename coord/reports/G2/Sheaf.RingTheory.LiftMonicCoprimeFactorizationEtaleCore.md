## What changed

Proved both declarations in `Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtaleCore`
without changing either signature or visibility. Added proof-only imports of
`Mathlib.RingTheory.Polynomial.UniversalFactorizationRing` and
`Sheaf.RingTheory.EtaleSectionNeighbourhoodRefinement`.

The core proof constructs the universal coprime factorization algebra and its unique
map to A/I using Mathlib's representing equivalence. The existing section refinement
lemma supplies the etale neighbourhood and compatible maps. Quotient lifting,
surjectivity of the canonical quotient map, and injectivity of the inverse map give
the prescribed first reduction. The zero quotient case uses A itself with factors f
and 1. The second reduction follows by mapping the two product identities and
cancelling the monic first factor, with no nontriviality assumption.

Updated both node proofs and their proof dependencies to match the Lean argument.
The refinement node belongs to the same unit and packages the original idempotent
and localization steps; no unit statement or realized step is bypassed.

## Proved and sorry left

Closed 2 original holes:
- `Polynomial.exists_etale_lift_monic_coprime_factorization_core`
  (`lem-weil-pbc-lift-monic-coprime-factorization-etale-core`).
- `Polynomial.lift_monic_coprime_factorization_h_reduction`
  (`lem-weil-pbc-lift-monic-coprime-factorization-etale-h-reduction`).

No sorry remains in the item. No holes or new declarations were added. This is a
proof from existing declarations, not a decomposition into new sorry statements.
The refinement declaration and its section-splitting dependencies are already proved
in the source tree. The delivery tool checks the compiled transitive axiom footprint.

## No longer needed

None: the original module had only public imports for its statements, no proof-only
imports, and both original core nodes had empty proof_deps. The universal algebra
and refinement imports are both used. The cancellation proof needs no project
proof dependencies. The original six-step route's quotient base change, idempotent
splitting, localization, and composition remain needed within the refinement lemma;
they are packaged there rather than separately imported here. No modules can be
claimed pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The core node's sole proof step was only an instruction to decompose the six-step
argument, with empty proof_deps. It omitted the already available section refinement
interface. The updated node now records the actual construction and dependencies.
The second-factor node similarly omitted its direct monic-cancellation argument.
Both existing statements are valid, including the zero-ring and unit-ideal cases.
The binder hh0 in the second theorem is mathematically unnecessary but is retained
unchanged and referenced to keep the compiler's unused-variable linter clean.

The local literature checkout is absent on this machine; checked the source proof
on the [official Stacks Tag 0ALH page](https://stacks.math.columbia.edu/tag/0ALH).
Its universal algebra, section and idempotent localization are exactly the route
packaged by the existing refinement lemma.

Searches used the launcher msearch wrapper (LeanFinder for etale factorization,
Loogle for Monic.isRegular, and grep), plus rg of Mathlib and both library roots.
LeanFinder found the universal coprime factorization algebra rather than an exact
lifting theorem. Local signature inspection identified the existing refinement
lemma. Import-direction checking confirmed there is no cycle.

## Second reading by G2

1. **Visible declarations: pass.** Compared the delivered module with the repository
   using diff and compared both complete theorem signatures through `:= by` as
   literal strings. They are byte-identical. Visibility, universes, hypotheses,
   conclusions, existing docstrings, and public imports are unchanged. No definition,
   helper declaration, other module, or change record was added.
2. **Proof and axioms: pass.** Compiled the module with lcompile.py without errors
   or warnings. A scratch copy with `#print axioms` for both delivered declarations
   and the imported section refinement theorem compiled successfully; each reports
   exactly propext, Classical.choice, and Quot.sound, with no sorryAx. Scanned the
   module for sorry, axiom, unsafe, opaque, implemented_by, and extern: none occurs.
   B and its factors are explicit Mathlib constructions; the section map comes from
   the representing equivalence. The neighbourhood is obtained inside a theorem
   proof from an already proved existence result, not defined using a holed witness.
3. **Split statements and small cases: pass, none split off.** No new declaration
   or hole was added. Read the existing refinement and idempotent splitting
   interfaces and their proofs. The zero quotient branch takes A itself, f and 1;
   subsingleton elimination supplies the prescribed reduction. The nonzero branch
   permits either factor to have degree zero. Monic regularity proves cancellation
   even in the zero ring and does not require a bijective reduction map here.
4. **Shortest route, imports, pruning and unit: pass.** Independent LeanFinder
   search for lifting a prescribed factorization over an arbitrary quotient found
   the universal coprime factorization algebra and only more restricted standard
   etale lifting results. Searched both library roots for factorization lifting;
   the parent theorem imports this core, so using it would be circular. Inspected
   Mathlib homEquiv and its naturality lemmas: the current first-factor argument
   uses the forward-inverse identity directly. Both added imports are used only in
   proofs and correctly written plain import. Both old proof_deps lists are empty,
   so No longer needed is complete. Read sk-thm-p1.realized: these nodes are below
   its realized unit statements and steps, and none is bypassed or altered. The
   refinement implements the section, idempotent and localization route of
   [Stacks Tag 0ALH](https://stacks.math.columbia.edu/tag/0ALH).
5. **DAG agreement: pass.** Compared both JSON records to the repository: only
   proof, proof_deps and proof_origin differ. The core names exactly the Mathlib
   universal factorization node and the existing refinement node used in Lean;
   the reduction records elementary quotient-map compatibility and monic
   cancellation with no project dependency. Each step matches the actual proof,
   including the zero quotient branch. There are no new nodes to validate.

Second reading changed only this report by adding the independent review and
explicit compiler/axiom evidence. No repair to the Lean proofs or DAG was needed.
