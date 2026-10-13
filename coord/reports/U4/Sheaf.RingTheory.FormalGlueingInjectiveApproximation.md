## What changed

Proved `FormalGlueing.exists_injective_approximation` in
`Sheaf.RingTheory.FormalGlueingInjectiveApproximation`, with its statement unchanged.
The module constructs the actual compatible-section submodule `h0`, tensors its prime
projection, extends its chart projections using the existing localization theorem,
and proves both glueing compatibility equations. All added helpers are private and proved.
No definitions, instances, public imports, or other modules were changed.

The kernel and cokernel calculation uses bijectivity of the localized prime map,
which follows directly from the morphism equation and the chart linear equivalences.
Finite generation puts a power of the generated ideal inside each element's annihilator.
Torsion base change then lifts a kernel element to a compatible section; its prime
coordinate and every chart coordinate vanish, proving injectivity.

All remaining imports were already present. Updated the existing node's proof,
proof dependencies, and proof origin to describe this argument. Finite-generation
and unit-action lemmas are available through the public imports of the retained modules.

Validation: the complete single module compiles through `lcompile.py` without warnings.
The delivery dry run checks the source, signatures, imports, and axiom probe.
The source proof was read at https://stacks.math.columbia.edu/tag/05ER.
The argument includes empty chart families, zero generators, and the unit ideal;
no new hypotheses restrict these cases.

## Proved and sorry left

Closed the original hole in `FormalGlueing.exists_injective_approximation`
(node `lem-weil-pbc-formal-glueing-injective-approximation`).
Original holes: 1. Closed: 1. Added: 0. Split off: 0.
No `sorry` remains anywhere in the delivered module, including its private helpers.
The proof uses existing dependency declarations; their modules are outside this delivery.
In particular, no admitted existence result supplies an arbitrary object: H is the
explicit `h0` submodule, p is a tensor lift, and each chart map is determined uniquely
by its values on compatible sections.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.FormalGlueingCanonicalMaps`:
  `lem-weil-pbc-formal-glueing-canonical-maps` is no longer a direct proof dependency.
  The compatibility checks need only the defining equations of `compare` and `swap`,
  already proved in `FormalGlueingData`; localized prime bijectivity follows from
  the morphism equation instead of a comparison-map bijectivity theorem.
- `Mathlib.Algebra.Module.LocalizedModule.Exact`:
  `lem-weil-pbc-localization-module-exact` is no longer needed by this proof.
  Kernel vanishing uses localized injectivity; cokernel vanishing uses localized
  surjectivity and the zero composite of the quotient map with the prime map.

The other original proof dependencies remain needed. The existing Mathlib leaf
`lem-weil-pbc-fg-ideal-radical-power` replaces the monomial exponent calculation.
These are removals of direct dependencies; no claim is made that another target's
or dependency's transitive imports of these modules disappear.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's exactness and canonical-map bijectivity
steps were stronger than necessary. The proof above implements the same compatible-section
construction and injectivity argument with fewer direct dependencies.
No target signature or unit route changed, and no forced adaptations were needed.

## Second reading by U4

1. I diffed the delivered module against the repository version. The public theorem
   signature is unchanged; only its proof and private helpers changed. Verdict: pass.
2. The module compiles through `lcompile.py` with no warnings and contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The construction uses
   the explicit compatible-section submodule and proved universal-property maps.
   Verdict: pass.
3. No statements were split off and no new nodes were added. The target statement is
   unchanged and the proof covers empty chart families and zero generators. Verdict: pass.
4. The proof follows the unit route through compatible sections, localization, and
   torsion base change. The removed imports are unused, as recorded above; retained
   imports match the actual proof. Verdict: pass.
5. The DAG proof, proof dependencies, and proof origin agree with the Lean proof;
   the unit route and target statement are unchanged. Verdict: pass.

I changed only this report by recording the second reading. No Lean source or DAG
changes were needed.
