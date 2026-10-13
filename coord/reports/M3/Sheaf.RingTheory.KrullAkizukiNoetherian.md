## What changed

Proved `krullAkizukiNoetherian` in
`lean/Sheaf/RingTheory/KrullAkizukiNoetherian.lean`, preserving its full signature and
visibility. Added proof-only imports `Mathlib.RingTheory.Ideal.GoingUp` and
`Mathlib.RingTheory.Finiteness.Ideal`. The former supplies the algebraicity and
nonzero ideal contraction argument; the latter lifts finite generation across the
quotient by the principal ideal `(x)`.

The proof follows the existing two-step route: find a nonzero scalar in each
nonzero ideal, embed D into a finite power of K, apply the existing finite-length
theorem, and lift finite generation from D/(x). Updated the node's proof and
proof_origin to describe the actual Lean argument; its proof dependency stays the
same. Updated the theorem docstring accordingly. No interface changes, new
modules, new nodes, or forced adaptations.

## Proved and sorry left

Closed the sole original hole: `krullAkizukiNoetherian`
(node `lem-sc-krull-akizuki-noetherian`). The delivered module has no `sorry`.
Added zero holes and split off zero statements.

This is a complete proof from the existing dependency, not a sorry-free proof of
the entire import closure: it uses
`Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one`
(node `lem-sc-finite-length-global-submodule`, module
`Sheaf.RingTheory.FiniteLengthGlobalSubmodule`), whose existing `sorry` is unchanged.

Validation: the module compiled through `lcompile.py` without errors or warnings.
The zero ideal is handled separately; the scalar is explicitly nonzero; the
finite-length theorem includes the unit case. No separability, integrality of D,
or integral-closedness of R is assumed. The unit record
`sk-thm-curveestimate` realizes `thm-sc-proper-cohomology` and has no proof steps
realized by this node, so this implementation preserves the unit route.

## No longer needed

None. No original imports, DAG proof dependencies, or planned modules are pruned.
`Sheaf.RingTheory.FiniteLengthGlobalSubmodule` remains essential.
The proof does not need a separate minimal-polynomial or generator-lifting node:
Mathlib proves those steps. The redundant exploratory import
`Mathlib.RingTheory.Localization.Integral` was omitted because it is publicly
imported by `Mathlib.RingTheory.Ideal.GoingUp`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The DAG's elementary first step already
has a Mathlib implementation via algebraicity and ideal contraction; it does not
need new intermediate statements. Its second step can use Mathlib's general
finite-generation lifting theorem instead of explicitly choosing and adjoining
lifted generators.

The repository's cited `literature/stacks-project/algebra.tex` is absent on this
machine; the source proof was checked at the public Stacks page for Tag 00PG
(https://stacks.math.columbia.edu/tag/00PG). The given finite-length dependency was
read together with its node. No new literature or unsupported proof is introduced.


## Second reading by M3

1. PASS: Compared the complete module and node with the repository versions.
   The sole existing declaration's signature, universes, hypotheses, conclusion,
   and visibility are byte-for-byte unchanged. No definitions, target statements,
   or additional modules changed. The node changes only proof and proof_origin.
2. PASS: Independently compiled the module with lcompile.py (2.7 seconds, no
   errors or warnings). Scanned the complete file: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definitions. A scratch copy with #print axioms
   reports exactly propext, Classical.choice, Quot.sound, and sorryAx, as expected
   from the unchanged open finite-length dependency. The basis comes from Mathlib;
   the only witnesses chosen in the ideal argument come from proved Mathlib facts,
   not from an unproved existence theorem. All lines meet the 100-character limit.
3. PASS: No split-off statements or new nodes exist. Checked the actual argument
   for the zero ideal, unit scalar, D = R, D = L, and degree-one extensions. The
   scalar is nonzero, the principal ideal lies in I, and the quotient-kernel
   intersection is precisely that principal ideal. No separability, integrality,
   or integral-closedness assumption is introduced.
4. PASS: Independently searched Mathlib with leanfinder, loogle, and grep using
   subalgebra/algebraicity/finite-generation formulations, and searched both
   library roots. No theorem closes the unrestricted intermediate-ring statement
   directly: the integral-closure results require additional hypotheses. Read
   Mathlib's ideal-contraction and finite-generation-lifting lemmas. Both added
   imports are proof-only and necessary; all original signature imports and the
   finite-length proof dependency remain needed. No old proof_deps are omitted
   from No longer needed. Read sk-thm-curveestimate.json: its realized statement
   and empty realized steps are unchanged; the route is preserved. Independently
   checked the source proof at https://stacks.math.columbia.edu/tag/00PG.
5. PASS: Read the delivered node and its finite-length dependency node alongside
   the Lean modules. The two updated proof steps accurately describe the linear
   embedding, quotient equivalences, and ideal lifting. proof_deps is still
   exactly lem-sc-finite-length-global-submodule, the sole Sheaf theorem used;
   proof_origin identifies the source and implementation. No new node fields or
   change records are needed.

Second reading changed only this report, adding the independent checks above.
The Lean proof and DAG update are accepted without repair. Closed one original
hole, added zero holes, split off zero statements, pruned no modules.
