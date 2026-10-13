## What changed

Proved `AlgebraicGeometry.coherentFormalModules_restriction_objects` with its original
signature, docstring and public imports unchanged. The restriction functor definition
and additive instance are unchanged. Coherence restricts by the open-cover criterion;
quasi-coherence follows from the locally Noetherian coherence criterion; annihilation
restricts by `idealPowerProduct_restrict_isZero_iff`. The transition quotient condition
uses the existing proved private `restrictionQuotientIso` and
`restrictionQuotientIso_π` from `TorsionControlledFormalRestriction`, then restricts the
original transition isomorphism and its equation.

The second reading removed the remaining duplicate local image and quotient helpers.
All new imports are proof-only, with `import all` used to access the existing private
quotient comparison. The existing node's proof, proof_deps and proof_origin now record
this shorter route. No definition, public interface or other module is changed.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.coherentFormalModules_restriction_objects`
(node `lem-weil-pbc-coherent-formal-modules-restriction-objects`). Added 0 holes,
split off 0 statements. No sorry remains in this module; no new helper is declared.
This is a local proof from existing dependencies, not a claim that the entire imported
closure is sorry-free. The isomorphism used is an existing explicit construction,
not an arbitrary witness chosen from an unproved existence theorem.

## No longer needed

Removed direct import `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
and direct proof dependency `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`:
its comparison is used inside the existing quotient construction instead of re-proved
here. The module remains transitively imported, so no whole module is claimed to leave
the targets' closure. All other original proof dependencies are retained.

Removed the duplicate local `restriction_power_image` and `restriction_quotient_iso`
proofs. The previous repair had already removed `restriction_product_iso`; the added
`ModulePullbackIdealPowerProductImage` and source `IdealSheaf.Functorial` direct imports
are now also unnecessary. `IdealPowerProductRestrictionZero` is an ordinary proof
import rather than `import all`, since its private helpers are no longer used here.
The new proof-only `import all TorsionControlledFormalRestriction` supplies exactly
the quotient isomorphism and its projection equation.

## Where the brief, the DAG or earlier work was wrong

The previous repair removed only the duplicated product comparison. Independent source
search found that `TorsionControlledFormalRestriction` also already constructs the
image and quotient comparisons. Reuse removes both remaining local helpers. No
statement is false, no statement or definition was changed, and no forced adaptation
is necessary. This item is not a realized statement or step of `sk-thm-p1`, and its
unit route remains unchanged.

The compiled snapshot initially still contained the old sorry-only version of
`TorsionControlledFormalRestriction`, although its source proof had landed. Per
roles/worker.md section 2.2, the second reader waited for the existing compiled
comparison rather than duplicating it or compiling a replacement dependency.

## Second reading by G3

1. PASS: diffed the complete delivered module and compared declarations with the
   repository declaration parser. Every existing signature, visibility and docstring
   is byte for byte unchanged. The restriction functor construction and additive
   instance are unchanged. Public imports are unchanged; no change record is needed.
2. PASS: independently compiled the final file with lcompile.py without warnings or
   errors (2.8 seconds). Source contains no sorry, axiom, unsafe, opaque, implemented_by,
   extern, or hollow definition. A fresh scratch copy prints only propext,
   Classical.choice and Quot.sound for the reused quotient isomorphism and its
   projection theorem. The main theorem and restriction functor additionally inherit
   sorryAx from existing dependencies; this delivery introduces no hole. The explicit
   quotient construction determines the comparison, and the final equation is obtained
   by functoriality from the original transition equation.
3. PASS: no split-off statement, new node or new declaration remains. Read the reused
   image and quotient constructions in full. Exponent zero, empty opens, zero modules,
   and zero/unit ideals require no extra assumption. Independent source searches for
   quotient/restriction and power-image terminology found the existing private
   constructions in TorsionControlledFormalRestriction, which are now reused.
   Independent Loogle search confirmed Mathlib's cokernelImageι comparison.
4. PASS after repair: removed both remaining duplicate local helpers and their direct
   proof imports. The final proof uses the shortest existing quotient construction;
   all retained proof imports provide declarations used here. No longer needed names
   the old direct affine-section import and dependency removed, while expressly
   retaining its transitive use and making no global closure-pruning claim. The
   sk-thm-p1 realized record contains neither this node nor any bypassed unit step.
   The acyclic import check permits TorsionControlledFormalRestriction.
5. PASS: node diff changes only proof, proof_deps and proof_origin. The union of each
   step's uses equals proof_deps exactly. Its coherence, annihilation and transition
   steps follow the final Lean proof and name existing dependencies. No new-node
   requirements apply.

Second reading changed the Lean proof to reuse restrictionQuotientIso and
restrictionQuotientIso_π, removed restriction_power_image and restriction_quotient_iso,
pruned their direct proof imports, changed IdealPowerProductRestrictionZero from
import all to ordinary import, and updated the node and this report. Closed 1 original
hole, added 0 holes, split off 0. After the server published green build c24f34e0d,
the verified dependency artifacts were refreshed from that build; final compilation
and the independent axiom checks use that existing proved module.
