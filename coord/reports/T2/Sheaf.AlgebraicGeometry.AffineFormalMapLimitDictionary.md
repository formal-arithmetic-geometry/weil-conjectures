## What changed

Replaced the hole in `AlgebraicGeometry.affine_formal_map_limit_dictionary` by a
complete categorical assembly from the affine formal equivalence and two natural
comparisons. The existing signature and all public imports are unchanged.

The proved private helper `finite_presentation_module` uses coherence, the
existing affine finite-generator theorem, the tilde unit, and restriction along
`X.isoSpec.inv` to prove that every supplied presentation module P is finite.
Tensor base change then makes B finite over the completed ring.

The main proof takes Q from the inverse equivalence, lifts the conjugated formal
map through its full forward functor, and obtains the stated factorization by
naturality and cancellation. Its a and b are compositions of the section-limit
natural comparison with actual limit maps of isomorphisms. Naturality proves the
square with `lim.map (Functor.whiskerRight δ.hom evaluation)`. In particular b
uses the supplied eta; no tensor-unit normalization or unrelated linear bijection
is substituted.

Added `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineGlobalComparison`, which
states the general-affine equivalence with its quotient-system and section-limit
natural isomorphisms. It has no P, epsilon, eta, delta, factorization or elementwise
square. Those parts, including finiteness of P, are proved in the original module.
This is a reusable intermediate step rather than a renamed copy of the item.
Updated the original node's proof, proof dependencies and proof origin to match.

Both Lean modules compile locally. The original module compiled without warnings
in 45.8 seconds before its final docstring update. The delivery dry run is the
final validation. No existing definition, theorem signature, visibility or target
was changed, and no forced adaptations are needed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.affine_formal_map_limit_dictionary`
(node `lem-weil-pbc-affine-formal-map-limit-dictionary`). There are no remaining
sorries in the item's module.

Added one hole:
`AlgebraicGeometry.coherentFormalModules_affine_global_comparison`
(node `lem-weil-pbc-affine-global-formal-comparison`), in the new module of that name.
Its proof is exactly `by sorry`; its docstring and node explain the affine-chart
transport, quotient-system comparison and natural section-limit cones. All other
new proof code is complete. This is a decomposition (one hole closed, one added),
not a net reduction of holes or an assertion of an axiom-free completed theorem.

Checked the edge cases mathematically: for I=0 the systems are constant; for I=A
the completed ring and formal systems are zero. Empty affine schemes and zero
modules obey the same comparisons. Neither the intermediate statement nor the
assembly requires a proper ideal or a nonzero ring. There is no definition
choosing data from the existential theorem; its witnesses are used only locally
in the proof of a proposition.

## No longer needed

Removed the original direct proof imports
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` and
`Mathlib.RingTheory.AdicCompletion.AsTensorProduct` from the item's module.
The Spec equivalence remains a documented proof-plan dependency of the new
affine-comparison theorem; it is not claimed as globally pruned. The new module
has only the public imports required by its statement: no proof dependency is
imported for its still-open proof. The finite-module tensor-completion theorem
`lem-weil-pbc-completion-finite-module-tensor` is no longer a direct dependency of
the item: the assembly uses finiteness of B and the affine-comparison theorem,
with the given eta, instead of constructing an additional tensor-completion iso.
No claim is made that its Mathlib module leaves the complete targets' import closure.

The third removed old proof dependency is
`lem-weil-pbc-spec-module-tilde-sections`: it remains a statement dependency,
and `Mathlib.AlgebraicGeometry.Modules.Tilde` stays publicly imported for L.
The actual finiteness argument uses `tilde.toTildeΓNatIso` and the existing
restriction comparisons, recorded under
`lem-weil-pbc-affine-tilde-gamma-adjunction`. Thus the removed old proof-node
list is exactly `lem-weil-pbc-coherent-formal-modules-affine`,
`lem-weil-pbc-completion-finite-module-tensor`, and
`lem-weil-pbc-spec-module-tilde-sections`; none is claimed globally pruned.

Kept the four public imports required by the unchanged statement. The tilde
adjunction and coherence criterion still occur in the proved finiteness helper.
Added only the three existing proof tools it uses and the new affine-comparison
module. No node realizing a unit's statement or proof step is bypassed:
`sk-thm-p1` and its realized route are unchanged. No other nodes or modules are
claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The first dry run found that the planned module
`Sheaf.AlgebraicGeometry.AffineFormalQuotientComparison` has no compiled object in
the shared cache. Its declaration is not used by the new module's current open
proof, so removed that unused import, together with its other unused proof-plan
imports. No dependency declaration was copied or restated to work around the
cache. The node retains the named lemmas the next worker should use.

No statement error was found. The Spec-level theorem's exact interface does not
provide the general-X functor and both natural comparisons needed here. The
existing affine-open limit equivalence gives natural cones but omits the inverse
quotient-system comparison. The new intermediate theorem isolates this remaining
interface work while the formal-map assembly is fully proved.

LeanSearch returned Internal Server Error and is recorded as unavailable, not as
negative evidence. LeanFinder, Loogle, Mathlib grep and project searches found no
exact existing statement. The literature payload is not present in this clone;
read Stacks 087W, 01IB, 00MA and 05GG online and obtained the source coherent.tex
in the sandbox scratchpad. Tag 087W's actual source label is
`lemma-inverse-systems-affine`.

## New nodes

`lem-weil-pbc-affine-global-formal-comparison` states an equivalence from finite
modules over the top-ideal completion to coherent formal modules on the exact X,
together with natural comparisons to chart-pullback quotient systems and the
actual inverse limit of top sections. Its three proof steps use the existing
natural affine Spec transport, Spec formal-module equivalence and affine quotient
projection comparison. Its unit and chapter are inherited from the original item,
and its blueprint ancestry points to the same affine formal-map presentation.
No change record is required because all existing interfaces are unchanged.

## Second reading by T2

1. **Interface: pass.** Compared both delivered modules with the repository.
   The global comparison module is new. The existing theorem signature is byte
   for byte identical, and all four public imports and its visibility are
   unchanged. No existing definition is modified and no change record is needed.
2. **Proof and axioms: pass as a decomposition.** Compiled the complete delivery
   in import order with lcompile.py: the new module took 3.0 seconds and the item
   41.1 seconds, without errors or warnings. A scratch copy with #print axioms
   for both public theorems compiled in 46.7 seconds and reported only propext,
   Classical.choice, Quot.sound and sorryAx. The delivered sources have exactly
   the one reported named theorem hole, no hollow definition, and no forbidden
   axiom, unsafe, opaque, extern, implemented_by or kernel-check bypass. The
   equivalence witnesses are eliminated locally inside a proposition proof;
   no definition chooses an arbitrary witness from the open existence theorem.
3. **Split statement: pass.** Read the coherent formal conditions, the Spec
   equivalence, affine Spec transport, quotient projection comparison, and the
   source proof of lemma-inverse-systems-affine in scratchpad/coherent.tex.
   The new theorem isolates the equivalence and its two functorial comparisons;
   it contains none of P, epsilon, eta, delta or the factorization/square.
   The main proof separately establishes finiteness of P, lifts the conjugated
   morphism by fullness, and proves both equations by naturality. For I=0 the
   quotient systems are constant and finite modules are finite A-modules; for
   I=A all positive quotients vanish and the completion is the zero ring.
   Empty affine schemes and zero modules obey the same formulas. All comparisons
   are A-linear after the explicit chart/scalar transport. The docstring gives
   the construction and projection tests for naturality, with source and node.
   Independent searches used LeanFinder on finite completed modules and coherent
   quotient systems, Loogle on AdicCompletion with Module.Finite, Mathlib grep,
   and project rg on formal equivalences and section-limit comparisons. Hits
   supplied module-completion tools, the Spec equivalence, and affine-open
   limit cones, but no general-X theorem with both natural comparisons.
   FormalCompletionAffineNaturalComparison applies only to coherent completions;
   CoherentFormalModuleAffineLimitEquivalence lacks the inverse realization.
   Closing the remaining theorem requires substantial affine transport assembly,
   beyond a few-minute repair; it is explicitly left open.
4. **Route and pruning: pass after report repair.** Checked the categorical
   assembly from the top down, including that b uses the supplied eta and that
   the last equation is the actual limit map of delta. Each added plain import
   supports a used declaration; each public import is needed by the statements.
   Existing coherent-affine-sections finiteness also supplies the finiteness
   ingredient, but replacing this already proved helper would not close the
   remaining comparison hole. Read sk-thm-p1.json and its realized fields: none
   of its statement/step nodes is bypassed or changed. Completed the report's
   removed-old-proof-dependency list, distinguishing direct removal from global
   pruning. No globally pruned module is claimed.
5. **DAG: pass.** The existing node differs only in proof, proof_deps and
   proof_origin. Its steps match the finite-module helper, fullness lift and
   naturality proof. In both delivered nodes proof_deps is exactly the union
   of step uses. Checked the new node's source, self-contained statement,
   statement dependencies, three search kinds, split status, creation record,
   ancestry, inherited chapter/unit and verbatim Lean signature. The open node
   retains the existing Spec transport, Spec equivalence and affine quotient
   comparison as its planned dependencies.

Second reading changed only this report: completed the pruning list and added
these independent checks. No Lean proof or statement repair was necessary.
One original hole closed and one new hole added: decomposition, net zero holes.
