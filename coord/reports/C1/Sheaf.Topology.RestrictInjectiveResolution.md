## What changed

Completed `AlgebraicGeometry.RingedSpace.restrict_injectiveResolution` in
`lean/Sheaf/Topology/RestrictInjectiveResolution.lean`, preserving its entire signature
and all imports. Installed the finite-limit and finite-colimit preservation supplied
by `open_restriction_adjunction_exact` as local instances, and used its exact
left-adjoint adjunction with the existing right-adjoint preservation theorem.
Constructed the resolution on the literal mapped cocomplex. Its augmentation is the
inverse of Mathlib's single-complex comparison followed by the mapped original
augmentation. Mathlib preserves the quasi-isomorphism; simplification verifies the
required degree-zero augmentation equality with the complex equality `rfl`.
Updated the node's proof and proof dependencies to match this construction.

## Proved and sorry left

Proved `AlgebraicGeometry.RingedSpace.restrict_injectiveResolution`
(node `lem-sc-ringed-space-restrict-injective-resolution`): 1 of 1 original sorries.
No sorry remains in the delivered module; no new declarations or sorries were added.
The proof depends on the existing, still-sorry
`AlgebraicGeometry.open_restriction_adjunction_exact`
(node `lem-sc-derived-open-restriction-adjunction-exact`), as intended by stage 3.
The supplied adjunction has extension by zero on the left, restriction on the right.
The resolution's positive-degree and degree-zero behavior are both covered by
preservation of the original quasi-isomorphism. There is no nonempty-open assumption;
the argument applies also to the empty open, the whole space, and the zero sheaf.
Local compilation passes without warnings.

## No longer needed

Removed `lem-sc-ringed-space-module-sheaves-enough-injectives` from the node's
**proof** dependencies: constructing the termwise restricted resolution uses no
existence theorem for resolutions. Its module
`Sheaf.Topology.RingedSpaceModuleEnoughInjectives` remains a public import because
it supplies the original statement's vocabulary transitively; this delivery keeps
the public interface unchanged and does not claim that module leaves the target
closure. No imports were removed. No other planned nodes or modules were pruned.
The other original dependencies, including the generic right-adjoint preservation
node, are all retained and used.

## Where the brief, the DAG or earlier work was wrong

The plan's third step unnecessarily invoked enough injectives on the open category.
Mathlib already supplies abelian module-sheaf categories, and an injective resolution
is assembled directly from mapped injective terms and a quasi-isomorphism. The
existing declaration docstring still describes the original enough-injectives route;
its source, statement, and signature are unchanged. The node now records the precise
route used in Lean. The unit `sk-thm-curveestimate` realizes only
`thm-sc-proper-cohomology`, so this change bypasses no unit statement or proof step.
Searches via leanfinder, loogle, and grep were run with msearch; leanfinder found the
injective-object preservation API, loogle could not resolve InjectiveResolution,
and grep found the single-complex comparison and quasi-isomorphism mapping API.
No direct ready-made mapping theorem for injective resolutions was found.

## Second reading by C1

1. **Unchanged interface: pass.** Diffed every delivered module (one) and the
   existing node against the repository. The entire module prefix through the
   theorem signature is byte-for-byte unchanged; only the former `sorry` body
   changed. No definition, declaration signature, public import, or target changed,
   and there are no change records or adapted modules.
2. **Proof and trust: pass.** Independently compiled the module with `lcompile.py`
   (4.1 seconds, no errors or warnings). A scratch copy with `#print axioms
   AlgebraicGeometry.RingedSpace.restrict_injectiveResolution` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The remaining
   `sorryAx` is permitted from existing open dependencies, principally the exact
   restriction/extension-by-zero adjunction. There is no textual `sorry`, forbidden
   axiom, unsafe declaration, opaque declaration, or foreign implementation in the
   delivered module. Checked Mathlib's resolution structure and the direction of
   the single-complex comparison: its inverse has the correct source for the
   augmentation, and the complex equality is literally reflexivity.
3. **Split statements: pass (none).** No new theorem, new node, or split-off `sorry`
   was introduced. Checked the argument for the empty open, full open, zero module,
   and degree zero: no nonemptiness assumption or positive-degree-only argument is
   used. Independently searched leanfinder for exact functors mapping injective
   resolutions, loogle for the single-complex comparison, and grep for resolution
   mapping in Mathlib and the library. Found the comparison and preservation APIs
   already used, but no direct mapping theorem replacing this construction.
4. **Route, imports, and pruning: pass.** The proof directly constructs the mapped
   resolution with Mathlib rather than requesting a new one from enough injectives.
   Both plain imports are used only in the proof and have the correct visibility.
   The two public imports supply statement vocabulary (module rings and restriction
   through the first, `InjectiveResolution` through the second). All imports are
   retained for that use. The report names the sole discarded old proof dependency,
   `lem-sc-ringed-space-module-sheaves-enough-injectives`; the three other old proof
   dependencies remain. Read `dag/units/sk-thm-curveestimate.json`: its only realized
   statement is `thm-sc-proper-cohomology` and it has no realized steps, so this
   reduction changes no unit route.
5. **DAG agreement: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ in
   the existing node. Their three steps match quasi-isomorphism preservation,
   preservation of injective terms, and explicit construction with the
   single-complex comparison. The union of step `uses` equals `proof_deps`.
   The statement, statement dependencies, Lean signature record, chapter, and unit
   remain unchanged. The additivity instance cited in Step 1 is already proved in
   `DerivedHomMayerVietoris.lean`; no new dependency is left open for it.

Second reading changed only this report, adding the independent checks above.
The Lean proof and node repair are correct as delivered by the first worker and
were not rewritten.
