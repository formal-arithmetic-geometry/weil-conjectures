## What changed

Closed `AlgebraicGeometry.tensorPullback_flat_proper_support` in
`Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport`, preserving its signature,
visibility and existing docstrings. Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`,
`Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback`,
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`, and
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`.

Finite presentation uses the proved native pullback instance via uniqueness of
left adjoints. Relative flatness uses the existing canonical base-change theorem,
transported across the cartesian-square isomorphism. Two proved private helpers
transport relative flatness through module isomorphisms and open-immersion restriction;
the latter checks the base-ring scalar action with `comp_appLE` and
`appLE_appIso_inv`. Proper support uses the support equality, a closed subscheme
structure on the old support, and vertical pasting of pullback squares.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
The unit record has no realized statement or step for this node, and no unit route
is bypassed. No definitions, statements, other modules or public imports changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.tensorPullback_flat_proper_support`
(node `lem-pc-tensor-pullback-flat-proper-support`): 1 of 1 original holes.
Added holes: none. Remaining holes in the delivered module: none.
The private helpers `flatOver_of_iso` and `flatOver_restrict` are fully proved.

This is a complete proof from existing named dependencies, not a proof of their
remaining theory. In particular,
`AlgebraicGeometry.relativelyFlat_module_pullback`
(node `lem-pc-relatively-flat-module-pullback`) still has its pre-existing `sorry`
in its existing dependency module; this delivery does not add or change that hole.
There are no new modules and no split-off statements.

The launcher single-file compile passed without warnings. The zero module and empty
source cases require no separate assumptions: all affine-section transport and support
arguments apply uniformly. No flatness of either cartesian-square projection is used.

## No longer needed

Removed planned direct dependencies:

- `def-pc-base-change` / `Sheaf.AlgebraicGeometry.BaseChangeConventions`:
  use the supplied `IsPullback` and Mathlib's canonical pullback directly.
- `lem-pc-affine-sections-flat-over-base` / Mathlib flat-localization criterion:
  no direct localization proof is needed here; canonical relative flatness is the
  existing named dependency. This does not assert that the criterion is unnecessary
  inside that dependency.
- `lem-weil-pbc-module-support-proper-over-base` /
  `Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`:
  the closed support from `hproper` and closed-subset structure equivalence suffice;
  no annihilator, pushed-forward module, or scheme-theoretic module support is needed.

None of these planned dependency modules had been imported in the original item.
An exploratory explicit `Mathlib.AlgebraicGeometry.PullbackCarrier` import was removed
because the needed range lemma is already available through the retained imports.
No original public imports were removed. The retained direct DAG dependencies are
`def-pc-module-pullback`, `lem-pc-relatively-flat-module-pullback`,
`lem-weil-pbc-support-pullback-finite-type`, and
`lem-weil-pbc-closed-subset-proper-over-base-properties`.
Global pruning depends on whether other target branches still use these nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG's local-presentation step can use the proved native pullback instance rather
than develop presentation theory anew. Its flatness step needs a transport from the
canonical fibre product to the arbitrary cartesian square; that transport is now proved
explicitly. Its support step asks for more module-on-closed-subscheme data than needed:
topological support equality and properness of a closed subscheme structure suffice.
No mathematical error or unusable statement was found. No interface change or forced
adaptation was needed.

## Second reading by H3

1. **Interfaces: PASS.** Read the complete module and compared it with the repository
   using `diff -u`. The existing theorem signature, universe, visibility, public imports,
   and docstrings are byte for byte unchanged. Only four plain proof imports, two proved
   private helpers, and the theorem proof were added. There are no definition changes,
   adapted modules, new modules, or change records.
2. **Proof and axioms: PASS.** The required launcher single-file compilation succeeded
   without warnings (4.7 seconds). A scratch copy with `#print axioms` also compiled:
   both private helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the
   main theorem additionally uses `sorryAx` through existing open dependencies. A scan
   found no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or kernel
   checking bypass in the delivered module. The affine-section equivalence uses the
   same base-ring scalar action, and restriction identifies that action explicitly.
   The chosen adjunction/composition isomorphisms are used inside a proof only;
   no data definition chooses an arbitrary witness from an unproved existence theorem.
   The closed subset on the new source is explicitly constructed as an inverse image.
3. **Split statements: PASS (none).** No holes or split-off statements were added.
   The two private lemmas are fully proved and strictly address transport, not a
   renamed copy of the item. Their arguments allow zero modules and empty opens;
   proper base change allows empty support and needs no flatness of either projection.
   Reviewed the signatures of all three named Sheaf theorem dependencies. Independent
   searches for `IsFlatOver.*restrict|IsFlatOver.*iso|support.*pullback` via `msearch.py`
   and searches of the local source and Mathlib module directories found no applicable
   public replacement for the transport helpers. Similar private helpers elsewhere
   are not available to import.
4. **Route and pruning: PASS.** Native finite-presentation pullback is proved upstream
   and is reused. The canonical flatness result is an existing open theorem, followed
   by proved transport to the arbitrary cartesian square. The support argument uses
   support equality and properness under a pasted pullback square directly. The existing
   canonical `properSupport_tensorPullback_properties` theorem still requires transport
   of proper support to an arbitrary square, so it gives no shorter direct replacement.
   Each added proof import supplies a theorem or instance actually used. Every old
   proof dependency omitted from the new proof is listed under `No longer needed`:
   `def-pc-base-change`, `lem-pc-affine-sections-flat-over-base`, and
   `lem-weil-pbc-module-support-proper-over-base`. The unit
   `dag/units/sk-thm-picard-semicon.json` has empty realized statement and step lists;
   this local reduction bypasses no realized unit statement or step.
5. **DAG: PASS.** Compared the node with the repository. Only `proof`, `proof_deps`,
   and `proof_origin` changed. The union of the proof steps' `uses` is exactly the
   four retained proof dependencies, and the three steps describe the Lean proof.
   The node statement, its recorded Lean signature, and all other node fields remain
   unchanged. There are no new nodes to validate.

Second reading changed only this report, adding the independent checks and verdicts.
No mathematical or Lean repair was needed. Closed holes: the original
`AlgebraicGeometry.tensorPullback_flat_proper_support`; added holes: none;
remaining holes in this module: none. This closes the local hole while retaining
existing open dependency theory, as already stated above.
