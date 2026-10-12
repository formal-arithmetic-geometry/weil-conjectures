## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalks` in
`Sheaf.AlgebraicGeometry.SheafZeroStalks` without changing its signature or visibility.
The underlying abelian-group stalk has the same carrier as the module stalk; convert
zero objects to subsingleton carriers, apply Mathlib's zero-stalk criterion to the
underlying abelian-group sheaf, and reflect the identity-equals-zero equation through
`SheafOfModules.toSheaf`, which is faithful and additive.
Added private imports `Mathlib.Topology.Sheaves.Abelian` and
`Mathlib.Algebra.Category.Grp.Zero`. Updated the existing node's proof, proof_deps,
and proof_origin to this implementation. Its unit has no realized statement or proof
step carried by this node, and no unit route is bypassed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalks`
(node `pqf-lem-sheaf-zero-stalks`). No holes remain in the delivered module;
no holes were added or split off. Single-file compilation passed without warnings.
An independent scratch-copy `#print axioms` check returned exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the private import `Sheaf.Topology.PresheafModuleStalkFunctor` and its
proof dependency `def-weil-pbc-module-stalk`: the theorem needs the ringed-space
stalk functor already used by its hypothesis, carried by
`def-pc-module-stalk-functor` / `Sheaf.Algebra.Homology.ModuleStalkFunctor`.
The presheaf-module stalk node remains a statement dependency in the original
node record, and remains needed elsewhere; no claim of global unreachability is made.
No other imports, nodes, or modules are pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly identified the fixed-category Mathlib theorem but did
not complete the forgetful step. Faithful additive forgetting reflects zero by the
identity criterion, so no additional module-sheaf conservativity theorem is needed.
The original proof dependency pointed to the presheaf stalk functor although the
statement uses the ringed-space stalk functor; the route now records the latter.
The cited blueprint source file is absent from this machine's literature checkout;
the original docstring and node contain its complete germ/separatedness argument,
and the actual proof uses existing, proved Mathlib results only.


## Second reading by A4

1. Compared the only delivered Lean module with the repository using `diff` and
   checked the existing theorem signature byte for byte: unchanged, including its
   visibility, universe, hypotheses, and conclusion. No definitions, local
   instances, options, or public imports changed. PASS.
2. Independently compiled the module using `lcompile.py`: no errors or warnings.
   Scanned for holes and prohibited declarations: none. Compiled a scratch copy
   with `#print axioms AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalks`:
   exactly `propext`, `Classical.choice`, `Quot.sound`. The stalk-carrier conversion
   is definitional; the final identity equation is reflected by Mathlib's faithful
   additive `SheafOfModules.toSheaf`. No data is chosen from an unproved theorem.
   PASS.
3. There are no split-off statements or new declarations/modules/nodes to review.
   The proof remains valid on an empty scheme (the stalk condition is vacuous and
   Mathlib's sheaf criterion still applies), for the zero sheaf, and for a
   one-point scheme. No coherence or finiteness assumption is introduced. PASS.
4. Read Mathlib's stalk criterion, the forgetful functor and its faithful/additive
   instances, and the ringed-space module-stalk construction. Searched the local
   Lean library and Mathlib using zero/stalk and faithful zero-reflection terms;
   no shorter applicable ringed-module criterion was found. This proof uses the
   existing Mathlib criterion directly and adds no holes. Both new private
   imports are needed (scratch removal checks); the two retained public imports
   supply the statement's types. The old unused proof dependency
   `def-weil-pbc-module-stalk` and its private module import are fully listed under
   No longer needed. Read `dag/units/sk-prop-av-pqf-finite.json`: its realized
   statement and step lists are empty, so this node carries no fixed unit step
   bypassed by this proof. PASS.
5. Compared the node JSON with the repository: only `proof`, `proof_deps`, and
   `proof_origin` changed. Read the dependency nodes: the retained module-sheaf
   category and the newly recorded ringed-space stalk functor match the Lean.
   The proof's three steps match the carrier conversion, Mathlib criterion, and
   faithful zero reflection; their uses have exactly the recorded union. PASS.

Second reading changed only this report: added independent verification and the
axiom result. The Lean proof, imports, and node record needed no repair.
