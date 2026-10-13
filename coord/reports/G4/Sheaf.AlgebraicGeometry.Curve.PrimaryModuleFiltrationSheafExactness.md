## What changed

Proved the sole existing theorem in
`Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafExactness` without changing
its signature, visibility, docstring, or any definition. The proof constructs the
canonical equivariant quotient map, checks its kernel after forgetting to integer
modules, reflects its cokernel universal property into discrete representations,
and maps that cokernel through the supplied equivalence and inverse image.
`ShortComplex.exact_cokernel` gives short exactness of the specified sheaf complex.

Added only the proof import `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.
The forgetful functor receives a locally constructed family of FunLike instances
with the representations' stored module instances explicitly specified. All such
instance work is inside the proof; no attribute or global command is changed.
There are no changes to the imported fixed-field comparison module.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.primarySheafSequence_shortExact`
(node `lem-sc-primary-subgroup-sheaf-exactness`).

Holes added: none. Holes left in delivered modules: none. The first worker's
`AlgebraicGeometry.Scheme.primarySubgroupQuotient_exact` hole and its new node
were removed after implementing the quotient-kernel calculation directly in
`hex`. Thus this is a proof, not a decomposition.

Local compilation succeeds without errors or warnings. A scratch copy with
`#print axioms AlgebraicGeometry.Scheme.primarySheafSequence_shortExact` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The old proof dependency `lem-weil-pbc-inverse-image-composition` is not used:
Mathlib's inverse-image preservation instances suffice. Its module
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Composition` was already absent
from the repository version's imports, so no existing import was removed and
this delivery makes no additional module unreachable by deleting an import.

Removed the first worker's unnecessary added proof imports
`Mathlib.CategoryTheory.Abelian.Exact` and `Mathlib.Algebra.Category.Grp.AB`.
Removed the proposed split node
`lem-sc-primary-subgroup-sheaf-exactness-quotient-exact` and its theorem.
The final `proof_deps` is empty: every step uses definitions or Mathlib.

## Where the brief, the DAG or earlier work was wrong

The previous report described a missing dependency and a 60-second timeout.
Neither occurs in this reading: the supplied compiled fixed-field comparison
loads, and the final module compiles in about five seconds. No dependency source
needs to be delivered. The first worker left quotient exactness open even though
Mathlib's faithful exactness reflection and module exactness criterion reduce it
to a three-line kernel calculation. A competing canonical integer-module instance
is avoided by specifying the representations' stored module instances in the
local FunLike family. The first dry run conservatively rejected a scoped attribute
command; that command was eliminated completely in favor of this local instance.

The earlier node's proof steps did not name its proposed split dependency although
`proof_deps` did. The final proof and metadata now both describe the inline kernel
calculation and have no named proof dependencies.

## Second reading by G4

1. Compared the complete delivered module with the repository version. Verdict:
   the existing declaration's signature is byte for byte unchanged; its original
   docstring and all definitions are unchanged. The sole new import is private
   to the proof. No other module is delivered.
2. Compiled the final module and a scratch copy with an axiom print. Verdict:
   no errors, warnings, sorry, unsafe/opaque declarations, external implementations,
   or added axioms; the theorem uses only the three permitted standard axioms.
3. Read the proposed quotient exactness statement, testing A=B, A=0 and B=0 in
   the kernel argument, and searched with quotient-inclusion terminology using
   leanfinder, loogle and grep plus rg in the library. Verdict: it was true and
   strictly smaller, but could be proved immediately. The direct kernel calculation
   now replaces it, so no split statements or new nodes remain. Leanfinder also
   found LinearMap.exact_subtype_mkQ; adapting its domain from N to A is longer
   than the explicit one-witness proof used here.
4. Read the proof from the target downward and checked import necessity and the
   old dependency list. Verdict: the proof uses existing Mathlib machinery and
   the explicit quotient, with unnecessary added imports removed. The unit
   sk-prop-cd-affine and its realized fields are unchanged; this reduction is
   wholly below that unit and preserves its route.
5. Compared the node's proof, proof_deps and proof_origin to the Lean proof.
   Verdict: the inline faithful exactness reflection, quotient kernel calculation,
   cokernel reflection and sheaf transport now agree with the metadata. No new
   node or statement-change record is needed.

Changed during this reading: closed and inlined the quotient exactness step,
removed its theorem and node, kept instance elaboration entirely within the existing proof,
restored its original docstring, pruned two unnecessary added imports, and rewrote
this report and the node's proof metadata to describe the final proof.
