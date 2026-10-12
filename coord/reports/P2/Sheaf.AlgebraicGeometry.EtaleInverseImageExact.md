## What changed

Proved `AlgebraicGeometry.Etale.upperStar_abelian_exact` in
`Sheaf.AlgebraicGeometry.EtaleInverseImageExact`, with its signature unchanged.
The source library already supplies finite-limit preservation for arbitrary scheme
morphisms with Grothendieck abelian coefficients, finite-colimit preservation through
its adjunction, and additivity. Specialize these instances to `AddCommGrpCat`.
Kernel and cokernel preservation follow by instance synthesis; short exactness
follows from `ShortComplex.ShortExact.map_of_exact`.
Removed the proof-only import `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`.
Updated the node's proof, proof dependencies and proof origin to this route.
No definitions, public imports or statements changed. The unit's statement and
realized steps are preserved: this proposition is below those steps.

## Proved and sorry left

Proved the module's sole sorry: `AlgebraicGeometry.Etale.upperStar_abelian_exact`
(node `prop-weil-pbc-inverse-image-exact`). No sorry remains or is introduced.
The single-file local compile succeeds. The delivery dry run checks the axiom
probe, server compilation and preflight.

## No longer needed

Removed import/module `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits` and
its proof dependency `lem-weil-pbc-inverse-image-preserves-colimits`: the source
adjunction already supplies the needed preservation instance.
The following separate DAG proof dependencies are no longer needed by this module:
`lem-weil-pbc-etale-base-change-finite-limits`,
`lem-weil-pbc-presheaf-pullback-left-exact`,
`def-weil-pbc-sheafification`, `def-weil-pbc-direct-image`, and
`lem-weil-pbc-sheafification-exact`.
Their mathematical content is already incorporated into the proved source-library
instances reached through the existing public import of UpperLowerStar.Defs;
those transitive source-library imports remain. No additional Sheaf modules are
imported for these nodes, and no global reachability claim is made for other users.

## Where the brief, the DAG or earlier work was wrong

The node's older searches reported that small-etale continuity and the relevant
large-category Kan-extension exactness were unavailable. The current source
library now provides both, including the instance for arbitrary morphisms in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
Thus the original multi-step argument needs no new intermediate statements.

## Second reading by P2

1. Compared the complete delivered module and node with the repository using `diff`.
   The only Lean changes are removal of the plain proof import
   `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits` and replacement of the sole
   `sorry` by the proof. The existing declaration's signature is byte-for-byte
   identical, including universes and every quantifier. No definition, statement,
   public import or docstring changed; no change record is required. Verdict: pass.
2. Independently compiled the delivered module with `lcompile.py`: clean success.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Etale.upperStar_abelian_exact`: exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned the complete module:
   no sorry, axiom, unsafe, opaque, implemented_by, extern or kernel-check bypass;
   no new definitions and no lines exceeding 100 characters. Verdict: pass.
3. There are no split-off statements, new declarations or new nodes to assess or
   search for duplicates. The theorem still treats every scheme morphism, without
   an etale hypothesis on f; zero morphisms and arbitrary short exact complexes are
   included. Read the source finite-limit instance and its general-morphism
   Grothendieck-abelian Kan-extension instance, the adjunction, and the additive
   instance. These provide precisely the needed hypotheses. Verdict: pass.
4. Searched `lean/Sheaf` and `lean/WeilConjectures` for inverse-image exactness and
   `map_of_exact`, and read the existing source route: instance synthesis already
   supplies the first three clauses and both parallel-pair clauses; Mathlib's
   short-exact mapping theorem supplies the last clause. No shorter substantive
   argument or duplicate intermediate theorem is needed. All remaining public
   imports support the signature (the functor, short complexes, and abelian-group
   coefficients); the removed import was used only by the old plan. Compared old
   and new `proof_deps`: all six removed dependencies appear under No longer needed.
   Read `dag/units/sk-thm-properbasechange.json`: its realized statement nodes are
   torsion assembly and bounded-below base change; its three steps are projective
   line, reduction/prime base change, and torsion assembly. Neither this node nor
   any of the six pruned nodes realizes those steps. The unit route is preserved.
   Verdict: pass.
5. Compared the node JSON field by field: only `proof`, `proof_deps`, and
   `proof_origin` change. Their source-instance, adjunction, parallel-pair and
   short-exact mapping route agrees with the Lean proof. The remaining dependency
   records identify `Etale.upperStar` in UpperLowerStar.Defs and the sheaf category
   with abelian-group coefficients in Mathlib, exactly as used. The node's arbitrary
   morphism and five conclusions match all five Lean conjuncts. Verdict: pass.

Changes by the second reader: appended this independent review only; no Lean or
DAG repair was needed. The scratch axiom probe is outside the delivered lean tree.
