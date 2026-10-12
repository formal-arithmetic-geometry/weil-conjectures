## What changed

Proved `AlgebraicGeometry.jacobian_compatibility` in the sandbox module. The proof constructs the degree-zero Picard comparison from the pullback square, verifies preservation of fibrewise degree, sheafifies the comparison, transports the representing isomorphism along `Over.mapPullbackAdj`, and applies Yoneda uniqueness. Preserved the signature verbatim and locally suppressed the unused-name linter for its original instance binder, which is used through typeclass inference. Added the proof-only import `WeilConjectures.Mathlib.CategoryTheory.Yoneda` for the representing-object compatibility lemma.

## Proved and sorry left

The declaration `AlgebraicGeometry.jacobian_compatibility` is proved with no `sorry` in its body. Its axiom audit includes `sorryAx` through the existing upstream theorem `picardPresheafDegree_pic_map_of_isPullback`; this delivery closes the local proof, not its entire transitive axiom closure. No new postponed theorem is introduced.

## No longer needed

The proof does not use the separate `nonempty_picardFunctorDegree_iso_of_isPullback` theorem or its node `cor-pd-pic0-base-change`; it constructs the needed degree-zero comparison directly so that the classifying element is explicit. Removed the proof-only imports `Sheaf.AlgebraicGeometry.BaseChangeConventions` and `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`: the former supplies no declaration used here, and the latter is already publicly imported by the required AbelianVariety.Jacobian module. These modules are not claimed to leave the targets' closure. The only old proof-dependency node pruned is `cor-pd-pic0-base-change`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan described the Picard comparison abstractly. The existing library exposes enough concrete pullback, degree, and sheafification APIs to implement that comparison directly; the separate existential comparison theorem does not provide the element-level compatibility needed by the target.


## Second reading by K1

1. Compared the complete module with the repository version and checked the theorem
   signature byte for byte, including all field, curve, Jacobian, representation, and
   multiplication hypotheses and the classifying-map equality. There is no definition
   change, new declaration, changed signature, or change record. Verdict: unchanged API.
2. Compiled the delivered file locally without errors or warnings. Scanned for forbidden
   declarations and found no axiom, unsafe, opaque, extern, implemented_by, or sorry.
   A scratch copy with `#print axioms AlgebraicGeometry.jacobian_compatibility` reports
   propext, Classical.choice, Quot.sound, and sorryAx. Separate audits trace sorryAx to
   the existing `picardPresheafDegree_pic_map_of_isPullback` dependency; the Picard
   presheaf iso, sheafification iso, and Yoneda compatibility lemma have only the three
   permitted axioms. Verdict: real local proof, still conditional on upstream proofs.
3. No statement was split off and no new node was added. Read the existing Picard Defs,
   Degree, Jacobian and project Yoneda implementations. The degree comparison is for
   the cartesian square over the identity of T; properness and local finite presentation
   are supplied by the original proper/smooth hypotheses. The subtype equivalence
   works also on empty T, and imposes no positive-genus or nonidentity-extension condition.
   Verdict: no new mathematical assertion to test or duplicate.
4. Read from the target down: `hiso` identifies the two canonical pullback maps by their
   projections; `hmem` proves degree-zero membership in both directions; `eS` restricts
   the explicit natural Picard iso; `E` sheafifies it; `hbc`, `hbc'`, and `hunit` verify
   its action on the specified line-bundle class. Finally Yoneda compatibility and the
   Over adjunction give exactly the displayed projection equality. Searched the library
   for Jacobian compatibility, degree-functor isomorphisms, and representing-object
   compatibility. The existing `nonempty_picardFunctorDegree_iso_of_isPullback` proves
   only existence, with no prescribed element action, so it cannot replace this argument.
   The proof-only Yoneda import is appropriate. The two removed proof imports are now
   named above. The unit `sk-prop-ext-invariance` retains its proper-case route through
   canonical Jacobian base change; its `realized` fields are empty and unchanged.
   Verdict: route kept; pruning list now complete.
5. Compared the node JSON semantically against the repository: only proof, proof_deps,
   and proof_origin change. The pullback, fibrewise-degree, Picard sheafification, and
   Yoneda steps match the Lean constructions and the existing nodes carrying those APIs.
   The union of step uses equals proof_deps. The old dependency
   `cor-pd-pic0-base-change` is unused and recorded as pruned. Verdict: DAG agrees.

Changed only the report (complete import pruning list and transitive axiom limitation)
and the node's proof_origin (explicit Degree and Yoneda sources and declaration names).
The Lean proof was left intact. The cited blueprint markdown is absent on this machine;
read the preserved proper-case route in `dag/units/sk-prop-ext-invariance.json` and the
item's node statement, together with the full upstream declarations listed above.
