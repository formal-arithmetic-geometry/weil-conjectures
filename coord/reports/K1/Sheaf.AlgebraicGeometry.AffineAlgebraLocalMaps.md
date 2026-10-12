## What changed

Completed `AlgebraicGeometry.affine_algebra_local_maps` in
`lean/Sheaf/AlgebraicGeometry/AffineAlgebraLocalMaps.lean`, without changing its statement
or imports. A proved private helper `inclusion_appTop` identifies the global-section
map of an open inclusion after the canonical top-section transports.

For each affine base open U, the proof constructs q_U into g inverse image U using
`Scheme.toSpecΓ`, `Spec.map`, and `IsAffineOpen.isoSpec.inv`. It calculates q_U.appTop
and uses `ext_of_isAffine` and the Under-morphism equation to prove that q_U is over U.
Naturality of the algebra morphism proves compatibility under affine-open inclusions.
For arbitrary U,V, `Scheme.hom_ext_of_forall` compares the two maps on neighborhoods
pulled back from affine W contained in U intersection V. Finally, composition of appLE
maps proves the required section formula. No affineness of X or of U intersection V
is introduced. Empty schemes and inverse images are handled by the same construction
and the vacuous local-uniqueness criterion.

The proof follows both numbered steps of the existing node
`lem-weil-pbc-affine-algebra-local-maps`; there is no change of route or new dependency,
so no node copy is needed. The unit statement and realized steps remain untouched.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.affine_algebra_local_maps`
(node `lem-weil-pbc-affine-algebra-local-maps`). This is a complete proof, not a
decomposition. The new private theorem `inclusion_appTop` is also fully proved.
No holes remain in the delivered module; no holes or new modules were added.
Local compilation completed with no errors or warnings.

## No longer needed

None. Both original public imports are required by the unchanged statement.
All original proof dependencies remain used: affine inverse images,
`lem-weil-pbc-morphism-into-affine-scheme` through Mathlib's Gamma-Spec construction
and `ext_of_isAffine`, and `lem-weil-pbc-scheme-morphism-gluing` through
`Scheme.hom_ext_of_forall`. No modules or DAG nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The two correspondence and gluing
proof dependencies are Mathlib leaves, rather than standalone Sheaf modules; their
recorded Mathlib APIs suffice. The supplied repository has no Stacks .tex files;
the source was read from the existing local Stacks checkout, including Morphisms,
label `lemma-affine-equivalence-algebras`. Searches through leanfinder, loogle,
and grep found the affine correspondence and restriction APIs. LeanSearch returned
an internal server error, recorded as unavailable rather than an absence of results.

## Second reading by K1

1. Interface: compared the complete module against the repository with `diff` and
   checked the existing theorem signature byte for byte by script. The signature,
   docstring, definitions, notation, and both imports are unchanged. The only additions
   are the proved private helper, theorem-local elaboration options, and the proof.
   Verdict: pass; no change record is needed.
2. Proof and axioms: independently compiled the delivered file with `lcompile.py`
   (6.1 seconds, no errors or warnings). Compiled a scratch copy with `#print axioms`
   for both `AlgebraicGeometry.affine_algebra_local_maps` and `inclusion_appTop`.
   Both use exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the source: no sorry, forbidden construct, or line over 100 columns.
   The local map q is an explicit Gamma--Spec construction, not an arbitrary witness
   chosen from an unproved existence theorem. Verdict: pass.
3. Split statements: none. The private helper is an elementary transport identity,
   proved from `Scheme.homOfLE_appTop` and functoriality. Reviewed empty base,
   empty inverse images, identity inclusions, and disjoint affine opens: the same
   construction and vacuous neighborhood criterion apply. No affine intersection
   or affine source assumption is introduced. Verdict: pass.
4. Route and pruning: read the proof from construction q through hq, hqg, hqn,
   the pullback neighborhood comparison, and the appLE formula. Independently
   searched Mathlib's affine, adjunction, restriction, and gluing sources and the
   project's Lean files, and queried Loogle for `Scheme.Hom.appTop`.
   No existing relative local-family theorem or shorter replacement was found.
   Both public imports supply the unchanged statement's types and instances;
   there are no proof-only public imports. All three old proof dependencies are
   used via their recorded Mathlib APIs, so No longer needed is complete.
   Read `dag/units/sk-thm-p1.json`: its realized statement and steps remain intact.
   Verdict: pass.
5. DAG agreement: read `lem-weil-pbc-affine-algebra-local-maps` and the correspondence
   and gluing dependency nodes alongside the Lean proof. Step 1 is the explicit
   Gamma--Spec construction and over-base/section calculations; step 2 is naturality
   for inclusions followed by local uniqueness on the pullback. `proof_deps` and
   `proof_origin` accurately describe this route. Checked the cited local Stacks
   affine-algebra equivalence and Mathlib uniqueness and restriction APIs.
   No new split nodes or node-field changes are needed. Verdict: pass.

Second reading changed only this report, adding the independent review and axiom
results. No Lean repair was necessary. One original hole closed, zero holes added;
this is a complete proof, not a decomposition.
