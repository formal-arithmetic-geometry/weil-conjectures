## What changed

Proved `AlgebraicGeometry.qcqsProjectionMate_shiftedUnit_isIso` in
`Sheaf.AlgebraicGeometry.QCqsProjectionMateShiftedUnit`, with its signature and public imports
unchanged. Added proof-only imports of `Mathlib.CategoryTheory.Adjunction.Mates`,
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf`, and
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.

Two private helpers are completely proved. `equivalence_projection_mate_isIso` rotates the
supplied comparison across inverse equivalences and uses `conjugateEquiv_iso`; its component
calculation uses naturality and both inverse triangle identities.
`shifted_unit_tensorLeft_isEquivalence` uses the explicitly shifted tensor-unit homotopy
complex and the existing K-flat shift comparison to construct the tensor equivalence.
The final proof transports these equivalences along the supplied object isomorphism and
pullback's unit and shift isomorphisms, restricts the supplied tensor comparison, and applies
the categorical helper. The DAG proof and dependencies now describe this argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.qcqsProjectionMate_shiftedUnit_isIso`
(node `lem-pc-qcqs-projection-mate-shifted-unit`). No `sorry` remains in the delivered module;
no holes, modules, definitions, or public declarations were added elsewhere. Both private
helpers are proved. This is a proof from existing library declarations, not a decomposition.

## No longer needed

The planned dependency `def-pc-derived-pullback-monoidal-model` and its module
`Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel` are no longer needed by this proof.
The existing `lem-sc-derived-pullback-structure-sheaf-local` supplies the needed unit
identification directly. No original import was removed: all three public imports are used
by the unchanged statement. No additional planned proof dependencies were bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The plan's conjugation calculation needed an explicit
rotation through the inverse tensor equivalences before `conjugateEquiv_iso` applies; the
private helper proves that calculation, including equality with the supplied mate.

The upstream global derived tensor-shift instance couples its Grothendieck and derived
localization universes. Applying it directly would require a hypothesis absent from this
statement. The existing K-flat representative shift comparison works in independent
universe `w`; the proof uses the explicitly shifted unit homotopy complex. No universe,
hypothesis, or interface was changed, and no arbitrary representative was chosen from a
mere existence theorem. The unit's route is unchanged; its `realized` record does not require
this node to use the monoidal-model dependency.

## Second reading by N2

1. Compared the sole delivered module against the repository version. The existing theorem
   signature is byte-for-byte identical, as verified by a textual assertion. All three public
   imports and the public section remain unchanged. There are no definition or statement
   changes and no change records are required. Verdict: pass.
2. Read both private helpers and the final proof. The mate rotation cancels both inverse
   equivalence triangles and has exactly the displayed adjunction transpose as its component.
   The shifted tensor inverse is built from the concrete shifted homotopy tensor unit, not an
   arbitrary representative obtained from an existence theorem. The pullback specification
   supplies its shift structure; the structure-sheaf isomorphism concerns the already defined
   pullback. The full module compiles without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.qcqsProjectionMate_shiftedUnit_isIso` compiles and prints
   exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry` or forbidden
   declaration in the delivered source. Verdict: pass.
3. No statements were split off and no new public declarations or holes were added. Checked
   the helpers on zero shift and the unit case: opposite translations compose to degree zero
   and the unit comparison is invertible. Empty schemes require no nonzero stalk or object
   hypothesis. Repeated search with LeanFinder for tensoring with a shifted unit and mates
   across equivalences, grep for `tensorLeft.*IsEquivalence`, `conjugateEquiv_iso`, and
   `commShiftTensorRightQhObj`, and repository searches found no shorter scheme result.
   The existing conjugate-equivalence and K-flat shift tools are used. Verdict: pass.
4. Read the argument from the supplied mate downward. The three original public imports are
   needed by the signature; the three added imports are proof-only and each is used. The only
   old proof dependency omitted is `def-pc-derived-pullback-monoidal-model`, already listed
   under No longer needed. The replacement is the existing structure-sheaf theorem, with no
   new hole. Read `dag/units/sk-thm-picard-duality.json`: its realized fields impose no step
   using the omitted monoidal-model node. The unit-and-shift route is retained. Verdict: pass.
5. Compared node JSONs: only `proof`, `proof_deps`, and `proof_origin` changed. Each recorded
   dependency names the declaration used by the code; the proof steps describe the K-flat
   unit construction, pullback unit/shift transport, categorical mate calculation, and final
   restriction of the supplied comparison. No new nodes require validation. Verdict: pass.

Second-reading changes: cached the existing category and abelian instances locally in the
shifted-unit helper and supplied explicit independent universe parameters to
`DerivedCategory.singleFunctorObjUnitIso`, letting Lean infer its isomorphism type. These
proof-only elaboration changes address repeated instance synthesis and costly unit-type
comparison observed during local timeout diagnostics. The mathematical proof, signatures,
imports, and node route are unchanged from the first worker's delivery. All diagnostic files
are confined to scratchpad and are not delivered.
