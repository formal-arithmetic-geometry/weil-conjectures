## What changed

Repaired the returned delivery by preserving the concurrently landed
`Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition` and its node unchanged.
The earlier delivery treated these as new files, but they now contain a different
public composition theorem. Neither file is included in this repaired delivery.

Moved the fully proved composition calculation into private helpers in the assigned
`Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend` module. The public theorem
`AlgebraicGeometry.Etale.abelianRawPullback_coherent_extend` retains its signature and
public imports. Its proof derives the coefficient identity from `colimit.w`, `hH`,
and isomorphism cancellation, then applies the private composition calculation and
componentwise extensionality. The intentionally unused `hφid` and `hφcomp` remain;
the unused-variable linter is disabled only for this public theorem.

Private proof imports supply `upperStarComp_assoc'`, generic single-complex
compatibility, and shift compatibility. The private composition calculation first
works with arbitrary Grothendieck abelian coefficients, then specializes to abelian
groups. All helpers are proved; no interface change or forced adaptation is needed.
Updated the original node's proof and dependencies to describe this complete route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.abelianRawPullback_coherent_extend`
(`lem-sbc-abelian-raw-pullback-coherence-extend`).

Private proved helpers: `shiftedHom_comp`, `singleComparison_source`,
`singleComparison_target`, `pullbackHom_comp`, and
`abelianHigherDirectImageRawPullback_comp`.

Original holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
No unproved intermediate statement was split off. The concurrently landed public
`abelianHigherDirectImageRawPullback_composition` is unchanged and is not imported
or used by this proof.

## No longer needed

Removed the original direct proof imports
`Sheaf.AlgebraicGeometry.DerivedInverseImageComposition` and
`Sheaf.AlgebraicGeometry.AbelianPullbackSingleComposition`.

Nodes `lem-weil-pbc-derived-inverse-image-composition` and
`lem-sbc-abelian-pullback-single-composition` are unnecessary for this route.
The proved generic single-complex ingredients in `EtalePullbackSingleComp` and
shift helpers in `AbelianDerivedDirectImageTransitionShift` are used directly.
Underived associativity comes from `WeilConjectures.SixFunctors.BaseChange.Pasting`.

Compared with the returned delivery, the import of
`Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition` and dependency on
`lem-sbc-abelian-raw-pullback-composition` are also removed. Its calculation is now
private in the assigned module. No unit statement or unit proof step is bypassed.
These modules may remain reachable along other branches; this report describes
pruned proof dependencies, not global unreachability.

## Where the brief, the DAG or earlier work was wrong

The previous delivery's base predated another landing of the composition module
and node. Replacing those files would remove the concurrently landed public theorem
and alter the existing node's statement. This repair avoids both changes by moving
only the earlier delivery's proved helpers into the assigned module and updating
its proof route. The previous second reading concerned the superseded two-module
layout and has been removed so the new delivery can be independently read.

The bundled derived-coherence theorem is stronger than this proof needs. Generic
single-complex compatibility, shift compatibility, source associativity, and the
colimit coefficient identity suffice. No mathematical statement is disputed.
Search results from the original work remain recorded in the assigned node and
searches.jsonl. No new nodes or change records are added.

## Second reading by J2

1. Compared the complete delivered module and node with the repository versions.
   The existing `abelianRawPullback_coherent_extend` signature is byte for byte
   identical, including `hφid`, `hφcomp`, all coefficient equations, and the
   conclusion. The public imports and visibility are unchanged. There are no
   definitions, other delivered modules, new nodes, or change records. Pass.
2. Compiled the module locally through `lcompile.py`: clean, 29.0 seconds.
   Compiled a scratch copy with `#print axioms` for the public theorem and all
   five private helpers: each uses only `propext`, `Classical.choice`, and
   `Quot.sound`; none uses `sorryAx`. The delivered source contains no `sorry`
   or forbidden declaration mechanism. Read the actual five-factor raw map in
   `AbelianHigherDirectImageNaturalComparison`: `pullbackHom_comp` reproduces
   it exactly. The scheme substitutions and proof irrelevance identify its
   equality witnesses without assuming an extra equality. Pass.
3. Nothing is split off. Read `shiftedHom_comp` as a generic equality of
   morphisms: source compatibility, naturality of the comparison, and its
   CommShift law account for every factor. Read both single-comparison lemmas:
   the inserted isomorphisms cancel in the displayed orientations. Their
   applications use the existing generic `plus_single_comp` and
   `plus_single_natIso`, not the module-coefficient specialization. No arbitrary
   data is chosen from an unproved existence theorem. The calculations permit
   identity maps, zero classes and coefficients, empty schemes, and zero or
   negative integer shift; the public conclusion is vacuous for an empty index.
   Searched the library for raw composition and the generic helper names, and
   ran Loogle for `NatTrans.CommShift` (unknown identifier, no search hits).
   The existing public `abelianHigherDirectImageRawPullback_composition` still
   has `sorry`; using it would lose the axiom-free proof achieved here. Pass.
4. Read top downward: `hc` follows directly by precomposing `colimit.w` with
   `(eH i).inv`, substituting `hH`, and cancelling the inverse-hom pair.
   Componentwise extensionality and the prescribed raw components then reduce
   the goal to the proved private composition calculation. Both new `import all`
   imports are proof-only and needed for private generic single and shift
   helpers; Pasting supplies `upperStarComp_assoc'`. The report names both
   original proof dependencies and both removed direct imports. Read
   `dag/units/sk-lem-failure-field.json`: this replaces only a subordinate
   coherence calculation and does not bypass its failure-detection argument or
   any realized unit node. Pass.
5. Compared node fields: only `proof`, `proof_deps`, and `proof_origin` change.
   Read the two new dependency nodes and their Lean modules. The proof record
   explicitly distinguishes their generic private ingredients from the public
   specialized statements; the steps track source associativity, single
   comparisons, shift naturality, coefficient cancellation, and extensionality
   in the actual proof. Its dependency list is exactly the union of step uses.
   Pass.

Second reading changed only this report by recording the independent review.
No proof or metadata repair was needed. Original holes closed: 1; holes added: 0.
