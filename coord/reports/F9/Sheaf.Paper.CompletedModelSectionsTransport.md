## What changed

Filled `unit_existsUnique` by final-object sections of constant module sheafification,
the specified constant-to-completion coefficient map, and the existing coefficient-ring
tensor-square isomorphism. The component formula is the existing generator `1 tensor x`.
Generator naturality makes these components commute with every differential and proves
naturality of the actual selected units.

Filled `derivedMap_existsUnique` by K-projective chain representatives. Additivity of
realization preserves homotopies, so two representatives of the same derived arrow
have the same realized derived class; the unit naturality square gives the required
sections equality. All public theorem statements are preserved up to definitional equality.
The only Lean file changed is
`lean/Sheaf/Paper/CompletedModelSectionsTransport.lean`. Its new helpers are private
and fully proved. Private proof imports expose the existing tensor naturality and
final-section helpers in `FiniteFreeCompletedScalarComparison` and
`PointFiniteReductionSectionAlgebra`, and the adopted final-object theorem in
`AlgClosedFieldSiteColimits`. The item's existing DAG node records the new route;
no new node is needed. In `scalarLocalizedNaturality`, the two representative-
independence proofs now compose the existing fraction formulas with the functorial
image of the representative equality. Its statement and mathematical argument are unchanged. The generator naturality
proof transports the section equality directly with `congrArg`. Its model and generator
expressions, and the term-unit goal, are unfolded explicitly before the calculation,
so elaboration follows their prescribed definitions directly. Two private calculation
lemmas evaluate the tensor-square and final-sheafification isomorphisms, keeping the
unit proof from repeatedly unfolding their constructions.

The coefficient telescope of `completedModelSectionsTransport` is beta-expanded and
specialized as a single expression to share its canonical algebra structures. A private,
fully proved generic adapter converts the constructibility hypotheses. Checking this
statement now takes about 0.1 seconds instead of ten seconds. A separate Lean check
applied the new form to the original signature verbatim and compiled in 15.7 seconds.
A second check proved equality of the complete old and new proposition telescopes
by `rfl` and compiled in 22.2 seconds.
The change record is
`coord/changes/completed-model-transport-coefficient-telescope.md`.
There are zero external Lean consumers; no consumer adaptation is required.

## Proved and sorry left

Closed the two existing holes:

- `WeilConjectures.CompletedModelSections.unit_existsUnique`.
- `WeilConjectures.CompletedModelSections.derivedMap_existsUnique`.

No holes added; no `sorry` remains in the item. Both belong to
`lem-pod-completed-model-sections-transport`.

## No longer needed

The projective-summand construction planned for the unit is unnecessary: sheafification
at the final algebraically closed point already identifies the actual sections.
No public import is removed and no node or dependency module is withdrawn; the other
proof steps still use the recorded dependencies. The finite-projective hypotheses remain exactly
as stated and supply K-projectivity for the derived-map proof. The existing
perfect-complex interface already supplies the K-projective representative theorem
and module-projective instance, so no extra imports are needed for those results.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy. The node's unit plan can be shortened using the existing
`lem-trf-point-sheafification-final`. The node's proof and proof dependencies have been
updated to record that argument.

Validation: the complete revised module compiled in 43.1 seconds through
`lcompile.py` with aggregate profiling enabled; profiling options are removed from the
packet. The original-signature application and the direct `rfl` equality check passed.
The item has zero remaining holes. The axiom probe confirms that
`unit_existsUnique` and `derivedMap_existsUnique` each use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
