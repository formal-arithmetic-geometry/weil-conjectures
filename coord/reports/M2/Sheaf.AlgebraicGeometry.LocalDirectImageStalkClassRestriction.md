## What changed

Reduced AlgebraicGeometry.localDirectImage_stalk_class_restriction to two separate
comparisons, combined by transitivity of equality. Added proof-only imports of
LocalDirectImageStalkClassTopComparison and TargetSectionClassRestriction. The
original signature, visibility, definitions and unit route are unchanged.

The earlier sandbox attempt did not pass compilation: its final conversion unfolded
the chosen injective resolution and exceeded the file limit. Replaced its generic
ResolutionSectionClassTopComparison obligation with the top-open computation of the
defined class map using the supplied resolution. This still covers only change of
resolution; it has no smaller open, restricted-resolution choices or restriction map.
The other obligation covers restriction and germ compatibility with that resolution
fixed, using Mathlib germ_res_apply. Neither new
statement is a restatement of the item's theorem.

## Proved and sorry left

Closed the hole in AlgebraicGeometry.localDirectImage_stalk_class_restriction by a
Lean proof from two strictly separate intermediate comparisons. This is a
decomposition, not a sorry-free proof of the underlying mathematics: one hole closed,
two added (net minus one). No sorry remains in the item's module.

Added holes:

- AlgebraicGeometry.localDirectImage_stalk_class_top_comparison
  (lem-weil-pbc-local-direct-image-stalk-class-top-comparison): the defined class is
  the top-open germ of the class from any supplied resolution, without restriction
  to a smaller open or restricted-resolution choices.
- AlgebraicGeometry.Scheme.Modules.FlatBaseChangeOpenChoices.targetClass_restriction
  (lem-weil-pbc-target-section-class-restriction): restriction with a fixed global
  resolution, followed by germ compatibility, without changing that resolution or
  using the defined local class map.

All three modules compile with no warnings: the two intermediate modules in
4.6 and 9.7 seconds and the main module in 12.6 seconds.
The docstrings give the sources and complete arguments. Edge cases checked
mathematically: degree zero, zero modules and top opens; an empty V cannot
contain the required point y. Neither assumes that theta is invertible on sections.
No data is chosen from an unproved existence theorem, and no definition is modified.

## No longer needed

No original import was removed and no existing module is pruned. The previous
sandbox's ResolutionSectionClassTopComparison module and
lem-weil-pbc-resolution-section-class-top-comparison node are absent from this
delivery; their role is replaced by the explicit top-open computation above.

The original direct dependencies on resolution lifts, homotopy independence,
cohomology-map functoriality, the sections quasi-isomorphism and derived-functor
naturality are covered inside the two new nodes. Lift existence, functoriality,
sections quasi-isomorphism and derived-functor naturality remain dependencies there;
homotopy independence is supplied by the functoriality dependency. No realized unit
statement or step is bypassed.

The old direct proof dependencies removed from the item node are:

- lem-weil-pbc-derived-functor-map-via-lift;
- lem-weil-pbc-homotopic-maps-equal-cohomology;
- lem-weil-pbc-injective-resolution-lift-exists;
- lem-weil-pbc-module-cohomology-fmap-functorial;
- lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso.

These are replaced as direct dependencies by the two new comparison nodes. This
is dependency relocation, not pruning of their modules from the import closure.

## Where the brief, the DAG or earlier work was wrong

The original general lift and functoriality declarations do not state the required
section-class naturality comparisons. Those are made explicit as the two obligations.
The delivery tool initially classified a short expression applying transitivity to
the two new theorems as a single application. The final proof names both intermediate
equalities explicitly and then combines them; both statements are strictly separate
parts of the argument.

The earlier report claimed a compiling reduction, but the inherited final proof
exceeded 60 seconds. The corrected route avoids expanding the canonical resolution
in the combining proof. It keeps the statement and definitions unchanged.

Read the unit statement, steps and realized nodes in dag/units/sk-thm-p1.json; the
blueprint unit source is absent locally. Read Stacks Tags 01E4 and 01FB. LeanSearch's
Internal Server Error is recorded as unavailable, not as a no-match search.

## New nodes

lem-weil-pbc-local-direct-image-stalk-class-top-comparison is the identity-lift and
naturality part of the original argument, followed by the top germ. It is stated in
Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassTopComparison. Its conclusion uses
the defined class map but has no restriction or restricted-resolution data.

lem-weil-pbc-target-section-class-restriction is the augmented restriction-lift and
section-complex restriction part, generalized to a scheme square with the supplied
global resolution fixed, followed by Mathlib germ compatibility. Its module is
Sheaf.AlgebraicGeometry.TargetSectionClassRestriction. No change record is needed.


## Second reading by M2

1. Interface: PASS. Compared all delivered Lean files with the repository. The
   existing theorem signature is byte-for-byte identical; only its docstring,
   proof and two plain proof imports differ. The two other modules are new.
   No existing definition, visibility, public import or target statement changes;
   no change record or forced adaptation is required.
2. Kernel and holes: PASS as a decomposition. Independently compiled all three
   modules through lcompile.py, without errors or warnings (4.6, 9.5 and 11.2 s).
   Scratch copies with #print axioms for each of the three declarations compiled;
   each reports precisely propext, Classical.choice, Quot.sound and sorryAx.
   There are exactly the two named theorem holes reported above, no definition
   holes and no forbidden declaration forms. The combining proof uses both
   intermediate equalities. It does not establish a sorry-free mathematical
   theorem: one original hole is closed and two smaller holes are added.
3. Split statements: PASS. Read the actual definitions of resolutionSectionClass,
   sectionCohomologyComparison, sectionCohomologyTheta, targetClass, the restricted
   resolution choices, and the cohomology-map data. Rechecked Stacks 01E4, 01FB
   and 01EZ. The augmentation equation pins the restricted-resolution comparison;
   its degreewise sections equation prevents an arbitrary twist. Identity-lift
   naturality proves the top comparison, and an augmented restriction lift plus
   cancellation of its sections quasi-isomorphism proves the fixed-resolution
   restriction comparison. The docstrings spell out these distinct arguments;
   neither merely renames the original statement. Checked degree zero, the zero
   module, top V, and the impossible empty-V case. The arbitrary-g restriction
   statement requires no flatness or invertibility of theta on sections.
   Independently searched leanfinder, loogle and Mathlib grep with different
   queries; also searched lean/Sheaf and lean/WeilConjectures. Found naturality,
   germ_res_apply, higherDirectImagePresheaf, and cohomology-map independence
   ingredients, but no theorem with either displayed comparison. The presheaf
   restriction theorem uses openModuleCohomologyRestriction, not the supplied
   restricted-resolution/moduleCohomologyFMap identification required here.
   Closing either obligation still needs several comparison squares, rather
   than a short application of an existing result. No object is chosen from
   a newly holed existence theorem.
4. Route and pruning: PASS after reporting repair. The main proof is the direct
   transitivity reduction and its two new imports are proof-only. Each public
   import in a new module supplies symbols in its statement. Both original
   imports supply symbols in the unchanged main signature. Read sk-thm-p1's
   statement, steps and realized lists: none of these three nodes realizes a
   unit statement or step, and no realized node is removed or bypassed.
   The five old direct proof dependencies are now listed explicitly above;
   their relocation does not count as pruning of modules.
5. DAG: PASS. Checked every node's Lean statement verbatim against its module,
   and checked proof_deps equals the union of proof-step uses. The existing node
   changes only proof, proof_deps and proof_origin; its statement and metadata
   remain unchanged. The new nodes include their source, full argument, three
   successful search kinds, split status, creation provenance, blueprint origin,
   chapter/unit and exact Lean records. Their proof plans agree with the two
   mathematical obligations and the main node agrees with the Lean reduction.

Second reading changed only the report (explicit old-dependency inventory and
this review) and the two new nodes' search records (independent searches added).
No Lean proof or statement needed repair. Verdict: deliver the decomposition,
with one hole closed, two holes added, net minus one, and no module pruned.
