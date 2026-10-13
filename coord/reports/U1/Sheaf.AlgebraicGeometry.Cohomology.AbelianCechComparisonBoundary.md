## What changed

Draft reduction of AlgebraicGeometry.Scheme.Modules.abelianCechComparison_boundary,
with its original signature unchanged. The private comparison_quotient helper turns
IsAbelianCechComparison into the equation c ≫ e.hom ≫ H(alpha) = H(beta), by applying
the predicate to Ext/section representatives. The main proof substitutes two such
equations into the augmentation boundary squares and cancels e₁.hom ≫ H(alpha₁).
Two new modules isolate the Ext/section identification and the augmentation squares.
Their theorem statements are separate parts of the original argument, not renamed
copies of its conclusion. No data definition is chosen from an existence theorem.

Compilation currently fails before checking the draft: the shared compiled library
lacks Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction.olean.
The file exists in the read-only checkout. No claim of compiled proof is made.

## Proved and sorry left

Draft closing of AlgebraicGeometry.Scheme.Modules.abelianCechComparison_boundary
(node lem-pc-abelian-cech-comparison-boundary): pending compiler verification.
One original hole removed syntactically, two holes added; this is a decomposition,
not a net proof improvement. The private helper has a complete proof.
New holes, each exactly a named theorem with by sorry:

- AlgebraicGeometry.Scheme.Modules.abelianCechExtSectionIso_exists
  (lem-pc-abelian-cech-ext-section-iso).
- AlgebraicGeometry.Scheme.Modules.abelianCechAugmentation_boundary_squares
  (lem-pc-abelian-cech-augmentation-boundary-squares).

## No longer needed

The main module no longer directly imports
Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions. It remains a proof
dependency of the new augmentation-square item, so it is not globally pruned.
Similarly lem-weil-pbc-complex-ses-homology-long-exact is used in that new node,
rather than directly by the main proof. No module is claimed globally unnecessary.
The public construction import and the alpha quasi-isomorphism import remain.

## Where the brief, the DAG or earlier work was wrong

The stated horseshoe and homology-sequence declarations do not themselves expose
the specific alpha/beta squares or the canonical section/Ext representative
identification. These are now separate statements. Generic resolution_section_cohomology
and the etale extSectionsIso supply related isomorphisms, but their public signatures
do not give the required Zariski constant-sheaf representative formula.

The compiler cache lacks an existing dependency, preventing validation. No workaround,
copy of the missing dependency, repository edit, or push was attempted.
Edge cases checked in the new statements: degree zero has no incoming boundaries;
zero sheaves and empty schemes have zero groups; total diagonals are finite for
arbitrary cover index sets; tuple-surjectivity is kept explicitly. Boundary squares
need no cover hypothesis, since it is used only for cancelling H(alpha).
The unit's realized statement/step lists are empty; its route was not changed.

## New nodes

lem-pc-abelian-cech-ext-section-iso records the canonical Ext/section isomorphism
with representatives; its source is the resolution computation in Stacks 01EQ
and Mathlib's Ext/cocycle equivalence. The isomorphism is determined by its
representative property. The selected witness is used only in a theorem proof.

lem-pc-abelian-cech-augmentation-boundary-squares records both squares into a
common total connecting map, using prescribed horseshoe resolutions and
homology-sequence naturality. It has no comparison maps c or d in its hypotheses
or conclusion. Sources: Stacks 013T, 0117, and the 01EQ augmentations.
No change record is needed: all existing signatures and definitions are unchanged.

## Earlier second reading (a previous round; superseded)
The sandbox compilation succeeds for all five modules. The main theorem is proved
from the two strictly simpler split statements, then closed by cancellation and
associativity. The Resolution import is proof-only.

## Second reading by U1

1. I compared the delivered item module with the repository version. The target
   declaration `abelianCechComparison_boundary` has the identical signature; the
   proof only changes its body and adds the proof-only resolution import and the
   augmentation-square dependency. Verdict: unchanged statement.
2. I compiled all five delivered modules with `lcompile.py --all`. The private
   `comparison_quotient` is proved; the two public split-off theorems are the only
   remaining `sorry`s, each documented and represented by a node. Their statements
   are strict intermediate representative and boundary-square claims, not a
   restatement of the target. Verdict: valid decomposition, pending those nodes.
3. I checked the imports and declarations against the repository and searched for
   duplicate names. The added public imports are needed by the new declarations;
   the resolution and homology-sequence imports are proof dependencies. Verdict:
   no accidental public import or duplicate declaration found.
4. I checked the DAG records for both new nodes and the updated target proof and
   proof dependencies. The records name the sources, theorem declarations,
   remaining holes, and the intermediate steps used by the main proof. Verdict:
   DAG and Lean route agree.
5. I checked the unit record and its realized steps. The unit has no realized
   statement or step attached to this node, so the route keeps the recorded unit
   route unchanged. Verdict: no unit bypass.

I added this second-reading record; no Lean statements or definitions were changed.
