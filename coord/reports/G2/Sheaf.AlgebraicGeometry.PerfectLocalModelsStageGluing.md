## What changed

The assigned theorem now obtains a stage object and compatible local limit comparisons
from the new module Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons. It proves
that the inverse-image opens cover, applies derived_hom_mayer_vietoris exactness to construct the
global map, and constructs both pointwise witness families by choosing a covering open.
The localized restriction equations identify the local maps with isomorphism homs.
A proved private helper model_witnesses_of_local_comparisons performs the Hom exactness
and cover-witness argument with abstract schemes, avoiding repeated expansion of the
large stage base-change expressions. A second proved private helper transports invertibility through the exact open-site equivalence
and mapDerivedCategoryCompIso to schemeOpenRestriction. All public imports are unchanged. The non-target theorem signature now uses local
let bindings for Yj, X and gj, sharing its repeatedly expanded geometric expressions.
The proposition is definitionally identical after reducing the lets; every original
hypothesis and conclusion remains. This presentation change is recorded in
coord/changes/perfect-local-models-stage-gluing-sharing.md. Both delivered modules compile through
lcompile.py without errors or warnings. No sorry remains in the assigned module. The delivery parser classifies the let-sharing
presentation as an interface change; the change record accounts for every downstream module. No definitions or target statements change.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.perfect_local_models_stage_gluing
(lem-pc-perfect-local-models-stage-gluing), by a complete proof from named declarations.
Added one hole: AlgebraicGeometry.perfect_local_models_stage_comparisons
(lem-pc-perfect-local-models-stage-comparisons), in its own new module. This is a
decomposition: one hole closed, one added, net zero. The new theorem constructs a stage
object with two perfect covering restrictions and compatible localized-site limit isomorphisms;
it supplies neither a global comparison morphism nor the pointwise witness conclusions.
The real combining proof constructs these using existing Hom gluing and the cover laws.
There are no other sorry declarations in the delivery, no data definitions, and no
anonymous or private holes.

## No longer needed

The assigned module removes these direct proof imports:
Sheaf.AlgebraicGeometry.DerivedPullbackComposition,
Sheaf.AlgebraicGeometry.PerfectDescendMorphisms,
Sheaf.AlgebraicGeometry.DerivedPullbackPerfect,
Sheaf.AlgebraicGeometry.DerivedOpenGluing,
Sheaf.AlgebraicGeometry.OpenPerfectModelTransport,
Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses,
Sheaf.AlgebraicGeometry.SchemeDerivedHomGluing.
The complete list removed from the old node's direct proof_deps is:
lem-pc-derived-pullback-open-restriction-universes,
lem-pc-derived-pullback-perfect,
lem-pc-perfect-descend-morphisms,
lem-pc-ringed-spaces-derived-pullback-composition,
lem-sc-derived-open-gluing,
lem-sc-open-perfect-model-transport, and
lem-sc-scheme-derived-hom-gluing.
The first four remain needed by the new stage-comparison construction; their
modules are not pruned from the import closure by this move.
DerivedOpenGluing and its node lem-sc-derived-open-gluing are replaced by the smaller
DerivedOpenGluingObjects / lem-sc-derived-open-gluing-objects object-only assertion.
Thus the unused global-morphism clause is not imported through this wrapper.
OpenPerfectModelTransport and its node lem-sc-open-perfect-model-transport are no longer
needed by this proof: the stage object is perfect on the supplied covering opens, and
pointwise neighbourhood witnesses just choose a cover member.
SchemeDerivedHomGluing and its node lem-sc-scheme-derived-hom-gluing are also no longer
needed: we use the localized-site Hom Mayer-Vietoris theorem directly.
These modules are not asserted globally unreachable through other target branches.
The unit sk-thm-picard-semicon has no realized nodes for this step; its route
and all unit records remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical proposition was changed or disputed; the theorem type is presented
with let sharing as recorded above. The plan's geometric stage-construction
step needs substantial tail/restriction/comparison bookkeeping beyond its supplied
interfaces; that is the explicitly retained intermediate theorem. The final Hom-gluing
step is implemented from the existing localized-site Mayer-Vietoris theorem.
The transported overlap-composition definitions were expensive to elaborate; the new
statement uses canonical localized-site Hom restrictions instead, preserving the same
mathematical overlap equation without changing any existing definition.
Explicitly supplying the two existing derived-category instance families in the
intermediate-theorem application avoids expensive unification of the chosen localizations;
this preserves precisely the given instances and brings compilation below the file limit.
The local Stacks tex files are absent in this clone; the official statements and proofs
of Tags 09RF, 09RE and 08DG were read at
https://stacks.math.columbia.edu/tag/09RF,
https://stacks.math.columbia.edu/tag/09RE and
https://stacks.math.columbia.edu/tag/08DG.
Mathlib searches ran through msearch.py: LeanFinder returned scheme-gluing declarations,
Loogle returned functor/iso facts, and grep found no stage-perfect gluing theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable.
The new statement was checked on empty schemes, empty overlaps, equal covering opens,
zero objects and non-strict preorders. All use the same directed-tail construction;
no nonemptiness, global perfectness or strict inequality hypothesis is introduced.

## New nodes

lem-pc-perfect-local-models-stage-comparisons, in
lean/Sheaf/AlgebraicGeometry/PerfectLocalModelsStageComparisons.lean, records the geometric
stage-object construction and the compatibility of its local limit isomorphisms before
Hom gluing. Its docstring and node give the overlap-descent, stabilization, object-gluing,
perfect-restriction and comparison-equation arguments with their existing dependencies.
Its source is the two-open construction in Tag 09RF and the object-gluing part of Tag 08DG.
Change record: coord/changes/perfect-local-models-stage-gluing-sharing.md.
No adaptation is necessary: reducing the introduced lets recovers the original type.
The unchanged original PerfectLocalModelsEventuallyCompatible compiled against the
changed module in 14.8 seconds with no errors or warnings; its temporary verification
copy was removed from the delivery set.

## Second reading by G2

1. Compared both delivered modules with the repository. The new comparison module
is new; the only existing public declaration is perfect_local_models_stage_gluing.
Its signature has the documented let-sharing presentation change, fully recorded
in coord/changes/perfect-local-models-stage-gluing-sharing.md. Reducing Yj, X and
gj recovers every original parameter type and the identical conclusion. Public
imports, the existing docstring, definitions and target statements are unchanged.
A scratch theorem with the original repository signature applies the delivered
theorem to every original argument and compiled successfully in 13.0 seconds.
No other module is adapted. Verdict: pass, with the declared presentation change.

2. Independently compiled the two-module set using lcompile.py: comparisons in
55.4 seconds and gluing in 47.8 seconds, without errors or warnings. Scanned both
sources: the single remaining sorry is the public named comparison theorem;
there is no new definition or forbidden axiom, unsafe, opaque, extern or
implemented_by declaration. Scratch #print axioms checks show only propext,
Classical.choice and Quot.sound for both proved private helpers; the main theorem
and the comparison theorem additionally depend on sorryAx. Verdict: a checked
reduction, not a sorry-free geometric theorem.

3. Read the new statement, its complete docstring proof and its node against
Stacks Tags 09RE, 09RF and 08DG. The compact overlap is quasi-compact because
Yj is quasi-separated; its inclusion and its structure map are finite
presentation. Descent on the directed tail supplies the prescribed transition
and inverse equations; object gluing supplies F and the compatible local
comparisons, with perfectness invariant under their isomorphisms. E itself need
not be assumed globally perfect. Empty schemes, empty overlaps, one empty cover
member, equal opens, zero objects and reflexive/non-strict index transitions add
no missing hypothesis. The input j provides nonemptiness of the directed tail.
No arbitrary witness is put into a definition. The new theorem omits the global
morphism and both pointwise witness families: it isolates the geometric
construction, while the caller proves the Hom exactness and cover arguments.
Verdict: true and a strict part of the argument; retained as one decomposition
hole, too substantial to close in a few minutes.

Repeated independent searches with different wording: LeanFinder for descent of
an overlap isomorphism between perfect complexes returned scheme-gluing and
section-stabilization results, not a derived-stage construction. Loogle found
NatIso.isIso_map_iff, precisely the transport lemma already used. The msearch
grep query found no direct match; local rg found PerfectDescendMorphisms,
DerivedOpenGluingObjects and the upstream consumers, which were read. No
existing declaration replaces the comparison construction.

4. Read the proof from its conclusion downward. Hom Mayer-Vietoris exactness
produces the actual global map with the prescribed restrictions. The inverse-image
cover follows from preimage_sup and preimage_top. Each neighbourhood witness is
one cover member; invertibility is transported by the exact open-site equivalence
and mapDerivedCategoryCompIso. There is no adjunction detour or new categorical
hole. Proof-only imports use plain import, and the geometric dependencies remain
in the comparison module for its stated construction. The report now lists every
old direct proof_deps entry removed, distinguishing four moved dependencies from
three replaced nodes. The unit sk-thm-picard-semicon has empty realized lists;
the chapter/unit records and two-open descent route are retained. Verdict: pass.

5. Checked the nodes' Lean statements verbatim against the source signatures;
both match. Each proof_deps list is exactly the union of its proof steps' uses.
All dependencies name existing recorded declarations, apart from the new
comparison node supplied in this delivery. The new node has source, creation,
blueprint lineage, chapter/unit, searches, proof_origin and full Lean record.
The item's node records the construction, Hom gluing and cover-witness steps
actually used. Verdict: pass.

Second reading changed only this report: completed the explicit removed-node
list and documented the independent reading and checks. Lean proofs and node
files were retained. One original hole closed, one new hole added, net zero.
