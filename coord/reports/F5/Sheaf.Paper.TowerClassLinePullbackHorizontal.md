## What changed

Proved the restored item and retained the complete signature of
AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_components_horizontal.
Its proof conjugates the two paths, transposes with the actual finite adjunction,
tests only on generators 1 tensor z, computes the two paths separately, then cancels
the conjugating isomorphisms.

Repaired the shared Geometry definition in SmoothPurityTowerShriekData: its old
horizontal normalization referred to freely supplied generic underlying-sheaf
identifications. Added ordinaryUnitTransition, requiring the actual finite adjunction
units to commute with horizontal restrictions. OrdinaryUnitTransition is a real
irreducible predicate for that formula, keeping Geometry small during kernel checking.
It mentions no Chern datum, root, finite root-line comparison or line-pullback square.
The B abbreviation now directly names the same actual constant ring sheaf; this
definitional equality gives the finite functor domains their direct constant-ring
presentation. All existing fields, public imports, operation names and theorem
signatures are retained.

ScalarExtensionSectionNaturality proves restriction naturality of scalar extension
on an arbitrary ringed site. TowerLineTransitionTensor uses it and the rootForget
transition equations to compute the root-line transition on unit tensors.
TowerLinePullbackLowerTensor proves the lower-path tensor formula from the repaired
actual-unit normalization and root direct-image naturality. Ring homomorphisms
preserve one; neither general scalar-action normalization nor general coefficient
transition naturality is needed.
Adapted the explicit constructor in TowerClassSectionGeometryExistence by proving
its added ordinaryUnitTransition field from the existing finite transpose
normalization and restriction-underlying identity. Its complete public
signature and the original ordinary and derived constructions are retained. This
module was unclaimed when copied. Its actual-unit proof uses two private
general lemmas about normalized adjunction transposes on ringed sites, then
transported as a complete finite-adjunction package.
The scalar-extension transition, root-line transition, lower-path and horizontal
square theorems have passed single-file compilation. All new helper statements
have complete proofs; there are no split-off obligations.

Change record: coord/changes/F5-actual-horizontal-unit-normalization.md.

## Proved and sorry left

Original item: one sorry, in
AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_components_horizontal
(node lem-sfb-tower-class-line-pullback-horizontal).
The original Geometry definition was inadequate, so the archived claim with that
meaning is disputed. This is explicitly a definition repair, not a claim to prove
the old false interpretation. After repairing the geometry normalization, the item
and the supporting naturality, unit-tensor path and transition theorems compile.
The adapted constructor and its unchanged direct consumer
TowerClassUnitLevelCoordinates compile. All 16 current direct importers of the
changed data module passed compatibility compilation.

No literal sorry remains in the delivery files, and no new sorry or axiom is added.
There are no hollow definitions or arbitrary data chosen from unproved existence.
The extra field of Geometry is a proof of a concrete normalization law of the actual
termwise inverse image; it is not a new object or a root-line compatibility assumption.

Supporting declarations:
WeilConjectures.SemilinearSections.scalarExtensionSection_transition
(node lem-coef-scalar-extension-section-naturality),
AlgebraicGeometry.ProEtale.SpTowerClasses.lineEvaluation_transition_tensor
(node lem-sfb-tower-line-transition-tensor), and
AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_lower_tensor
(node lem-sfb-tower-line-pullback-lower-tensor).

The repaired shared data module and the adapted constructor originally had zero
sorry and still have zero. The item closes its one hole and adds zero holes.
The unchanged direct parent TowerClassLinePullbackExistence compiles against the proof.
After profiling cleanup, lcompile accepted all six delivery modules. It also
accepted the 16 direct data importers, the constructor consumer, and the item
consumer. Every unchanged temporary importer copy was removed. All six delivered
Lean files have zero literal sorry, no profiling options, and lines of at most
100 characters.
Inherited obligations of imported modules are not claimed closed by this delivery.

## No longer needed

No existing public import, module or quarantined attachment is removed.
lem-sp-tower-line-evaluation-universal is no longer a direct proof dependency of
the item: the already proved lineEvaluation normalization suffices. Its module
remains needed transitively and is not withdrawn.
def-sp-tower-class-chern remains needed through the transition lemma; its root
and scalar data are still used. def-sp-tower-shriek-data remains a statement
dependency and supplies the actual-unit law through the lower-path proof.
def-sp-tower-class-pullback remains needed for the statement and root restriction.
The old direct proof dependency def-coef-semilinear-geometry-derived is replaced
by the repaired actual-unit interface. Its module remains required by Geometry's
existing fields, so it is not withdrawn. def-cbc-strict-constant-tower-operations
remains a statement dependency: the finite functors and coefficient map still occur
in the unchanged signature. Its general coefficient-transition calculation is not
needed in the proof. The universal property needs only values on 1 tensor z, so
semilinear scalar-action calculations are omitted as well. No blueprint unit or
proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old definition): the original Geometry interface permits
level-dependent scalar conjugation of the horizontal system operations. Modify the
generic moduleUnderlying identifications and levelPushUnderlying by reciprocal
units and transport the tensor/derived comparisons by the same conjugation. Its
old equations, fixed finite adjunction package and identity-on-carrier evaluations
are preserved. For f=id and l=3, opposite signs at levels 0 and 1 insert a minus sign
in the pulled root-line transition while the normalized finite comparisons remain
the canonical identity-pullback comparisons. On a scheme with all 3-power roots, the level-0 nonzero root tensor then
contradicts the archived horizontal square. The change record gives the construction.

The genuine termwise inverse image satisfies actual finite-unit naturality; requiring
that law fixes the missing horizontal normalization independently of arbitrary generic
underlying-sheaf identifications. The definition node now states the law explicitly.
All its citing nodes are recorded in statement_change. Because this repairs a shared
definition used downstream, the affected targets' statement-meaning reviews reopen
under AGENTS.md section 4; comparator target signatures themselves are unchanged.

## New nodes

lem-coef-scalar-extension-section-naturality, in
Sheaf.Paper.ScalarExtensionSectionNaturality: the scalar-extension section commutes
with site restrictions, proved from the ordinary unit and presheaf naturality.
It handles an arbitrary coefficient tower, without roots, Chern data, or geometric
pullback. Its conclusion uses HEq to retain the underlying section carrier during
restriction of scalars.

lem-sfb-tower-line-transition-tensor, in Sheaf.Paper.TowerLineTransitionTensor:
the actual line transition sends the inverse-evaluated unit tensor to the
inverse-evaluated lower unit tensor, with HEq recording coefficient restriction.
It is proved without geometric inverse image or finite pullback comparisons.

lem-sfb-tower-line-pullback-lower-tensor, in Sheaf.Paper.TowerLinePullbackLowerTensor:
the lower path of the finite adjunct on a unit tensor, proved using one level-n
morphism and its unit-tensor formula. It requires neither cX nor a level-m comparison or a family of isomorphisms.
Its conclusion is a calculation on one unit tensor. The other path is computed independently in the item.

Change record: coord/changes/F5-actual-horizontal-unit-normalization.md.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
