## What changed

The signature of AlgebraicGeometry.proper_flat_rightAdjoint_open_support is unchanged.
Its complete Lean proof now follows the five steps of the existing node. The proof
uses properFlat_derivedDirectImage_perfect, transports perfectness through hF on local
strictly perfect representatives, applies case (i) of exists_perfect_annihilator to
the adjoint map, and cancels the restricted isomorphism supplied by the new transport
lemma. DerivedOpenLocalization supplies open derived models without adding hypotheses
or equating the independent universes wXT and wYT.

Added PerfectOpenSupportDetection, proved from the existing supported perfect generator
with full support, perfect supported map lifting with T=X, and perfect-implies-QCoh.
Every shifted perfect test lifts; naturality of mapDerivedCategoryCompIso transports
the assumed vanishing to the open subscheme; the generator detects zero; homology and
restrictStalkNatIso give the stalk conclusion. Two proved private helpers construct the
open-scheme localization by locally-small transport along the over-site equivalence,
and prove perfect shift closure directly from local strictly perfect representatives.
No thick-closure sorry is used for the elementary shift step.

Added AdjointTensorAnnihilatorTransport for precisely the projection-formula and
adjunction step, including invertibility over the inverse-image open. It assumes the
tensor annihilation equation; it does not assume support of Q or perfection of P.
Thus it neither restates the original support theorem nor hides the perfect-pushforward
and support-annihilation steps. Its existential data are consumed inside a proof only;
no definition chooses an arbitrary object from a sorry theorem.

Updated the parent's proof, proof_deps, and proof_origin, and added both helpers' nodes.
All existing public imports remain. Added proof imports are the two helper modules,
ProperFlatDerivedDirectImagePerfect and DerivedOpenLocalization. The heartbeat settings
are local to the two proofs, with comments: comparing the selected derived models is
expensive. No existing statement or definition changed, and no adaptations are needed.

Sources read: Stacks https://stacks.math.columbia.edu/tag/0E4G (Lemma 48.4.4),
https://stacks.math.columbia.edu/tag/09IM and https://stacks.math.columbia.edu/tag/0A9C.
The local literature/stacks-project directory is absent on this machine; the existing
source references are retained in the DAG. The unit sk-thm-picard-duality has empty
realized statement/step lists; its route was not changed.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.proper_flat_rightAdjoint_open_support
(lem-sc-proper-flat-right-adjoint-open-support).

Added one hole:
AlgebraicGeometry.adjoint_tensor_annihilator_transport
(lem-sc-adjoint-tensor-annihilator-transport), whose entire proof is `by sorry`.
No other delivered declaration has a sorry. The newly added
AlgebraicGeometry.perfect_open_support_detection is proved, as are its two private helpers.

This is a decomposition, not an axiom-free closure of the original theorem: one old
hole is closed and one strictly intermediate hole is added, net zero. Existing imported
holes, including properFlat_derivedDirectImage_perfect and exists_perfect_annihilator,
remain with their existing nodes. They are used as intended by stage 3 and not copied.

Small cases checked in the argument: empty or total open; zero test object or zero map;
unbounded Q (only annihilator case (i), never case (ii)); independent source and target
Hom universes. The detector applies with full closed support, whose complement is empty,
so all lifting/generator support conditions are vacuous. The transport statement needs
no compactness of V and does not infer beta is globally zero from its local vanishing.

## No longer needed

Removed direct proof imports from the original module:

- Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration
- Sheaf.AlgebraicGeometry.PerfectSupportedMapLift
- Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

The last import is wholly unused by the new proof. The first is replaced by the shifted
Hom detector from SupportedPerfectGenerator, so lem-pc-derived-qcoh-perfect-generation
is not a dependency of this proof route. PerfectSupportedMapLift remains needed through
the proved detector, and ProperSupportPerfectDirectImage remains behind the existing
proper-flat specialization. These two modules are not claimed globally pruned.

lem-pc-projection-formula remains a mathematical dependency of the unproved transport
lemma, even though its recorded Sections declaration is insufficient and is not imported.
No claim is made that these removed direct imports are unreachable from all other targets.
PerfectThickClosure was also removed from the new detector during development: the shift
step is proved directly. No other original dependency can be pruned on this delivery's evidence.

For completeness, every original parent proof dependency removed from its direct
proof_deps is accounted for: lem-pc-derived-qcoh-perfect-generation is replaced by
lem-pc-supported-perfect-generator through the detector; lem-sc-perfect-support-map-lift
is used through the detector; lem-pc-proper-support-perfect-direct-image is used through
lem-sc-proper-flat-derived-direct-image-perfect-universes; lem-pc-projection-formula is
used by the remaining transport obligation. def-pc-derived-direct-image remains a
stmt_dep and its module SchemeDerivedDirectImage remains publicly imported: its removal
from proof_deps does not prune that definition or module. The annihilation dependency
remains direct. No whole module is certified globally unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The recorded Lean declaration for lem-pc-projection-formula,
Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso in Sections, states only
higher direct images twisted by an invertible module. Its docstring explicitly says so.
It supplies neither the derived formula for an arbitrary perfect I nor its naturality
and tensor-unit compatibility. The new remaining obligation states the exact portion of
that derived argument needed here; the original formula node is left unchanged.

The general properSupport_perfect_directImage has one common Hom universe and global
families of derived models; the original theorem has two independent universes. The
already-existing ProperFlatDerivedDirectImagePerfect specialization fixes this interface
mismatch, so no new perfect-pushforward statement was introduced.

LeanSearch returned Internal Server Error twice; recorded as unavailable without a
negative search verdict. LeanFinder returned only ordinary pushforward/adjunction or
localization/derived truncation facts. Qualified Loogle returned functor map_isIso and
naturality identities, used as elementary glue but no derived support theorem. Mathlib
and repository grep found the generator/lifting declarations used and only the inadequate
invertible-module formula for the projection step. Blueprint searches found no duplicate
detector; the known projection-formula node is retained as the transport's dependency.

The new transport uses lem-pc-projection-formula and
lem-pc-affine-derived-pullback-tensor-tilde (restriction compatibility) as generic tools
from the Picard representability unit, just as the parent used the projection formula.
Their statements are read in the nodes; their Lean interfaces do not finish this glue.
The maintainer/reader may record these tool uses; no tool_uses field was edited here.

## New nodes

lem-sc-perfect-open-support-detection: a proved global-perfect-test criterion for
vanishing of cohomology stalks on a quasi-compact open, independent of proper morphisms
or right adjoints. Its proof_deps list the exact generator/lifting/QCoh/open-model inputs.
Module: Sheaf.AlgebraicGeometry.PerfectOpenSupportDetection.

lem-sc-adjoint-tensor-annihilator-transport: the remaining projection-formula transport
certificate for a single map whose adjoint already has a perfect tensor annihilator.
It is strictly part of steps 4 and 5, omits all support and perfect-pushforward assertions,
and has a full source-based proof in its docstring and node.
Module: Sheaf.AlgebraicGeometry.AdjointTensorAnnihilatorTransport.

No change records: no existing signature, definition, public import, or namespace
opening changed. The heartbeat setting is scoped to the proof declaration.


## Second reading by T4

1. Compared the sole existing delivered module with the repository using diff. Its
   existing theorem signature and docstring are byte-for-byte unchanged; only proof
   imports, the scoped heartbeat setting, and the proof body differ. The other two
   modules and their nodes are new. There are no changed definitions, target statements,
   public imports of an existing module, or forced adaptations. Verdict: pass.

2. Compiled all three modules with lcompile.py in import order: 7.8, 29.2, and 15.7
   seconds, without errors or warnings. Read both private helpers and the complete
   detector and parent proofs. The only delivered sorry is the named theorem
   AlgebraicGeometry.adjoint_tensor_annihilator_transport, with its source, full
   natural-language construction, and node. No definitions are introduced, and no
   prohibited axiom/unsafe/opaque/extern mechanism occurs. Explicit scratch-copy
   #print axioms checks cover all five delivered declarations, including both private
   helpers; both private helpers use only propext, Classical.choice and Quot.sound; the three
   public theorems additionally use sorryAx, as expected from the listed open
   transport and existing imported obligations. The chosen
   open localizations come from proved localization constructions; the unproved
   transport's existential witnesses are eliminated only inside a proposition proof.
   Verdict: pass; the explicit probes compiled cleanly.

3. Read the projection-formula paragraph of
   [Stacks 0E4G](https://stacks.math.columbia.edu/tag/0E4G), the lifting statement
   [09IM](https://stacks.math.columbia.edu/tag/09IM), and the generator criterion
   [09IS](https://stacks.math.columbia.edu/tag/09IS), together with the actual Lean
   signatures of supported_perfect_generator, exists_perfect_supported_map_lift,
   exists_perfect_annihilator and the tensor construction. For transport take
   R=Lf*I tensor P and j=(Lf*i tensor id) followed by the unit comparison.
   Perfect-I projection compatibility takes Rf*j followed by the transpose of beta
   to hkill; source-naturality and preservation of zero by the adjunction give
   j beta=0. Restriction of j is invertible because i restricts invertibly. This
   requires no support condition on Q, no perfectness of P, and no compactness of V.
   For V empty choose R=0 and j=0; for V total the statement forces beta=0 and
   j can be the identity; beta=0 and P=0 also satisfy the conclusion directly.
   Thus the hole is true and strictly intermediate: it neither detects support,
   proves perfect pushforward, nor constructs the annihilator.

   Searched independently with msearch LeanFinder for tensor annihilators of
   transposed maps, Loogle for schemeDerivedDirectImage (identifier unavailable
   in that search service, not a negative match), and grep for annihilator/adjunction
   and perfect/restriction/zero combinations. Repository searches also led to
   RightAdjointTensorComparisonProjection and ProjectionFormulaLocality: the former
   requires Noetherian schemes, one Hom universe, and a supplied monoidal pullback
   adjunction; the latter only detects isomorphisms of a supplied map. Neither
   proves this obligation under its actual hypotheses. No duplicate transport or
   global-perfect-map open detector was found. The existing private perfect_shift
   helpers in PerfectTwoOutOfThree and ProperFlatRightAdjointDirectSums confirm
   the elementary reindexing argument; importing their larger proof packages is
   unnecessary. No short proof of the remaining transport was available from the
   present derived interfaces. Verdict: pass as a decomposition, net zero holes.

4. Checked the parent top-down: the detector reduces support to restricted perfect
   tests; properFlat_derivedDirectImage_perfect plus hF supplies the perfect domain
   for case (i) of annihilation, so unbounded Q causes no boundedness gap; transport
   and cancellation of the restricted isomorphism finish the argument. In the
   detector, T=univ makes all support-complement conditions vacuous, every shifted
   generator is perfect by reindexing, and the lifted map vanishes by htest.
   Naturality of mapDerivedCategoryCompIso identifies the two restriction models;
   exact homology restriction and restrictStalkNatIso give the stated stalks.
   The proof imports supply these steps and no visible import was removed.
   The unit sk-thm-picard-duality has realized.statement=[] and realized.steps=[[]];
   no recorded unit realization was bypassed. Completed the report's accounting
   of all removed original direct proof dependencies, including the still-imported
   direct-image definition. Verdict: pass; no global pruning claimed.

5. Read all three node files and compared their signatures with Lean. The parent
   proof_deps are precisely the detector, localization, perfect pushforward,
   annihilation and transport used in its proof. The detector records localization,
   restriction QCoh, supported generation, map lifting and perfect-implies-QCoh.
   The transport records the projection, QCoh and restriction inputs its remaining
   construction needs; their currently narrower Lean interfaces are explicitly
   acknowledged, rather than silently substituted for the mathematical inputs.
   New nodes have source, proof steps, searches, provenance, blueprint ancestry,
   chapter/unit and matching verbatim lean.statement records. Verdict: pass.

Second-reading changes: report only. Completed the old-dependency pruning accounting
and added this independent reading. No Lean proof, signature, node or import required
repair. The delivery remains one original hole closed, one strictly intermediate
hole added, with the additional detector and both private helpers proved.
