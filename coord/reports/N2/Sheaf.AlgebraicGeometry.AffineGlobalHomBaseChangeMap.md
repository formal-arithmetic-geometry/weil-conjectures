## What changed

Completed `AlgebraicGeometry.exists_globalHomPullbackComparison` in
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`. Its statement, all existing
signatures, definitions, visibility and public imports are unchanged. Two proof-only
imports provide the normalized internal-Hom mate and the scalar-compatible
sections/pushforward comparison. The proof fixes the original canonical adjunctions,
constructs the restricted-global-sections composite explicitly, and assembles every
required equation. Existing proofs of scalar-extension and tensor-Hom adjunctions
are retained.

The sandbox held an earlier, incomplete attempt. Repaired its final assembly:
partial application had already inferred the module-derived-category instance,
so supplying that instance again misapplied the next argument. Explicitly staged
application now supplies exactly the two canonical tensor-Hom predicates.

Completed both helper modules. In `NormalizedInternalHomPullbackComparison`, the
proved private categorical evaluation-mate calculation establishes naturality in
both internal-Hom inputs. The existing `exists_schemeHomTensorPullbackIso` supplies
the canonical tensor isomorphism; no second construction of that isomorphism is
introduced. In `AffineSectionsPushforwardNormalization`, the pullback condition
identifies the ring actions, and Mathlib scalar-restriction comparison isomorphisms
construct the identity on sections. Existing direct-image global-sections
acyclicity, exact restriction, and uniqueness of right-derived functors construct
the derived comparison. The right-derived natural-transformation factorization
identity proves its precise unit equation on every homotopy complex.

Updated the item's node proof, proof dependencies and proof origin. Added one node
for each proved helper, including exact Lean signatures and recorded searches.
No change record or forced adaptation is needed: no existing interface changes.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.exists_globalHomPullbackComparison`
(node `def-pc-affine-global-hom-base-change-map`). There are no sorries left in
that module and no holes added anywhere in this delivery.

Both new public helper theorems are proved:
`AlgebraicGeometry.exists_normalizedInternalHomPullbackComparison`
(node `lem-pc-normalized-internal-hom-pullback-comparison`) and
`AlgebraicGeometry.exists_affineSectionsPushforwardNormalization`
(node `lem-pc-affine-sections-pushforward-normalization`). Their private helpers
`evaluationMate_exists`, `exactComp_unit_isIso`, and
`composite_isRightDerived_of_acyclic` are also proved. This closes one original
hole, adds zero holes, and splits off zero unproved statements. These proofs use
existing project declarations; this does not claim that their entire transitive
import closure is sorry-free.

All three modules compiled together through lcompile.py, individually within the
60-second file limit. The delivery dry run also checks the axiom probe and static
preflight. Edge-case review: the sections construction needs only equality of
ring-map composites, and works for empty schemes, identity maps and arbitrary
nonflat base-ring maps. The derived construction uses acyclicity, not a false
claim that direct image preserves K-injectives. The mate argument is generic for
all internal-Hom inputs, including zero objects. No extra perfectness, flatness,
Tor independence, boundedness or quasi-coherence assumption is introduced.

## No longer needed

Second reading removed the redundant direct public import of
`Sheaf.AlgebraicGeometry.DerivedPullback` from the new
`NormalizedInternalHomPullbackComparison` helper; its declarations are already
available through `CanonicalPullbackTensorComparison`. This removes no module
from the targets' import closure. No original item import was removed, and no
module is claimed pruned from the targets'
import closure. The two new imports are used only in proofs. Every original
proof-only import remains needed by the already proved scalar-extension
adjunction. The completed comparison does not directly use the larger arbitrary
adjunction package in `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction`
(node `lem-pc-derived-internal-hom-pullback-adjunction`), the abelian-group-valued
`Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`
(node `lem-pc-derived-sections-pushforward-comparison`), or
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
(node `lem-pc-ringed-spaces-derived-direct-image-composition`). Their normalized
construction steps are realized by the two proved helpers instead. These are
alternative direct proof dependencies, not claims that the three modules become
globally unreachable. The unit's statement and proof route are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had no node files or report and did not compile its
final assembly. Its sections helper still contained a whole-theorem sorry. Those
issues are repaired. The larger internal-Hom package chooses adjunction data
existentially and does not pin it to this item's canonical adjunctions; it cannot
be used by merely destructuring its witnesses. The abelian-group sections theorem
also does not retain the affine R-module action or specify this unit equation.
The new helpers resolve these exact interface gaps and are both proved.

The repository includes citation records but not the Stacks TeX source files on
this machine. Read the official Stacks pages for Tags 08I3, 0D5T and 0AA7 to check
the evaluation, composition and affine-adjunction construction against the source.
LeanSearch was unavailable (Internal Server Error), recorded as unavailable;
LeanFinder and Mathlib source searches supplied the other search evidence.

## New nodes

`lem-pc-normalized-internal-hom-pullback-comparison`, in
`dag/nodes/sec-picard-framework/`, records the fixed-adjunction evaluation mate in
`Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison`. Its natural
transformation and tensor isomorphism satisfy the exact canonical predicate and
mate equation used by the item. The generic mate calculation is fully proved;
the tensor isomorphism comes from the existing proved construction in
`GlobalHomAdjunctionIso`. No global sections or affine-base inputs occur here.

`lem-pc-affine-sections-pushforward-normalization`, in the same node directory,
records `Sheaf.AlgebraicGeometry.AffineSectionsPushforwardNormalization`. It
isolates the scalar-action identity and the derived-unit-compatible Leray
comparison without any internal-Hom inputs. It is fully proved from Mathlib
scalar restriction, project global-sections acyclicity, and the right-derived
universal property. There are no change records.

## Second reading by N2

1. **Existing interface: PASS.** Read the complete three delivered modules and
   compared the item with the repository using `diff -u`. The differences are
   two plain proof imports, scoped linter/heartbeat options, and the body of
   `exists_globalHomPullbackComparison`. Every existing signature, definition
   body, visibility, public import and docstring is byte-for-byte unchanged.
   In particular, the qcqs, perfectness, quasi-coherence and derived-category
   hypotheses remain, and all canonical-adjunction and comparison equations
   remain. The relevant landed canonical tensor-Hom model and proof-context
   change records require no further adaptation here.

2. **Proof and axioms: PASS.** Independently compiled the three original sandbox
   files in import order (32.4, 23.1 and 49.5 seconds, no warnings). After pruning
   the redundant helper import, compiled both helpers again (25.2 and 25.0
   seconds). Searched all delivered Lean sources: no sorry, axiom, unsafe,
   opaque, implemented_by or extern occurs. A scratch import module printed
   axioms for the item's public definitions and existence theorems and both
   new public theorems. Only propext, Classical.choice, Quot.sound and existing
   upstream sorryAx occur. In particular,
   `exists_affineSectionsPushforwardNormalization` and
   `exists_affineDerivedExtension` use only the three allowed axioms.
   `exists_globalHomPullbackComparison` and the normalized internal-Hom helper
   retain sorryAx through their imported open constructions. This delivery
   closes one local hole and adds zero; it does not certify the whole closure.

3. **New statements: PASS.** No unproved statement is split off. The two new
   proved statements isolate different strict parts of the argument. Read
   [Stacks 08I3](https://stacks.math.columbia.edu/tag/08I3): transpose evaluation
   after the inverse tensor comparison, exactly as the mate equation requires.
   The generic `evaluationMate_exists` proves contravariant naturality in K
   and covariant naturality in L from hS.1 and hT.1, then uses adjunction
   naturality and cancellation. It works for zero objects and identities.
   Read [Stacks 0D5T](https://stacks.math.columbia.edu/tag/0D5T) and
   [Stacks 0AA7](https://stacks.math.columbia.edu/tag/0AA7): the latter's opening
   construction restricts global Hom scalars and takes the extension adjoint.
   Tor independence is needed for the later isomorphism assertion, not for
   this construction. In the sections helper, he follows from appTop
   functoriality, cancellation of GammaSpec_B and pullback.condition; s is
   literally identity on elements. Exact scalar restriction and the cited
   direct-image acyclicity theorem justify the two invertible unit factors.
   Right-derived uniqueness constructs c and its factorization identities
   prove the equation for every J. Empty X, identity g and nonflat ring maps
   do not invalidate these steps. No arbitrary data is extracted from a
   new unproved existence theorem.

   Independently searched with LeanFinder queries “naturality of transposed
   evaluation under a tensor preserving functor” and “right derived composite
   functor when first functor sends injectives to acyclic objects”, and rg
   searches in lean/Sheaf, the upstream checkout and Mathlib. Mathlib's
   expComparison requires Cartesian closed categories and its chosen ihom;
   it does not supply this arbitrary normalized tensor-right Hom family.
   The upstream rightDerivedFunctorCompIso requires preservation of
   K-injectivity, stronger than the available acyclicity. The analogous
   generic acyclicity helper in RingedSpaceDerivedDirectImageComposition is
   private. No existing public exact replacement for either new statement
   was found. GlobalHomPullbackComparison uses other chosen adjunctions and
   does not provide this item's fixed-adjunction natural-transformation and
   affine unit-normalization equations.

4. **Route and pruning: PASS.** Checked GlobalHomAdjunctionIso's proved
   exists_schemeHomTensorPullbackIso: it supplies precisely t and its
   canonical predicate. Checked the statement of
   isIso_directImage_globalSections_unit_on_kInjective: it supplies acyclicity
   of direct image for subsequent sections, not preservation of K-injectivity.
   These are the two substantive imported inputs of the new proofs. The
   item's old proof_deps consist of canonical tensor-Hom and mixed tensor
   K-flat quasi-isomorphism; both remain used by its retained proofs. None
   was dropped. Checked dag/units/sk-thm-picard-duality.json: its realized
   lists are empty and this item does not realize a unit-level step. The
   evaluation, scalar sections, derived composition and extension-adjunction
   route is kept. The three larger alternative packages named above were
   already absent from the original proof_deps; no global pruning is claimed.

5. **Nodes: PASS.** Compared the item's node with its repository version:
   only proof, proof_deps and proof_origin differ. For each of all three
   nodes, proof_deps is exactly the union of proof-step uses. Matched both
   new Lean statements to their node statements, including the direction
   of t.inv, both Hom transposes, the scalar restrictions and the equation
   for every homotopy complex. The new nodes have source, docstring proofs,
   search records (including honest unavailable LeanSearch results), created,
   blueprint ancestry, chapter/unit and complete Lean records. Neither
   restates the full item. The proof-only dependency imports remain plain.

**Changes by the second reader:** removed one redundant direct helper import
and clarified its pruning status in this report. Retained the mathematical
proofs and all node records. An attempted removal of the sections helper's
Limits import hit the 60-second timeout under concurrent machine load; restored
that import, and the restored helper compiled in 25.2 seconds. Removed the
scratch axiom module from the delivery set.
