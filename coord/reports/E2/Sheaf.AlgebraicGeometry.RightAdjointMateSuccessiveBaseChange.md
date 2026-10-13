## What changed

Reduced AlgebraicGeometry.rightAdjoint_mate_successive_baseChange to the geometric
rectangle comparison in RectangleInverseBaseChangeMateTransport, with its original
statement unchanged. The main Lean proof applies Mathlib mateEquiv_vcomp, evaluates
at K, rewrites both square mates, includes the equality in the ambient derived
category, and composes with the rectangle comparison. The middle comparison is the
identity. The source comparison is an explicit construction from the canonical
pullback composition family and hk₁.

Added QCohInverseBaseChangeMate: canonical QCoh pullback/direct-image lifts,
naturality of ordinary base change, its inverse square, and the fully proved
AlgebraicGeometry.dualityEquationBaseChangeMap_eq_inverseSquareMate. The latter
uses a proved private generic secondMate_formula, inverse uniqueness, and Mathlib's
iterated_mateEquiv_conjugateEquiv. No second mate is assumed invertible.

The remaining geometric comparison has no aS, adjS, O, or H: it identifies the
rectangle with the mate of the pasted inverse ordinary square. It therefore leaves
the geometric comparison/pasting step, while the categorical second-mate
factorization and fixed-formula identification are completed here.

## Proved and sorry left

Closed the item's one hole:
AlgebraicGeometry.rightAdjoint_mate_successive_baseChange
(lem-sc-right-adjoint-mate-successive-base-change).

Proved without sorry:
AlgebraicGeometry.dualityEquationBaseChangeMap_eq_inverseSquareMate
(lem-sc-duality-base-change-inverse-square-mate), including the generic private
secondMate_formula. All new definitions contain real data, and their proofs are
complete. successiveBaseChangeSourceIso selects the canonical comparison fixed by
its left-derived universal property, rather than arbitrary existence data.

Added one hole:
AlgebraicGeometry.rectangle_inverseBaseChange_mate_transport
(lem-sc-rectangle-inverse-base-change-mate-transport). This is the only sorry in the
delivered Lean files. Thus the original hole is reduced, not fully discharged:
one hole closed, one added, net zero before any pruning. The remaining statement
omits the middle right adjoint and all square second mates, and the proof combining
it with the proved single-square formula is complete Lean.

## No longer needed

Removed the item's direct proof imports of
Sheaf.AlgebraicGeometry.DerivedBaseChangePasting and
Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition. They remain in
the geometric comparison module because its proof plan still needs them; this is
not a claim that either module leaves the target closure. Replaced those imports
with Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport. No old
statement-dependency import was removed. No module or node is claimed pruned.

For completeness, all six old direct proof_deps have been replaced at the item's
node: def-pc-derived-base-change-map,
def-sc-duality-equation-base-change-map, lem-cat-right-adjoint-composition,
lem-pc-derived-base-change-pasting,
lem-pc-ringed-spaces-derived-direct-image-composition, and
lem-pc-ringed-spaces-derived-pullback-composition. They remain reachable through
the new helper nodes or the unchanged statement imports; none is claimed removed
from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or interface was found. The second reader corrected the
new helper's source reference: equation-base-change-map is Stacks Tag 0AA6,
Equation the project server; Tag 0AA8 is Lemma 48.6.2, a different result. The existing
DualityEquationBaseChangeMap docstring has the same stale tag, but its definition
is unchanged and that module is outside this delivery. The existing upper-left ordinary
pasting lemma alone does not supply the horizontal two-square identity with all
QCoh and right-adjoint comparisons. That geometric step remains explicitly stated.
Mathlib already proves the categorical second-mate composition, once the fixed
map is identified with the mate of the inverse ordinary square. The new proof
uses this shorter categorical route instead of manually expanding and cancelling
all three second mates. The unit record sk-thm-picard-duality has no realized step
that this route bypasses.

Checked edge cases: the new inverse-square characterization is categorical and
uses no nonzero-object or nonempty-scheme assumption; identity and empty schemes
are included. The rectangle comparison uses only pullback universal properties,
canonical functor comparisons and the supplied ordinary invertibility hypotheses.
No flatness, properness, or invertibility of second mates was introduced.

## New nodes

lem-sc-duality-base-change-inverse-square-mate records the proved identification
of the fixed map and the inverse-square mate, and the explicit QCoh constructions
in its module. Its proof is complete.

lem-sc-rectangle-inverse-base-change-mate-transport records the remaining geometric
comparison without any middle right adjoint, with explicit source comparison.
The declaration's docstring and node describe the ordinary-pasting and
right-adjoint-uniqueness argument still to formalize.

The item's node proof and proof_deps now follow the compiled argument. No existing
signature or visibility was changed, and no forced adaptations or change records
were needed. Mathlib searches were run through msearch.py and recorded in
searches.jsonl; blueprint search found no matching blueprint statement.

## Second reading by E2

1. Interface: compared the item's complete module against the repository with
   diff. The entire declaration signature, including all scheme instances, the
   four right adjoints and their adjunctions, three ordinary-invertibility
   hypotheses, K, k, both projection equations, and the three-isomorphism
   conclusion is byte for byte unchanged. Only its proof, local elaboration
   options, and private proof imports changed. Both other modules are new.
   There are no forced adaptations or statement/definition change records.
2. Proof and data: read all three modules. The categorical helper uses inverse
   uniqueness and iterated_mateEquiv_conjugateEquiv; the item uses
   mateEquiv_vcomp, the two proved fixed-formula identifications, inclusion, and
   the geometric transport. No second mate is inverted. qcBaseChange supplies
   naturality by Hom-equivalence naturality; qcInverseBaseChange constructs the
   inverse from the supplied component IsIso proofs. The source isomorphism is
   a composite of the pinned derived pullback comparisons and equality transport,
   not an arbitrary object selected from mere existence. The comparisons' homs
   are specified by the left-derived lift equation in
   exists_derivedPullbackComposition. The only local sorry is the named public
   rectangle_inverseBaseChange_mate_transport, with a source and proof docstring.
   No forbidden declaration or hollow definition occurs. All three delivered
   modules compiled locally. An independent scratch module importing all three
   compiled cleanly and printed the axioms of every public declaration:
   qcPullback and successiveBaseChangeSourceIso use only propext,
   Classical.choice and Quot.sound; the other six public declarations use only
   these plus sorryAx from the open imported library statements and the named
   geometric hole. No additional axiom occurs. In particular the source
   comparison itself is completely discharged, including its dependencies.
3. Split: the rectangle theorem retains all three ordinary-invertibility
   premises, the endpoint adjunctions and both projection equations, but removes
   the middle adjoint and the square second mates. Its conclusion identifies
   the rectangle with the single mate of the pasted inverse ordinary square,
   using a fixed source comparison. This is a genuine geometric part of the
   argument, with the categorical factorization separately proved. Identity
   morphisms reduce to comparison unit laws; zero objects and empty schemes
   require no additional hypothesis. Right-adjoint uniqueness gives the target
   comparison even for differently chosen endpoint adjunctions. Checked the
   source 0ATR's conjugate-composite argument, its ordinary-pasting reference
   0ATM (Remark 20.28.5), and 0AA6's
   displayed unit/inverse-conjugate/counit formula. Searches with different
   wording (Beck-Chevalley inverse transformations and pasted pullback squares)
   via leanfinder, loogle and grep found generic mate composition already used,
   not this geometric derived-QCoh transport. Repository/source searches also
   found a private baseChange_naturality in ProperFlatRightAdjointBaseChangeHbeta;
   it is inaccessible, so the short direct naturality proof here is justified.
4. Route and pruning: checked the Mathlib identities and the original dependency
   statements. DerivedBaseChangePasting alone is upper-left pasting with an
   inserted unit, not the needed two-square rectangle transport; closing the
   remaining geometric lemma is not a few-minute application. The new route
   handles the categorical step first and isolates geometry. Public imports are
   needed by the public signatures; the remaining private geometric imports
   supply the stated proof plan for the open lemma. The unit
   sk-thm-picard-duality has realized.statement = [] and realized.steps = [[]];
   no realized step is bypassed. No module is pruned from the closure.
5. Metadata: read all three nodes and compared their Lean statement records.
   The item's proof and its two proof_deps describe the actual reduction; the
   helper nodes record the categorical identification and geometric transport,
   with the required source, creation, searches, blueprint ancestry, chapter,
   unit and Lean records. The geometric docstring's ordinary-pasting,
   comparison and mate-transport steps agree with its node's proof plan.

Second reading corrected the new QCoh helper module and node's source citation
from Tag 0AA8 to Tag 0AA6, completed the report's old proof_deps list, and
recorded the independent review. No Lean proof or signature needed repair. The delivery is a decomposition (one original
hole closed and one new hole added), not a completed geometric proof.
