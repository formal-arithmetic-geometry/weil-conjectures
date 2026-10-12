## What changed

Proved `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_forward`
without changing its signature or visibility. Added the proof-only import
`Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus`. Five proved private helpers
handle isomorphisms, tensor nonvanishing, the component of a homogeneous product,
positive powers, and scalar multiples after restriction. The main proof uses
`t^d` as numerator for `s^e`, transports its degree using commutativity, and applies
the assumed fraction formula. Updated the node's proof route and dependencies.

Read Stacks Constructions Lemma 01N8 (`lemma-converse-construction`, chart quotient
construction and inverse-image calculation) and Properties Lemma 01PZ
(`lemma-map-into-proj`, clause (1)) in the locally available Stacks source mirror.
The unit `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and has
no realized proof steps; this local proof preserves that route.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_forward`
(node `lem-sc-ample-proj-canonical-map-preimage-forward`).
No `sorry` remains in the delivered module; no holes were added or split off.
Every private helper is proved. This is a proof, not a decomposition.
The imported section-ring infrastructure still has its existing unproved ring
laws; those holes were neither changed nor duplicated in this delivery.

Local compilation passed without warnings. The edge cases are covered: the
power helper allows degree zero, requires a positive exponent, handles exponent
one explicitly, and uses no reducedness of the scheme. On an empty scheme there
is no point argument. The scalar-multiple helper works for an arbitrary module
and does not assume that the scalar is a unit.

## No longer needed

None. No original imports or planned dependency nodes were removed. The proof
needs the section-ring construction and invertibility as in the existing plan.
No claim is made that any module has left the targets' import closure.
The tensor-power/nonvanishing machinery in `NonvanishingCommonDegree` and
`AmplePullbackIdealAffineSection` was inspected but is not imported; its private
helpers address different representations and are unnecessary for this proof.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The previous DAG described fibre calculations but
listed only definition dependencies. The Lean proof instead uses the existing
proved nonvanishing/local-generation bridge and generating-locus API to establish
the power calculation explicitly; those dependencies are now recorded. The
scalar step follows directly from the maximal-ideal submodule definition and
germ compatibility, without constructing a residue-field fibre.

Lean Finder, Loogle, and grep searches ran through `msearch.py`; no exact
section-ring power/nonvanishing theorem was found. Loogle returned
`DirectSum.of_mul_of`, which is used in the component helper. Existing library
proofs suggested the local-generator tensor calculation. No new nodes or
interface adaptations were needed.

## Second reading by N1

1. Interface: PASS. Compared the complete delivered Lean module and node against
   the repository with `diff`. The existing theorem's signature is byte-for-byte
   identical, including universe, invertibility, the formula for every exponent,
   pointwise positive-degree witness, positive degree of s, and the implication.
   No definition or public visibility changed. The only new import is plain
   `import Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus`, for proofs.
   The other additions are five proved private theorems; no change record is needed.
2. Proof: PASS with existing dependency holes. Compiled the delivered file cleanly
   through lcompile.py (2.5 seconds). A scratch copy printed axioms for all six
   theorems. The isomorphism, tensor and scalar-multiple helpers use only propext,
   Classical.choice and Quot.sound. The product-component and power helpers and
   main theorem also use sorryAx through the existing section-ring ring laws.
   There is no sorry in this module and no new axiom, unsafe/opaque declaration,
   extern/implemented_by attribute, kernel-check bypass or hollow definition.
   Thus one local hole is closed; the target import closure still has older holes.
3. Split statements and small cases: PASS. There are no split-off statements or
   new public declarations. Read every private helper: isomorphism transport uses
   restriction naturality and inverse cancellation; tensor nonvanishing uses
   simultaneous free generators and D(a*b)=D(a) intersect D(b); multiplication
   extracts the actual single-component representatives via DirectSum.of_mul_of.
   Positive-power induction treats exponent one separately and excludes exponent
   zero, which would make the assertion false for a vanishing section. Degree
   zero is allowed in this helper. The germ argument requires only scalar closure
   of the maximal-ideal submodule, with no unit assumption. Empty schemes have no
   point argument; nilpotents cause no problem. The main proof uses hd for t^d
   and he for s^e, and transports d*e=e*d in the required direction.
4. Route and pruning: PASS. Read Stacks Constructions lemma-converse-construction
   (01N8), its chart fraction maps and inverse-image calculation, and Properties
   lemma-map-into-proj (01PZ), clause (1) and its proof, in the local source mirror
   /home/ubuntu/weil-launcher/maint/bp/work/literature/stacks-project/.
   Independently searched lean/ with nonvanishing/power/tensor/iso and inspected
   GeneratingLocus, FreeGenerator, ZeroLocus, TensorSection and InvertibleSectionRing.
   No shorter public theorem for section-ring powers was found; similar helpers
   in AmpleIso and AmplePullbackIdealAffineSection are private. Reusing the proved
   nonvanishing/local-generation bridge avoids a new fibre infrastructure hole.
   All original imports are needed by the unchanged statement; the added import
   supplies the proved bridge and generating-locus API. Both old proof_deps remain
   used, so No longer needed is complete. The unit sk-thm-curveestimate realizes
   thm-sc-proper-cohomology as its statement and has no realized steps; neither
   the unit nor its route changes.
5. DAG: PASS. The node's statement, statement dependencies and Lean statement
   stay identical. Read the three replacement proof steps against the actual
   helper calls and main proof. Their dependency union equals proof_deps exactly:
   invertibility, section-ring construction, the nonvanishing/local-generation
   bridge, generating-locus API, and the nonvanishing definition from Ample.
   proof_origin correctly marks this explicit Lean calculation as agent-written
   from the cited literature. No new nodes require checking.

Second reading changed only this report, adding the independent review and exact
axiom findings. No mathematical or Lean repair was necessary. Holes closed: only
AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_forward. Holes
added: none; split off: none; pruned: none.
