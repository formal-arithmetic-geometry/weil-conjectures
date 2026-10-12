## What changed

Proved `AlgebraicGeometry.Etale.gabber_principal_vanishing_ideal` with its signature
unchanged. The ideal has precisely the stated zero-restriction carrier. Zero membership
uses the zero sheaf on the empty etale site. Closure under arbitrary left multiplication
uses cohomology pullback functoriality and cancellation of the coefficient composition
isomorphism. Addition restricts to D(fh+gh), transports the class to the ambient restriction
of F, and applies the given degree-one kernel condition to fh and gh. For q>1 it uses the
proved principal two-open joint-kernel lemma with the induction hypothesis at
(fh)(gh)(fh+gh). No change to a definition or existing statement was required.

Added `Sheaf.AlgebraicGeometry.PrincipalOpenCohomologyJointKernel`, containing the proved
`AlgebraicGeometry.Etale.principalOpenCohomology_joint_kernel`. This makes explicit the
relative-open isomorphisms, coefficient composition comparison, and intersection
cohomology transport needed to use the existing
`etale_mayerVietoris_connecting_pullback` exact segment. Its remaining private exactness helper is proved.
The edge cases include n=0, the zero ring, an empty sum open, zero summands, opposite
summands, and repeated members of the cover: neither proof imposes any exclusions.

The two modules compile locally through lcompile.py, with no warnings. The delivery dry
run additionally checks the local declaration probe and preflight; server compilation
is disabled by default in deliver3.py, and the global build verifies the landing.
Sources were read at https://stacks.math.columbia.edu/tag/0GY0 (the local literature
source is absent on this machine). The original node and the new node record the actual
Lean proof dependencies. The fixed sk-thm-p1 unit statement and route are preserved.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.gabber_principal_vanishing_ideal`
(node `lem-weil-pbc-gabber-principal-vanishing-ideal`).

Also proved the new helper:
`AlgebraicGeometry.Etale.principalOpenCohomology_joint_kernel`
(node `lem-weil-pbc-principal-open-cohomology-joint-kernel`).

No sorry remains in either delivered module. No holes were added or split off. This
is a proof from existing named library results, rather than a decomposition with new
holes. The proof still depends on the existing Mayer--Vietoris infrastructure and any
holes reachable there; no claim of axiom-free target closure is made.

## No longer needed

Removed the duplicate private `cohomologyMap_eq_zero_of_comp` declaration from the
new joint-kernel module; no node or import was attached to that private helper.

Removed the original proof-only import `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`:
its derived-functor comparison isomorphisms are not needed. The proof instead uses the
actual Sheaf.H pullback maps and exact segment in
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback`, through the new proved
joint-kernel module. Accordingly, `lem-weil-pbc-etale-mayer-vietoris` is no longer a
direct proof dependency of the item's node. This reports pruning of this proof edge;
it does not assert that another target or another dependency cannot still use that node.

Removed the redundant original proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its composition definitions
remain accessible through the statement import TopologicalInvariance. The
`lem-weil-pbc-inverse-image-composition` node remains needed. Retained both original
public imports because the existing statement uses them. Retained
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` because the proof uses its
composition identity. No other original proof dependency is unused.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned landing check: the two delivered modules repeated the same
private `cohomologyMap_eq_zero_of_comp` theorem. Removed that declaration from
`Sheaf.AlgebraicGeometry.PrincipalOpenCohomologyJointKernel`. Its two relative-open
restriction proofs now apply the existing `cohomologyPullbackFunctorial` declaration
and cancel the coefficient composition isomorphism directly. Importing the main
module instead would create a cycle, and its helper is private. The helper in the
main module remains the sole declaration of that statement. No signature, public
import, or mathematical dependency changed. The previous second reading predates
this repair and has been removed for the next reader to replace.

No statement dispute. The original planned Mayer--Vietoris module supplies arbitrary
comparison isomorphisms to derived global sections, so its signature alone does not
identify its maps with the actual Ext-defined pullbacks used in this theorem.
The existing connecting-pullback theorem supplies exactly those maps and the required
exactness. It was usable without changing its statement.

Directly rewriting fh+gh to (f+g)h under homOfLE creates dependent-type difficulties.
The proof instead restricts along the inclusion furnished by that equality; proof
irrelevance makes the resulting inclusion into D(h) the original one.

## New nodes

`lem-weil-pbc-principal-open-cohomology-joint-kernel` states the zero joint-kernel
consequence of the Mayer--Vietoris exact segment for D(a+b), assuming only that the
preceding-degree group on D(ab(a+b)) is subsingleton. It is strictly a part of the
original argument and is fully proved. Its module is
`Sheaf.AlgebraicGeometry.PrincipalOpenCohomologyJointKernel`. The node records the
existing connecting-pullback, functoriality, composition, and isomorphism-invariance
results actually used, and all three required search kinds. No change records.

## Second reading by J1

1. Compared the existing module with the repository using diff, and compared the
   complete original theorem signature byte for byte: unchanged. Both original
   public imports remain. No definition or existing statement changed; no change
   record is needed. The new module adds a fully proved intermediate theorem.
2. Read both proofs in full. Both modules compiled through lcompile.py without
   warnings. The source scan found no sorry, axiom, unsafe, opaque, implemented_by,
   extern, hollow definition, or arbitrary witness construction. Explicit scratch
   copies with #print axioms check the two public theorems; the delivery probe
   additionally checks every constant. Existing dependency holes remain allowed.
3. No statements were left split off with sorry. The new joint-kernel theorem is
   strictly the higher-degree addition step, with the needed preceding-degree
   intersection hypothesis. Its docstring and node give the argument and source.
   Checked n=0, a=0, b=0, a=-b, a=b, h=0, and the zero ring: the cover and exactness
   proof works without any nonemptiness or distinctness assumption. Independent
   LeanFinder, Loogle and grep searches using overlap/preceding-degree/injectivity
   terminology found no existing theorem with this signature. The upstream
   cohomologyMap_eq_zero_of_fac and composite-zero equivalence are degree-one
   only; the private general-degree proof is therefore needed.
4. The original theorem constructs the literal zero-restriction ideal. Zero and
   multiplication use existing library results; addition first handles q=1 with
   hfg and then uses the existing actual-pullback Mayer--Vietoris exact segment.
   Read the old Mayer--Vietoris statement: its arbitrary comparison isomorphisms
   do not identify its derived maps with these pullback maps. The new helper
   performs the required identifications. All imports serve a statement or an
   explicit proof use. No longer needed lists the complete removed original
   proof edge and both removed imports. Read sk-thm-p1.json and its realized
   steps: this below-unit specialization changes none of that route.
5. Compared the node records with Lean. The original node changes only proof,
   proof_deps and proof_origin. The new node signature matches Lean verbatim;
   its source, complete proof steps, origin, searches, creation, blueprint,
   chapter, unit and lean record are present. Both proof_deps lists equal the
   union of the corresponding proof-step uses and name the results actually
   used. The new theorem is proved rather than an added hole or restatement.

Explicit #print axioms results for both public theorems: propext, Classical.choice,
Quot.sound, and sorryAx from existing open dependencies; no additional axiom.

Verdict: pass. Changed no
Lean proof, signature, import or node: the duplicate-helper repair is correct.
Added this independent second-reading record and fresh search evidence only.
