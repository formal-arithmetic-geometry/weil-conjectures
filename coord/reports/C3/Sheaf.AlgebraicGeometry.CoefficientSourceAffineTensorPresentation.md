## What changed

Replaced the proof of
AlgebraicGeometry.Scheme.Modules.exists_coefficientSource_affine_tensor_presentation
by the direct standard-pullback affine-chart argument. The statement is unchanged.
The chart morphism is hB.fromSpec, and its composite with g and S.toSpecΓ is
Spec.map (g.appLE top B). Pullback composition and the open-restriction comparison
identify the source chart sections with spectral pullback sections. The proved
source tensor equivalence supplies the spectral presentation. The two pullback-unit
composition equations and the explicit restriction-sections formula establish the
coefficientGenerator equation.

The proof imports WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde and
WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine privately. Proved private
helpers expose the section equivalences with native section types, handle the
spectral generator formula and the restriction-unit formula, identify
coefficientGenerator with successive global units, combine two pullback-unit composition equations for arbitrary morphisms, and
construct the chart isomorphism with its unit equation before specialization. The DAG
proof, proof_deps and proof_origin now describe this route. Elaboration options are scoped to individual declarations. No definitions or public
signatures were changed, and no other existing module was adapted.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.Scheme.Modules.exists_coefficientSource_affine_tensor_presentation
(lem-pc-coefficient-source-affine-tensor-presentation). No holes were added, and no
sorry remains in the delivered module. The source declarations used for the tensor,
restriction and unit calculations are proved. Empty affine opens, zero rings and
zero modules are handled by these general equivalences; no nonemptiness, affineness
of S or S', or finiteness condition was added.

## No longer needed

Removed the proof import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections and
the dependency lem-weil-pbc-module-pullback-affine-sections. This proof needs neither
its tensorPullback comparison nor its chosen tensorPullback adjunction unit. Its
ModulePullbackAffineSectionsBijective (lem-weil-pbc-module-pullback-affine-sections-bijective)
and ModulePullbackAffineChartUnit (lem-weil-pbc-module-pullback-affine-chart-unit)
branch is not needed by this item. These modules can still have other users; no claim is made
that they are globally unreachable. The affine tilde-Gamma and open-immersion
restriction ingredients remain needed, and the standard-unit spectral base-change
and composition-unit ingredients are now explicit in the node. Also unused is lem-weil-pbc-tilde-pullback-base-change and its module
Sheaf.AlgebraicGeometry.TensorPullbackTilde: its recorded theorem concerns
tensorPullback, whereas this proof directly uses the proved standard-pullback
source implementation. No unit statement or realized unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The former affine-sections dependency describes tensorPullback with a chosen
adjunction unit, whereas this item uses the standard pullback and its fixed unit.
The proved source spectral formula is a shorter route and avoids comparing these
adjunctions. The earlier attempt left exploratory local holes and repeatedly
unfolded concrete equivalences while cancelling inverses. The revised proof uses
abstract section equivalences with their proved formulas, checks the
restriction-unit identity for an arbitrary module, and constructs the chart
isomorphism and its unit compatibility for arbitrary morphisms before specialization.
The entire delivered module, including all helper proofs, compiles together within
the unchanged single-file time limit, with no warnings. No separate module or
compiler-limit bypass was used. The
compiler's shared-slot queue can add waiting time before its single-file limit
starts; that waiting is not a Lean timeout.

## Second reading by C3

1. PASS: compared the complete module with the repository version. The only
   existing declaration is exists_coefficientSource_affine_tensor_presentation;
   its signature is byte for byte unchanged. There is no changed definition,
   added hypothesis, change record or forced adaptation. The added helpers are
   private proved theorems; public imports are unchanged.
2. PASS: compiled the complete delivered module with lcompile.py without errors
   or warnings. No sorry or forbidden declaration appears in it. The scratch
   #print axioms check of the public theorem and the delivery tool's probe check
   the proof's transitive axiom dependencies. The equivalences obtained by obtain
   are supplied by fully proved constructions, not arbitrary unproved witnesses.
3. PASS: no new split-off statements, nodes or holes. Read all seven private
   helpers: they construct tensor/section equivalences, compose two unit
   equations, and identify ordinary restriction with the open-immersion unit.
   They introduce no nonemptiness or finiteness assumptions. Empty B, zero rings
   and zero N are allowed by the general linear equivalences and presheaf laws.
4. PASS: read PullbackTilde's tildePullbackΓEquiv and one-tensor proof,
   PullbackUnit's open-immersion and composition-unit proofs, and
   LocallyFreeAffine's explicit sectionsRestrictFromSpecLinearEquiv. These are
   the direct proved source route; local searches found no ready-made arbitrary
   affine-open coefficient presentation. Both private imports are used. The old
   proof_deps difference consists precisely of the affine-sections node reported
   above. The coherence unit has realized.statement = [] and realized.steps =
   [[]]; this node is a below-unit affine calculation and bypasses no realized
   unit step.
5. PASS after repair: the node's three steps match the chart comparison, the
   restriction and composite-unit calculation, and spectral tensor inversion.
   Its statement and lean.statement are unchanged. Removed the unused
   lem-weil-pbc-tilde-pullback-base-change from uses/proof_deps: its recorded Lean
   declaration uses tensorPullback and is not applied here. Step 3 now explicitly
   records direct use of the proved standard-pullback source implementation and
   its tilde-adjunction construction. No new node fields require review.

Second reading changed only the DAG dependency description and this report;
no Lean changes were needed. Closed one original hole and added zero holes.
