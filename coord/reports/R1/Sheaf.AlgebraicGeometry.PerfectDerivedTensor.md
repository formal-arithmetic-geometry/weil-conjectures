## What changed

The signature and visibility of AlgebraicGeometry.perfect_derivedTensor are unchanged.
Its proof now obtains common local models using the already proved
AlgebraicGeometry.Scheme.perfect_common_affine_models, proves their total tensor strictly
perfect in the private helper strictlyPerfect_totalTensor, and applies the fixed-open
comparison AlgebraicGeometry.strictPerfect_tensor_localComparison.

The strictly-perfect tensor calculation is complete Lean: the bounds are [a+c,b+d];
the finite set of degree-n summands is indexed by p+q=n with a<=p<=b; tensoring the
finite-free retractions and assembling their biproduct gives a retraction to a finite
free sheaf. The free basis is the dependent sum of the finite product bases, reindexed
by a universe-lifted finite ordinal. mapBifunctorDesc removes every omitted zero summand.
This includes empty intervals, empty opens, zero complexes and rank-zero free targets.

Added the new module Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison, containing
one public theorem left sorry, together with proved local instance declarations needed to
elaborate the tensor totalizations on the localized site. These instances use the existing
sheaf tensor and colimits, not a new tensor construction. The new theorem's docstring gives
its sources, complete proof in words and edge cases. Local explicit totalization instances
avoid typeclass timeouts without changing a definition or any existing public interface.

Updated the original node's proof, proof_deps and proof_origin and added the comparison node.
No target, statement, public import of the existing module, or definition was changed.
No other existing module was adapted. Both files compile locally with the prescribed
lcompile.py; the delivery dry run performs the final compilation and preflight.

## Proved and sorry left

Closed the one original hole in AlgebraicGeometry.perfect_derivedTensor
(lem-sc-perfect-derived-tensor-perfect). Its body has a complete Lean proof from the common
local model theorem, the directly proved private tensor calculation, and the comparison.
The item module has no sorry left; strictlyPerfect_totalTensor is proved without sorry.

Added exactly one hole: AlgebraicGeometry.strictPerfect_tensor_localComparison in
Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison
(lem-sc-strict-perfect-tensor-local-comparison). Its proof is exactly := by sorry.
It states an isomorphism for prescribed representatives on a fixed open, not perfectness,
a covering, or existence of local models. It does not prove the finite-free retraction
conclusion; that conclusion is proved separately and combined with the comparison in the
item's proof. This is a decomposition: one upper hole closed, one lower hole added,
net zero holes removed. There is no claim that the original theorem is now axiom-free.
No other holes were added.

## No longer needed

Removed the proof imports Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat,
Sheaf.Algebra.Homology.KFlat and Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
from the item. KFlat remains available through the unchanged public statement imports;
its definition def-pc-kflat-complex is still part of the statement. The bounded-flat
K-flat result lem-pc-bounded-above-flat-kflat remains needed inside the comparison node's
argument, rather than being an independently applied step of the upper proof.

The item no longer needs lem-pc-affine-derived-pullback-tensor-tilde or its module
Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde: the comparison is about restriction
and prescribed K-flat models only. It uses the smaller restriction and K-flat-comparison
APIs; affine quasi-coherent equivalences, module tilde models, affine pullback, and affine
ring tensor computations are not used. No removal from the entire target closure is
asserted: other consumers may still need the old affine module.

The common-neighbourhood selection and restriction-of-strictly-perfect-model arguments
are reused from lem-pc-perfect-common-affine-models, not split into further nodes.
No unit statement or realized unit step is bypassed; the unit record has empty realized
statement and step lists for this supporting lemma.

## Where the brief, the DAG or earlier work was wrong

The old docstring said no derived tensor bifunctor exists. DerivedTensorStructure and
KFlatDerivedTensorComparison now provide one, so that sentence was corrected while keeping
the representative-based theorem signature identical.

The planned AffineDerivedPullbackTensorTilde restriction theorem lands in modules on
U.toScheme after the over equivalence, whereas IsPerfect uses modules on the localized
site over U. It cannot be applied directly to the existing signature. The new comparison
isolates that transport and the independence of prescribed K-flat models. The complete
remaining argument transports the given models through the exact over equivalence, uses
openRestriction_totalTensor_iso and openRestriction_isKFlat, applies the K-flat tensor
comparison on the open subscheme, and transports the result back. There is no affine or
quasi-coherence hypothesis to infer or add.

The local literature/stacks-project/cohomology.tex snapshot is absent on this machine.
I read the primary online sources: https://stacks.math.columbia.edu/tag/09J5,
https://stacks.math.columbia.edu/tag/08C4, https://stacks.math.columbia.edu/tag/06YH,
and https://stacks.math.columbia.edu/tag/08DX. The local-model proof implements the existing
DAG route for Tag 09J5; the current online proof of that result instead cites the
pseudo-coherence and Tor-amplitude criteria. The finite-free-retraction argument is a
complete elementary proof of the local closure step, not an unproved replacement route.

## New nodes

lem-sc-strict-perfect-tensor-local-comparison records the fixed-open comparison of
Q(Tot(P tensor N)) with Q(Tot(A tensor B)) for the given global K-flat representatives
and prescribed local strictly perfect models. It belongs to the original chapter and unit
and derives from steps 1 and 2 of lem-sc-perfect-derived-tensor-perfect. It is strictly a
part of that argument: it neither chooses the neighbourhood nor proves the output strictly
perfect. Its Lean module and declaration, source, proof steps, dependency union, four
Mathlib searches (LeanSearch unavailable; LeanFinder, Loogle and grep completed), blueprint provenance, edge cases and creation metadata are recorded.
There are no change records, because no existing interface was changed.

## Second reading by R1

1. I compared both delivered modules with the repository. The existing
`AlgebraicGeometry.perfect_derivedTensor` theorem signature is byte-for-byte unchanged;
no target statement or existing public definition changed. The new comparison theorem is
an explicitly recorded split node with a strictly smaller conclusion.

2. I compiled the two modules with `lcompile.py --all`; both compile cleanly. The item has
no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or long lines. The
axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for the proved
helper; the item theorem and the named comparison theorem report `sorryAx` through the comparison
hole.

3. I checked the finite-free proof term and the new theorem against their declarations.
The tensor helper handles degree bounds by zero summands, constructs finite biproduct
retractions from the two strictly perfect retractions, and reindexes the finite dependent
sum by `ULift (Fin n)`; empty intervals, zero complexes, and rank-zero targets therefore
remain covered. The comparison theorem has exactly the prescribed K-flat representatives,
strictly perfect local models, and two representing isomorphisms, and concludes only the
localized tensor isomorphism. Its docstring gives the source and a complete proof plan;
the node and Lean statement agree.

4. I checked pruning and the DAG route. The item removes only proof-only imports that its
new proof does not use, records those removals in the report, and retains the public
statement imports. The updated proof dependencies match the common-affine-model and local
comparison route; the unit has no realized statement or step to bypass. Searches found no
existing declaration duplicating the new comparison.

5. I checked the report and node metadata, including the split node's source, proof steps,
proof dependencies, blueprint provenance, creation record, and `lean` record. The report
records one original hole closed and one strictly simpler comparison hole added (net zero),
with no hollow definition or changed interface.

I changed only this second-reading report section; no Lean source, node, or proof was
altered during review.
