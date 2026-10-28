## What changed

Withdraw the false scalarExtension_image_basicOpen_isBasis declaration and its
module Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis. Its node is
retained with lean=null and a counterexample in the proof field.

Repair the sole consumer, Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart,
without changing its theorem statement or either public import. Mathlib's
mapAffineOpenCover supplies the affine image cover. The existing complete-chart
bijectivity theorem and the quasi-coherent affine-cover criterion imply that eta
is an isomorphism, so its sections map is bijective on W (indeed on every open).
Tensor pullback preserves quasi-coherence by the existing comparison theorem.

Add Sheaf.AlgebraicGeometry.ProjTwistQuasicoherent, stating the independent standard
fact that every concrete integer twisting sheaf is quasi-coherent. This geometric
step has a source and complete proof in words, but remains an explicit obligation.
It has no scalar-extension data or comparison morphism and is strictly a part of
the corrected argument, rather than a renamed basis or comparison assertion.

Validation uses lcompile.py --all, compiling the new module before the repaired
consumer, with both comfortably below 60 seconds. The parent statement was also
checked textually identical to the source. Final changed-module compiles were
3.4 s and 4.8 s, without warnings. The unchanged direct importer
Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence also compiled against the
sandbox overlay in 11.1 s; its temporary copy was removed before delivery.

## Proved and sorry left

Original holes: one, AlgebraicGeometry.Proj.scalarExtension_image_basicOpen_isBasis.
Proved: zero of one. The false hole is withdrawn, not counted as proved.

The replacement proof of
AlgebraicGeometry.Proj.scalarExtension_twistMap_basicOpen_bijective is complete
from named dependencies, with no sorry in that module. Its theorem was previously
proved using the false basis lemma; this is a proof repair, not an extra hole closed.

One hole added and left:
AlgebraicGeometry.Proj.isQuasicoherent_twist, node
lem-sfb-proj-twist-quasicoherent. This is an honest decomposition of the corrected
local-to-global argument, not a completed proof of quasi-coherence. The existing
holes in the imported complete-chart injectivity/surjectivity modules are unchanged.
The delivered Lean modules contain one sorry in total; the withdrawn item has zero.

## No longer needed

Withdrawn module and node attachment:
Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis,
lem-sfb-proj-scalar-extension-image-basic-open-basis. This is the only module pruned.
Its sole Lean and DAG parent is repaired in this delivery. The unit's realized
statement/step lists do not require this split; the unit route is preserved.

The consumer removes the false module's import and these unused proof imports:
Sheaf.RingTheory.HomogeneousLocalizationScalarExtension;
Sheaf.Algebra.Module.GradedLocalizationScalarExtension;
WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections;
WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis;
WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists;
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde;
WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions.
They are not used by the repaired parent proof itself. This does not withdraw
any of those modules or claim that they are unused by the complete-chart proofs
or by the planned proof of quasi-coherence. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned theorem is false. For R=k, S=k[t], A=k[x],
B=k[t][x], with k a field and deg(x)=1, all stated scalar-extension and graded-span
hypotheses hold. The image of a positive homogeneous c*x^n is either zero or a
unit times x^n. Its standard open is empty or all of Proj B=Spec k[t]. These opens
cannot refine the nonempty proper open D(t), hence are not a basis.

The old proof's finite-span step only finds an image element outside a given
prime; it gives no containment of its standard open in a prescribed neighborhood.
Tag 01N2 and Mathlib mapAffineOpenCover give the correct cover. Bijectivity on
sections of a cover alone does not detect sheaf isomorphisms; quasi-coherence and
affineness make the corrected application valid. Empty Proj and negative twists
are covered by the new lemma's stated proof and require no degree-one hypothesis.

The existing gradedModuleSheaf_exists theorem takes AddSubgroup-valued pieces,
whereas concrete twists admit any additive-subgroup-class presentation. Applying
it to the new obligation requires the identity graded-ring transport (or a direct
chart proof). That remaining implementation detail is recorded explicitly in the
new theorem's proof in words; no source signature was generalized in this packet.

A source-only DAG audit also encountered a pre-existing cycle, unchanged here:
lem-nagata-affine-proj-scalar-extension -> prop-nagata-relative-proj-functoriality ->
lemma-nagata-relative-proj-exists -> lem-nagata-proj-affine-restriction ->
lem-nagata-affine-proj-scalar-extension. None of the three newly introduced parent
proof dependencies has a path back to the parent. This packet does not edit those
unrelated Nagata nodes.

## New nodes

lem-sfb-proj-twist-quasicoherent: the concrete twist for one integer j is
quasi-coherent. Sources: Stacks constructions.tex, Tags 01MB, 01MN, and 01M7.
Its plan identifies the concrete homogeneous fractions with the associated sheaf
of the shifted graded ring. It is independent of scalar extension and does not
assume the false image-basis assertion. Three real Mathlib searches are recorded;
none finds the twist quasi-coherence theorem. The proof dependencies are existing
nodes for the associated graded-module sheaf, concrete twist fractions, and the
positive homogeneous standard-open basis.

The existing associated-sheaf, fraction, standard-open, tensor-pullback and
affine-cover criterion nodes are used as geometric tools from their original
units. They supply precisely the local construction and detection results needed
here; the current unit has no substitute, and none of its mandatory steps changes.
No tool_uses approval was written by this worker. The blueprint search for twisting
returned nine unrelated blueprint nodes and no assertion of this general concrete
Proj-twist quasi-coherence fact; the ancestor tool reports no named blueprint
ancestor for this supporting chain.

Change record: coord/changes/proj-scalar-extension-image-basis-withdrawal.md.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart": "6a4a61c8dc1d85092ef3afa593467224d54b32d9", "Sheaf.AlgebraicGeometry.ProjTwistQuasicoherent": "5607e36ad6dd343c2a2d74f15c75e55fb2365860"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence": {"hash": "693af4a4e71c412036c3f4e4840aa6bc158a41c9", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:39:58+0800", "transitive": 0, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
