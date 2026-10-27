# Stage-1 report: lem-sfb-flat-space-groupoid-kernels-cokernels

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-space-groupoid-kernels-cokernels.json: item, statement unchanged, six proof steps, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-ringed-topos-pullback-exact.json: statement-only generic lemma (Stacks 04JC), unsplit, no Mathlib match.
- citations.json: verbatim statement excerpts for all proof-step citations.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, equivariant quasi-coherent/groupoid terminology and flat ringed pullback; no declaration states the item. Ambient sheaf module abelianity does not identify the category of groupoid modules.

## WANTED

None. The proof uses the local Stacks source. No SGA source is used.

## Corrections and route

The imported item was statement-only and has not been changed. The source is spaces-groupoids.tex Tag 06VZ (lemma-abelian), with the module cocycle and identity equations in definition-groupoid-module immediately above. Its compressed proof leaves the cocycle and universal-property verifications to the reader. I wrote these out, including why the identity section need not be flat. The new 04JC node does not restate a clause about groupoids: it is exactness of scalar-extended geometric inverse image between arbitrary ringed topoi. Its future proof can use exact geometric inverse image (the existing lem-trf-geometric-inverse-image-exact), flat tensor and reflection through scalar restriction; that argument is not put into its statement.

Read the fixed chapter record, the recorded unit, and the newest blueprint/latest unit and det-thm-sf-ctf-stability-direct-images proof (3). The existing ancestry records the alteration/moduli auxiliary branch used by the algebra-image argument; this split keeps that branch and proves the 06VZ prerequisite. The ancestor command returns null, as already recorded by the item; this null is preserved in the new node with the full via chain. The whole-blueprint searches for groupoid, flat pullback and 04JC give no blueprint duplicate. The DAG search also found lem-sfb-flat-space-groupoid-abelian, a near-duplicate statement of the item: it is unsplit and is not used as a substitute proof. The earlier scheme-groupoid module-limits-colimits node cannot cover an algebraic-space relation R. No existing node other than the assigned item was edited.

The generic off-unit tool lem-trf-space-chart-adjunction-tensor-realization is declared in split_report.tool_uses: it provides ordinary tensor-composition formulas, with no change of proof route. All other non-leaf inputs are in the recorded unit.

## Review by Q101

I read spaces-groupoids.tex 06VZ and the preceding definition and isomorphism lemma; spaces-properties.tex 03M1 for quasi-coherent closure; spaces-morphisms.tex 073C for the geometric/site flatness equivalence and 03MN/03MO for flat composition/base change; sites-modules.tex 04JC for the one new node. I also read the statements of every cited node, not merely their proofs or sources.

Step 1 uses the ambient module category abelianity exactly as stated by lem-pur-ringed-site-module-category-abelian, on the small etale site in the size convention. The closure node says both that kernels/cokernels are quasi-coherent and that small direct sums are quasi-coherent, so the zero and biproduct construction stays inside the category. Equivariance of sums follows from the tensor formula, and the displayed inverse equation proves reflection of isomorphisms directly.

Step 2 uses the kernel/cokernel clause of lem-sfb-space-qcoh-kernels-colimits, the precise if-and-only-if in lem-sfb-space-flat-etale-ringed-comparison, and the new exact flat ringed-topos lemma. In each use the source and target are algebraic spaces, their ringed topoi are the specified small-etale ones, and the hypothesis is chartwise flatness; no finite presentation is introduced. The two arrow diagrams commute by the definition of an equivariant map. The kernel and cokernel universal properties give the descent maps and their inverse maps. Thus this step does not infer exactness from a definition of flatness alone.

Step 3 takes the actual ordinary tensor-composition isomorphism and its formula from lem-trf-space-chart-adjunction-tensor-realization. The threefold formula proves the coherence used here; the unit formula proves the identity identifications. Pulling back the descent-map equations by e needs no exactness: e*s*j=j and e*t*q=q under the identity composites. Cancelling j and q therefore proves the identity laws even when e is not flat.

Step 4 uses the flat base-change and composition assertion of lem-sfb-stack-chartwise-smooth-etale-calculus, for representable maps of algebraic spaces. Both projections of P are base changes of the flat s,t. Hence sc=sp1 and tc=tp0 are flat, so step 2 applies to these composites. The four displayed equations give the cocycle checks explicitly; cancellation occurs after the monic (sc)*j and epic (tc)*q. It does not presume that c or e is flat and does not pull a monomorphism back by an arbitrary map.

Step 5 uses only the universal properties already established in step 2 and the equations from steps 3-4. I checked both directions: maps into K are tested after s*j; maps out of Q are tested before t*q. The resulting uniqueness is uniqueness of module morphisms, so it also proves uniqueness in the equivariant category.

Step 6 reuses ambient module-sheaf abelianity for the coimage/image comparison and the definition def-sp-abelian for the precise conclusion. The comparison is built from equivariant universal factorizations, its inverse is equivariant by step 1, and the monic/epic cases give normal monos/epis. It uses no unquoted criterion theorem. Every citation has its verbatim excerpt in citations.json. All non-elementary steps are below 2000 characters; no hidden sublemma is concealed in a long step.

For the new node I checked 04JC's actual hypotheses: arbitrary geometric morphism on small presented topoi, commutative rings, and flat target structure ring over inverse-image ring. The assertion does not require a continuous functor between the presenting sites. Mathlib searches (both natural-language phrasings, Loogle and grep) are recorded from searches.jsonl. I inspected SheafOfModules.pullback at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53 and its adjunction at :60, the ambient abelian instance in Sheaf/Abelian.lean:40, and ModuleCat.preservesFiniteLimits_extendScalars_of_flat in ModuleCat/Descent.lean:42. They respectively construct pullback, give ambient abelianity, and prove ordinary-ring scalar exactness; none states arbitrary flat ringed-topos exactness. I inspected the existing lem-trf-geometric-inverse-image-exact: it supplies exact inverse image before any structural-ring extension and hence is not a duplicate of the new node.

Small cases: empty U and the zero module give the zero category and zero descent maps; the identity groupoid reduces to ordinary quasi-coherent kernels/cokernels; an arbitrary flat groupoid over an affine scheme recovers the same tensor-kernel construction. For the new 04JC input the identity geometric morphism reduces to flat scalar extension, while the identity coefficient map reduces to exact geometric inverse image. Flatness cannot be dropped: tensoring Z -> Z by multiplication by 2 with Z/2 destroys injectivity. No Noetherian, separation, quasi-compactness or finite-presentation assumption was used. The only repair while drafting was to make the cocycle cancellation take place after flat composite maps, instead of assuming exact pullback along the identity section.

## Not duplicates

lem-sfb-flat-ringed-topos-pullback-exact vs def-sfb-proetale-ring-derived-inverse-image: the existing node defines a specific scheme/coefficient inverse-image construction or diagram target; the new node is a theorem of exactness for arbitrary flat ringed-topos morphisms.

lem-sfb-flat-ringed-topos-pullback-exact vs def-weil-pbc-etale-coefficient-injective-target: the existing node defines a specific scheme/coefficient inverse-image construction or diagram target; the new node is a theorem of exactness for arbitrary flat ringed-topos morphisms.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-pur-coefficient-pullback-exact: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-pur-proetale-constant-module-pullback-homology: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-sf-comparison-pullback-exact: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-sf-etale-tor-flat-pullback-model: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-sp-level-pullback-exact: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-trf-geometric-inverse-image-exact: the existing node proves geometric inverse image with scalars f^{-1}B; the new node extends scalars further along an arbitrary flat f^{-1}B -> A.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-cohomology-module-square-compatibility: the existing statement concerns specified etale scheme diagrams, their injective constructions, or inverse-image compatibility; it does not assert arbitrary scalar-extended flat ringed-topos module exactness.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-etale-coefficient-injective-cokernel-system: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-etale-coefficient-injective-system: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-etale-coefficient-injective-system-data: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-etale-coefficient-injective-system-embedding: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-etale-replacement-stage-diagram: the existing statement concerns specified etale scheme diagrams, their injective constructions, or inverse-image compatibility; it does not assert arbitrary scalar-extended flat ringed-topos module exactness.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-etale-system-cone-functor: the existing statement concerns specified etale scheme diagrams, their injective constructions, or inverse-image compatibility; it does not assert arbitrary scalar-extended flat ringed-topos module exactness.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-proetale-module-inverse-image-comparison: the existing result is scheme pro-etale inverse image to modules over the inverse-image ring; the new theorem applies to arbitrary presented ringed topoi and further flat scalar extension.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-proetale-module-inverse-image-scalar-graph: the existing result is scheme pro-etale inverse image to modules over the inverse-image ring; the new theorem applies to arbitrary presented ringed topoi and further flat scalar extension.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-ringed-site-cech-refinement-square-abelian-exists: the existing node concerns inverse image or diagrams of abelian sheaves, without flat structural-ring extension; the new node concerns the scalar-extended module pullback.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-site-pullback-abelian-exact: the existing node concerns inverse image or diagrams of abelian sheaves, without flat structural-ring extension; the new node concerns the scalar-extended module pullback.

lem-sfb-flat-ringed-topos-pullback-exact vs lem-weil-pbc-site-pullback-abelian-underlying: the existing node concerns inverse image or diagrams of abelian sheaves, without flat structural-ring extension; the new node concerns the scalar-extended module pullback.

lem-sfb-flat-ringed-topos-pullback-exact vs prop-weil-pbc-inverse-image-modules-exact: the existing statement concerns specified coefficient sheaves or their diagram constructions; the new theorem allows arbitrary commutative ring sheaves and a flat, possibly noninvertible structural ring map.

## Unfinished work

The single new node is intentionally unsplit, as required for a one-level stage-1 split. The item proof is complete. No Lean files were written and no compiler or build was run.
