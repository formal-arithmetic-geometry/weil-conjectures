## What changed

The original statement of `AlgebraicGeometry.Scheme.nonempty_additiveIdealImageTensorIso`
is unchanged. Its proof now constructs the isomorphism from a limiting ideal kernel fork,
Mathlib's `ShortComplex.Exact.isColimitImage`, transport of categorical cokernels along
an isomorphism, and `PreservesCokernel.iso`. Finally, `sheafificationIso` identifies the
sheafified construction with the specified quasi-coherent tensor-sections sheaf.

Added three modules: `Sheaf.AlgebraicGeometry.EtaleTensorSectionsMapNaturality`,
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsRightExact`, and
`Sheaf.AlgebraicGeometry.Curve.EtaleIdealKernelPresentation`. The middle module constructs
an actual functor on all scheme modules: tensor-pullback section maps, additive universe
lift, and sheafification. Identity, composition, additivity before sheafification,
preservation of zero morphisms, and the quasi-coherent object comparison are proved.
No arbitrary data is chosen from an unproved mere-existence theorem in these definitions. The naturality
proof required by the natural transformation is a separately named, now proved theorem.

The original module adds two proof-only imports: the kernel presentation and Mathlib's
abelian exactness module. Its node now follows the actual kernel/cokernel argument.
All four delivery modules compiled together with lcompile.py. The original theorem's
proof closes without any new hypothesis, signature change, private assumption, or local hole.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.nonempty_additiveIdealImageTensorIso`
(node `lem-sc-additive-ideal-image-tensor-comparison`). No sorry remains in the item module.

Added two strictly smaller open obligations. The additional naturality theorem is proved:

- `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsMap_naturality`
  (`lem-sc-etale-tensor-sections-map-naturality`): module-variable naturality of the
  specified restriction maps. Proved during second reading from adjunction-unit and
  composition-isomorphism naturality. No ideal, image, quotient, or sheafification occurs.
- `AlgebraicGeometry.Scheme.Modules.preservesCokernels_etaleTensorSectionsFunctor`
  (`lem-sc-etale-tensor-sections-right-exact`): right exactness of the constructed
  functor on arbitrary scheme modules. No ideal or subscheme restriction occurs.
- `AlgebraicGeometry.Scheme.exists_etaleIdealKernelPresentation`
  (`lem-sc-etale-ideal-kernel-presentation`): tensor ideals present the kernel of
  restriction for nested ideals. No cokernel or tensor sections of a quotient occurs,
  and quasi-coherence of the quotient is not assumed.

This is a decomposition: one original upper hole closed, two lower holes added; the net
progress of this delivery alone is -1, before the ledger measures its actual import closure.
The first draft added the naturality hole; the second reading closed it, so it is not a
hole added by the final delivery. The item has one of its one original holes closed,
conditionally on the two remaining geometric obligations.
The isomorphism witnessing the kernel presentation is eliminated only inside the theorem
proof; it is never chosen as data for a public definition.

## No longer needed

No original import, dependency node, module, or unit realization is bypassed or pruned.
The old proof dependencies `def-sc-etale-additive-structure-restriction`,
`def-sbc-ideal-sheaf-powers`, and `def-sc-etale-qcoherent-module` are all still used: the
first two define f and a, and the last identifies the quasi-coherent tensor sheaf.
The new naturality import is proof-only (`import`), rather than `public import`.
The original definition dependencies remain needed through the intermediate statements.
The old node's informal direct affine gluing argument is replaced by the explicit
kernel presentation and right-exactness obligations, not discarded.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies are definitions, not lemmas stating the affine kernel
identification or compatibility of tensor sections with cokernels. Thus they cannot by
themselves provide a direct Lean proof of the comparison. The new nodes expose these
missing steps and the module-variable naturality needed to construct the functor.

The local literature payload is absent: the paths named in the node's source do not exist
in this clone. The node and original declaration retain the affine argument in full.
For the general sheafified construction I read Stacks Tags 03DR, 03DU, 070S, and 03FH
online. Tag 070S, Lemma 35.8.5(2), identifies sheafified tensor sections on the small
etale site with the ringed-site pullback, supplying a separate source for right exactness.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. Loogle
found the generic preserved-cokernel comparison; LeanFinder found no specialized
comparison or module-variable restriction theorem. Grep found no existing versions.

Edge cases checked in the new statements: I=J gives an identity kernel fork and zero
cokernel; J=0 gives zero kernel of restriction on the ideal; I=0 forces J=0; the empty
scheme and the zero ring give zero section groups. General right exactness uses local
Zariski lifting of module-cokernel sections, not surjectivity of global sections on a
non-affine object. The functor is defined on all modules, and is sheafified before
right exactness is asserted. No square-zero or nilpotence hypothesis is introduced.

The already existing tensor-pullback adjunction of unit `sk-def-av-jacobian` is used as
a general tool, via the existing tensor-sections interface. The unit record `sk-prop-h2`
has no realized statement or step nodes affected by this reduction.

## New nodes

`lem-sc-etale-tensor-sections-map-naturality` states the naturality of componentwise
pullback maps in the module variable; its proof is the composition of the adjunction
unit, normalized composition-comparison, and equality-transport naturality squares.

`lem-sc-etale-tensor-sections-right-exact` constructs the sheafified, lifted tensor-section
functor and states preservation of parallel-pair colimits. Its remaining proof is local
right exactness on the etale site, equivalently the ringed-site pullback of Stacks 070S.

`lem-sc-etale-ideal-kernel-presentation` states the geometric kernel fork without any
module quotient. Its proof is the flat affine kernel calculation and compatibility of
ideal inclusions with restriction, followed by gluing.

No interface change record or forced adaptation is needed.

## Second reading by T2

1. Signature and visibility: compared the item module with the repository using diff.
   Its only changes are two private imports and the theorem proof; the full existing
   signature and docstring are byte-for-byte unchanged. The other three modules are new.
   No target, existing definition, or existing public import changes. Verdict: pass.
2. Proof and axioms: compiled all four modules in import order with lcompile.py.
   Read every definition and proof. The cokernel comparison uses a limiting kernel fork,
   Mathlib abelian exactness and image-cokernel universality, cokernel transport, preserved
   cokernels, and sheafificationIso, with all isomorphism directions checked. There are
   exactly two remaining sorries, both named theorems listed above; no axiom, unsafe,
   opaque, extern, implemented_by, or holed definition occurs. Explicit scratch-copy
   #print axioms checks passed for every public declaration in all four modules,
   alongside the delivery tool's full probe. The naturality theorem
   uses only propext, Classical.choice, and Quot.sound. Open geometric statements and
   constructions using their proof obligations may additionally depend on sorryAx.
   The chosen adjunction is normalized by its specified unit formula; its use determines
   the section maps. The kernel presentation witness is eliminated within a Prop proof,
   not chosen as definition data. Verdict: pass with the two declared open obligations.
3. New statements: the kernel fork is genuinely smaller than the original comparison:
   it asserts no image/cokernel comparison or quasi-coherence of a quotient. Checked on
   affine rings: flat B/A gives B tensor I = I_B, and ker(I_B to B/J_B) = J_B.
   I=J gives an identity kernel fork, J=0 gives a zero kernel, I=0 forces J=0,
   and empty schemes/zero rings give zero groups. For right exactness, checked arbitrary
   modules, zero maps and non-affine objects: sections lift locally on a Zariski cover,
   not necessarily globally; these covers are etale covers. Stacks 070S, Lemma 35.8.5(2),
   and 03FH(1) identify precisely this sheafified construction with ringed-site pullback.
   Additivity reduces coequalizers to cokernels of differences. Repeated searches with
   different wording through msearch.py LeanFinder, Loogle and grep, plus rg in both
   library roots: generic pullback adjunction/sheafification lemmas and affine ideal-kernel
   lemmas exist, but no exact specialized comparison. The unit/composition naturality
   laws do suffice for the new naturality theorem; supplied that proof. Verdict: pass.
4. Route and pruning: read the original dependencies and dag/units/sk-prop-h2.json.
   Its realized statement and step lists are empty; none is bypassed. All three original
   proof dependencies remain explicit in the final proof_deps, and none is pruned.
   The kernel/cokernel argument is a real reduction, not application of a renamed copy
   of the original assertion. Retained the original proof and its two imports.
   Made the naturality module a private import; the universe-lift import is necessary
   for zero-map and sheaf-compose instances (removing it fails compilation).
   Verdict: pass, decomposition rather than a completed geometric proof.
5. Nodes: checked statements against the corresponding Lean signatures, sources,
   created records, chapter/unit, source ancestry, proof steps and dependency unions.
   Updated the naturality proof to its actual two private helpers and the main node
   to explicitly retain the two definition dependencies used in a and f. Fixed doubled
   TeX backslashes in the three new nodes. The two remaining open nodes have complete
   proof docstrings and genuine constructions for the functor they use. Verdict: pass.

Changed during this reading: proved etaleTensorSectionsMap_naturality, privatized its
proof-only import, corrected right-exactness source citations and completed its
coequalizer proof sketch, repaired node dependency/proof records and TeX escaping,
and updated the hole accounting. No existing statement or definition changed.
