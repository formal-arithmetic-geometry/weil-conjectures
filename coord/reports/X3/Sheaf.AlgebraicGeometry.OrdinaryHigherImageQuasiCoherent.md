## What changed

Proved `AlgebraicGeometry.ordinaryHigherImage_isQuasicoherent` by applying the existing
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage` from
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`. Register the given
quasi-coherence and the existing Grothendieck abelian structure on X.Modules locally;
the latter supplies injective resolutions. The conclusion is definitionally the same
ordinary right-derived module direct image. Existing signatures, definitions, public
imports and public elaboration context are unchanged.

The second reader replaced the submitted affine-base induction proof with this shorter
route, removed both private helpers, and removed the proposed conditional union module
and its new node. Only Sections is added as a proof-only import. The existing node's
proof, proof_deps, proof_origin and obsolete Lean note now describe this route.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ordinaryHigherImage_isQuasicoherent`
(node `lem-pc-ordinary-higher-image-quasi-coherent`).

No holes remain in the delivered module; no holes or new declarations are added elsewhere.
Zero split-off statements are delivered. The first submission closed one hole and added
one gluing hole, a decomposition; this second reading removes that proposed hole.

This is not an unconditional sorry-free proof: the existing Sections theorem relies on
`AlgebraicGeometry.Scheme.Modules.higherDirectImage_section_clearDenominators` and
`AlgebraicGeometry.Scheme.Modules.higherDirectImage_section_pow_annihilates`, both already
open in the repository, with nodes `lem-pc-higher-direct-image-section-denominators` and
`lem-pc-higher-direct-image-section-torsion`. Their statements separate lifting and the
kernel criterion for localization. Neither is introduced or changed by this delivery.
A scratch copy with #print axioms for both the delivered and reused theorem compiled;
each lists only propext, Classical.choice, Quot.sound and sorryAx. The delivered file
compiles without warnings. Whole-closure progress and actual unreachable modules are
for the pinned-baseline sorry ledger; no unsupported whole-library count is claimed.

## No longer needed

Removed every old direct proof import:

- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension`
- `Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction`
- `Sheaf.Paper.HigherDirectImagePresheaf`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`

All eight old proof_deps are no longer direct dependencies of this node:

- `lem-pc-restrict-derived-direct-image-open`
- `lem-sc-invert-s-cohomology-induction`
- `lem-pc-affine-morphism-hi`
- `lem-weil-pbc-higher-direct-image-presheaf`
- `lem-pc-affine-vanishing`
- `lem-sc-mayer-vietoris-open-cover`
- `lem-weil-pbc-module-presheaf-sheafification-exact`
- `lem-pc-quasi-coherent-extension`

The sole replacement dependency is the existing
`lem-pc-sections-higher-direct-image-quasi-coherent`. Some removed direct imports remain
reachable transitively through Sections or elsewhere; this is not a claim of their
removal from the target closure. The proposed OrdinaryHigherImageQuasiCoherentUnion
module and node were removed from the sandbox delivery, not from the repository.

## Where the brief, the DAG or earlier work was wrong

The old node's Lean note claimed that Sections cannot be imported because it reaches
TruncatedHigherImageQuasiCoherent. Its current imports no longer do so. In fact the first
worker already successfully imported Sections for open restriction, but overlooked its
existing quasi-coherence theorem as the shortest route. That theorem now uses two
localization criteria and the affine-cover criterion, without importing this item or
its proposed union lemma. The proposed gluing theorem is mathematically valid but is
unnecessary for this delivery. No change record or forced adaptation is required.

The existing theorem docstring records the original Mayer--Vietoris plan; it is preserved
as existing documentation. The revised DAG and this report record the actual shorter
proof through the already available localization theorem. The unit record
`dag/units/sk-thm-picard-duality.json` has no realized statement or step node here; the
item is a lower auxiliary node. Its Serre-duality statement and route are unchanged.
The reused theorem's unit `sk-thm-picard-coherence` is also unchanged.

## Second reading by X3

1. PASS. Compared every submitted module with the repository. The existing public
   theorem's signature is byte-for-byte unchanged, before and after my repair. No
   definition, target, public import or other existing declaration is altered.
2. PASS. Both original submitted modules compiled, as did the repaired single module.
   Scanned the delivered Lean for sorry, axiom, unsafe, opaque, implemented_by and extern:
   none occur. No data is chosen from an unproved existence assertion. Scratch #print
   axioms gives only the three allowed axioms and sorryAx from existing open dependencies.
3. PASS after pruning. Read the proposed union theorem and its full proof docstring;
   checked empty, equal and nested opens, degree zero and successor degrees, and zero
   coefficients via the relative Mayer--Vietoris kernel/cokernel sequence. LeanFinder
   search for a long exact sequence of derived pushforwards on two open subschemes
   returned site Mayer--Vietoris results, not this module statement. A source grep using
   union and quasi-coherence found no such union theorem. More decisively, source reading
   found the existing quasi-coherence theorem in Sections. Removed the unnecessary
   split-off statement and node; the final delivery has none to review.
4. PASS after repair. Use the shortest available library theorem instead of duplicating
   its result through an additional hole. Read the reused theorem's affine-cover proof
   and the two localization statements it applies. Their docstrings explicitly avoid
   the quasi-coherence-dependent affine sections comparison. The import graph is acyclic.
   Removed all seven old direct proof imports and listed all eight retired dependency
   nodes above. Kept all public imports and both units' statements, steps and realized
   records unchanged; no realized unit step is bypassed.
5. PASS after repair. Existing node statement and statement dependencies are unchanged;
   proof steps, their union proof_deps, proof_origin and Lean note now agree with the
   final three-line proof. No new nodes, modules, change records or adaptations remain.

Changed: replaced the induction proof with existing higher-image quasi-coherence,
removed two private helpers and the proposed one-hole union module/node, pruned seven
old direct proof imports, corrected DAG proof metadata and this report. The signature
and existing docstring remain unchanged.
