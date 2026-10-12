## What changed

Proved `AlgebraicGeometry.affineEtaleSiteBaseChange` without changing its statement
or any existing definition. Added the proved private helper
`AlgebraicGeometry.affineEtaleBaseChange_cover_pullback_continuous` in the same module.
It establishes covering preservation by cartesian point lifting, pullback preservation
by the full affine inclusions, and continuity by the pretopology sheaf criterion.
The main theorem obtains the adjunction directly, transports finite-limit preservation
through the existing inverse-image restriction comparison and the large-set restriction
equivalences, and obtains finite-colimit preservation from the adjunction.

Added proof imports of `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionUnit` and
`Sheaf.AlgebraicGeometry.AffineEtaleRestrictionLargeSets`. Retained the proof import
of `Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact`. Updated the existing node's
proof, proof dependencies, proof origin, and list of realized Lean declarations.
All public imports and existing declaration signatures remain unchanged.

## Proved and sorry left

Closed the one remaining sorry: `AlgebraicGeometry.affineEtaleSiteBaseChange`, node
`lem-weil-pbc-affine-etale-site-base-change`. The added helper is fully proved, and the
already proved `Scheme.affineEtaleBaseChange_isAffine` remains proved.
There are no sorries left in the delivered module and no new sorries or nodes.

The proof intentionally uses existing declarations whose own proofs remain open,
notably `etaleSetInverseImage_exact` and `fullAffineEtale_large_sets_equivalence`.
This is a reduction to existing stated dependencies, not a claim that the target's
whole transitive axiom closure is already sorry-free.

Single-file compilation passed without warnings. Edge cases: the finite covering
proof uses the original Fin n index set, including n=0; no point can exist on the
empty covered object. No affineness assumption on the base scheme is introduced,
and no terminal object of its affine subsite is assumed. The restriction comparison
uses Type (u+1), matching the theorem exactly. The item is not a realization of a
unit statement or step in sk-thm-iff, and its unit route is preserved.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; full-site continuity is
already available through the retained dependencies. That module remains a transitive
dependency, so this does not claim to prune it globally.

Removed `pqf-def-affine-morphism`, `def-weil-pbc-sites-and-cohomology`, and
`lem-weil-pbc-etale-base-change-continuous` from the direct proof dependency list:
the first two remain statement dependencies, and full-site continuity is used by the
existing restriction comparison rather than invoked directly here. No corresponding
module is claimed globally unreachable. Retained the covering-base-change node,
realized directly with Mathlib's cartesian point-lifting and etale stability lemmas.
No other original proof dependency is pruned; the affine-topos dependency is retained
for the public setup and inclusion continuity.

## Where the brief, the DAG or earlier work was wrong

The original planned transport needs the affine restriction equivalence for
Type (u+1), whereas the original fullAffineEtale_sets_equivalence declaration is
only for Type u. The already existing large-set equivalence supplies precisely the
needed universe; no statement correction was necessary.

The finite precoverage's realization as a Pretopology does not automatically give
Precoverage.IsStableUnderBaseChange: that class requires stability under arbitrary
isomorphic choices of indexed pullbacks, a stronger condition. The proof instead
uses the pretopology sheaf criterion directly, avoiding that unsupported instance.

The literature TeX files named by the existing node are absent from this read-only
checkout. This delivery introduces no new source claims or unproved lemmas; it follows
the recorded proof and the checked signatures of existing library declarations.

## Second reading by Y2

1. Compared the entire delivered module with the repository version and checked the
   declaration table: all three existing declaration statements are byte-identical.
   The definition `Scheme.affineEtaleBaseChange` and the previously proved
   `Scheme.affineEtaleBaseChange_isAffine` have identical bodies. Only proof imports,
   a proved private helper, and the remaining theorem proof change. No change record is needed.
2. Single-file local compilation passed without errors or warnings. A scratch copy
   with `#print axioms` for all four declarations shows only `propext`,
   `Classical.choice`, and `Quot.sound` for the definition, its affineness theorem,
   and `affineEtaleBaseChange_cover_pullback_continuous`. The main theorem also uses
   `sorryAx` through existing open dependencies; it is a checked reduction, not a
   sorry-free transitive proof. There is no sorry or forbidden declaration in the
   delivered module, and no hollow definition.
3. No statements were split off and no holes were added. Read the proved helper:
   its point lifting uses the cartesian square of the actual base-changed arrow,
   preserving the original finite index set and therefore the empty covering.
   Pullback preservation uses affineness of all three objects of the cospan, never
   affineness of the base. Identity base change and empty schemes satisfy the same
   argument. Independently searched Mathlib with msearch grep for affine base change
   and the pairwise-pullback sheaf criterion, and searched both library roots with
   rg. The generic lemmas used by the helper exist; no existing full-affine-site
   base-change theorem was found to replace it.
4. Read the restriction-unit and large-set-equivalence declarations and the full-site
   exactness statement. They use Type (u + 1), exactly as the target requires.
   The comparison identifies full inverse image followed by target restriction
   with source restriction followed by affine inverse image; precomposition by
   the inverse source equivalence and its counit gives the claimed finite-limit
   preservation. Finite colimits follow directly from the constructed adjunction.
   The proof imports are needed for these applications; public imports occur in
   existing signatures. The removed direct UpperLowerStar.Defs import is redundant.
   The report lists all three old proof dependencies omitted from the new list.
   Checked sk-thm-iff.json: this node realizes neither its statement nor its step;
   the unit's realized route is unchanged.
5. Compared the node files: only lean, proof, proof_deps, and proof_origin change.
   Read each new proof step against the Lean proof. Their uses union equals
   proof_deps, including the actual restriction comparison and large-set equivalence;
   the private helper is described in the proof steps, while the public declarations
   realizing this existing node retain their original list.
   No new node or statement-only dependency is introduced.

Verdict: pass. Made the implementation helper private to avoid adding an unneeded
public statement in the item module, and removed it from the node's public declaration
list. Its proof and the existing declarations are unchanged. Added this report of
the independent second reading. The delivery closes
`AlgebraicGeometry.affineEtaleSiteBaseChange` and adds zero holes.
