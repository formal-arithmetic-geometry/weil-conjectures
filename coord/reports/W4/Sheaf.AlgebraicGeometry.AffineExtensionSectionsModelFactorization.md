## What changed

The original theorem `AlgebraicGeometry.exists_affineExtensionSections_model_factorization`
keeps its entire signature and is reduced to two independent model-unit calculations.
`AffineExtensionModelUnit` constructs the R-sections and extension comparisons and computes
only the extension unit. `AffinePullbackSectionsModelUnit` computes only the pullback unit
against the same fixed inverse sections comparison. Neither new theorem mentions c or hc.
The original module supplies the substantive combination: lift hc degreewise with `ext i`,
apply the derived extension Hom equivalence, use its unit formula and naturality, and use
naturality of the exact restriction comparison to localize the degreewise equation.
The original node now records this proof route; the extension helper node records its
complete implemented scalar-extension proof. No existing signature or definition changes.

Validation uses lcompile.py for all three modules and deliver3.py --no-push for the
final delivery, including the axiom/sorry probe and preflight. Nothing was pushed.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_affineExtensionSections_model_factorization`
(new-affine-extension-sections-model-factorization), by decomposition into the following
strictly smaller calculations. There are no remaining holes in the original module.

Also proved: `AlgebraicGeometry.exists_affineExtension_model_unit`
(new-affine-extension-model-unit). Its proof constructs the sections isomorphism from
`affineTildeDerivedSectionsUnit_isIso`, identifies the sections complex with M using
`tilde.isoTop`, proves scalar extension preserves K-flat quasi-isomorphisms using the
mixed tensor test, and uses the standard derived adjunction unit factorization. It then
transports that unit equation through exact restriction and uniqueness of left adjoints.
No direct hole remains in this new module.

Added hole:
- `AlgebraicGeometry.exists_affinePullbackSections_model_unit`
  (new-affine-pullback-sections-model-unit).

One original hole closed, one lower hole added: decomposition, not a net proof gain.
Both new statements are independent of arbitrary c and hc. The first has no pullback or
v,r; the second has no extension adjunction. The original theorem's degreewise-to-localized
argument genuinely combines them. For the zero complex all comparisons are between zero
objects; for identity g the equations reduce to the derived unit formulas. The construction
uses no boundedness or flatness hypothesis on g. Data is not chosen from arbitrary unproved
existence: the only new uses are existential eliminations inside a theorem proof.

## No longer needed

Removed direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`,
`Sheaf.AlgebraicGeometry.TensorPullbackTilde`, and
`Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso`.
AffineTildeDerivedSectionsUnitIsIso remains imported by the proved extension helper.
The three original proof imports are now present in the unfinished pullback helper,
matching its recorded proof plan. The other geometric content remains required there, so no global pruning
of these modules or their nodes is claimed. The original proof dependencies are redistributed:
lem-pc-affine-tilde-kflat, lem-weil-pbc-tilde-pullback-base-change,
new-affine-tilde-derived-sections-unit-isIso, and the normalized derived adjunction machinery
remain below the two helper nodes. The parent now directly uses only the two new nodes.
Pruned globally: none.

## Where the brief, the DAG or earlier work was wrong

The DAG's third step refers to nonempty_derivedPullbackAdjunction, which only provides an
adjunction and does not pin its unit. The normalized interface needed here is
exists_schemeDerivedAdjunction from def-pc-derived-base-change-map, already used by the
unchanged canonicalPullbackAdjunction. The pullback helper records that dependency.
The blueprint ancestor command returns None for this new node; the new nodes retain the
explicit lem-sc-finite-duality ancestry already recorded by the parent.
LeanSearch returned Internal Server Error; this is recorded as unavailable. LeanFinder,
Loogle and grep returned generic adjunction-unit and uniqueness tools, no exact affine result.
Source read: Stacks perfect.tex labels lemma-affine-compare-bounded (06Z0),
lemma-affine-K-flat (08DV), lemma-quasi-coherence-pullback (08DW), and
lemma-affine-morphism-and-hom-out-of-perfect (0AA7). The source TeX is absent from the
read-only checkout, so it was downloaded into the sandbox scratchpad for inspection.

## New nodes

new-affine-extension-model-unit, module Sheaf.AlgebraicGeometry.AffineExtensionModelUnit:
the fixed extension adjunction unit computed on a K-flat affine sections model, including
the canonical inverse sections comparison. This is the scalar-extension part of the
parent's second and third steps; its source and complete argument are in the docstring.

new-affine-pullback-sections-model-unit, module
Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit: the normalized pullback unit
computed after affine sections, using hr and a specified inverse R-sections comparison.
This is the pullback part of the parent's first through third steps. It does not use c,
hc, or the extension adjunction. Its source and complete argument are in the docstring.


## Second reading by W4

1. Compared the existing module with the read-only repository by diff and checked the
   theorem signature byte for byte: identical. Only its proof and plain proof imports
   change. The existing node changes only proof, proof_deps and proof_origin. There
   are no changed definitions, existing signatures, public imports or change records.
2. Read all three modules and compiled them in dependency order. The extension helper
   constructs its comparison using the affine sections theorem, the ordinary tilde
   unit, mixed-tensor quasi-isomorphisms, and uniqueness of left adjoints; the parent
   combines its equation with the pullback equation by degreewise hc and naturality.
   The only direct sorry is exists_affinePullbackSections_model_unit. No forbidden
   declaration or hollow definition occurs. Explicit scratch copies append #print
   axioms for all three declarations: the extension helper uses only propext,
   Classical.choice and Quot.sound; the parent and open pullback helper additionally
   use sorryAx, exactly as expected. The delivery tool also probes every declaration.
3. The remaining statement is true: tilde takes a K-flat module model to a K-flat
   sheaf model, and tensor pullback of that model is termwise tilde of extension.
   Thus the pullback counit and B-sections comparison are invertible. The normalized
   adjunction formula, naturality and hr give exactly its unit equation for the
   specified inverse sections comparison. This needs no flatness of g or boundedness.
   Zero complexes and zero rings give zero objects; identity g gives the ordinary
   normalized unit equation, including any compatible choice of v and r. It neither
   mentions c nor constructs an extension comparison, so it is a strict subargument,
   not a renamed parent. Its docstring supplies the construction and proof, and its
   node contains the source, ancestry, searches and matching verbatim Lean statement.
   Repeated LeanFinder with "affine scheme derived global sections tensor pullback
   unit compatibility K-flat associated sheaf complex", Loogle for derivedη_fac_app,
   and rg for affine unit and adjunction uniqueness. No existing exact result was
   found. AffineDerivedPullbackTensorTilde provides related model isomorphisms, but
   not this normalized unit compatibility, so applying it does not close the hole
   in a few minutes. Read the cited K-flat and affine pullback proofs in perfect.tex.
4. The parent uses the shortest available combination of the two unit calculations;
   the extension calculation already uses existing generic derived-adjunction tools.
   Public imports supply its statement. The extension helper's plain imports supply
   actual proof lemmas and flat-resolution instances. The unfinished pullback helper
   must retain the three geometric imports prescribed by its proof plan. No global
   pruning is claimed. The report names every old direct proof dependency redistributed
   below the helpers. The unit's realized statement and step fields are unchanged;
   this local decomposition changes no chapter or unit route.
5. Checked every delivered node's lean.statement against the declaration text and
   proof_deps against the union of its proof steps' uses: all match. The parent records
   the actual hc/Hom-equivalence combination, the extension node records its complete
   implementation, and the pullback node records the remaining sourced calculation.
   The new nodes retain the parent's chapter, unit and explicit blueprint ancestry.

Second-reading changes: restored Modules.IsKFlatTilde, TensorPullbackTilde and
AffineTildeDerivedSectionsUnitIsIso as plain proof imports of the unfinished pullback
helper, where their DAG dependencies now live; clarified the redistribution above.
No mathematical statement or proof body was changed. One original hole is closed and
one lower hole added: decomposition, with no net hole gain; global pruning is none.
