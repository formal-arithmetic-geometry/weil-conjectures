## What changed

Proved `AlgebraicGeometry.exists_openComparison_cohomology_model_iso` in
`Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel`, retaining its original statement,
universes and derived-category parameters. Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`
for the K-injective preservation criterion and the existing composition instance.

Private helpers construct the ordinary-to-derived cohomology unit, show it is invertible
on K-injective complexes, show ordinary cohomology is derived by the cochain K-injective
localizer, compare the two ordinary homology isomorphisms, and prove preservation of
K-injectives under open restriction. The final proof applies the right-derived-functor
uniqueness theorem to the two prescribed units; its factorization equation is exactly
the required normalization square. Updated the existing node's final proof step and
proof origin to describe this implementation.

The original definitions and public signatures are unchanged. Two transparent public
abbreviations cache Mathlib’s canonical abelian structures on module sheaves and
over-site module sheaves; their instance attributes are local to this file. They add
no mathematical data or assumptions. The change record is
`coord/changes/open-comparison-abelian-elaboration.md`. Local instances also cache concrete category
properties in the proof to avoid repeated instance searches. The
unused-section-variable warning is suppressed only for the final theorem, to retain its
existing over-site derived-category parameter. The standard module-derived-category
instance is inlined to match the data of the existing comparison map.

Sources checked: Stacks Project [Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
and [Tag 079V](https://stacks.math.columbia.edu/tag/079V). The proof uses arbitrary opens
and complexes; it imposes no boundedness, quasi-coherence, nonemptiness, or nonzero-ring
assumption. The existing unit route is retained.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.exists_openComparison_cohomology_model_iso`
(node `lem-sc-open-sections-cohomology-model-comparison`).

No `sorry` remains in the delivered module. No holes were added or split off. Existing
proof dependencies retain their own obligations; no claim is made that the transitive
import closure is now free of holes.

## No longer needed

Both original proof dependencies remain necessary. No original imports were removed,
and no DAG nodes or modules were pruned. Second reading replaced the first worker's direct
proof-only `Comp` import with `FullyFaithful`, which reexports `Comp` and supplies the
already proved composition instance. Thus `Comp` remains a transitive dependency;
this is not a pruned module. The duplicate private `preservesKInjective_comp` was removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The final descent/cancellation step of the plan can be
implemented directly through the cochain K-injective derivability structure and the
universal property of right derivation. This gives normalization for all complexes in
one factorization identity. Initial compilation experiments found repeated concrete
instance searches expensive; the proof caches the relevant instances locally.

## Second reading by R3

1. **Interface: pass.** Compared the delivered module and node with the repository.
   Using the declaration parser, checked that every existing declaration's statement
   and every existing definition body is byte-identical. Restored the single space
   before the final theorem's `:=`. No hypothesis, conclusion, universe parameter or
   public visibility changed. The two new public abbreviations are transparent caches
   of Mathlib's canonical instances, with only local instance attributes. Reviewed
   `coord/changes/open-comparison-abelian-elaboration.md`: no downstream adaptation or
   target-meaning change is needed.
2. **Proof and axioms: pass.** Read every helper and the final construction. The
   ordinary-cohomology functor inverts quasi-isomorphisms between K-injectives because
   they are homotopy equivalences. Both prescribed units are invertible there, and
   right-derived uniqueness supplies the exact normalization equation. The repaired
   module, with explicit scratch `#print axioms`, compiled without warnings in 38.8 s.
   The comparison theorem and both cache abbreviations use only `propext`,
   `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs in their dependencies.
   No `sorry`, axiom declaration, unsafe/opaque declaration, external implementation,
   or hollow definition occurs in the delivery. No arbitrary data witness is chosen
   from an unproved theorem: the comparison is constructed by right-derived uniqueness.
3. **Split statements and edge cases: pass.** There are no split-off statements or new
   holes. The argument works for the empty open, zero ring, zero complex and unbounded
   complexes: all steps are functorial and no point, nonzero element or degree bound is
   selected. Reread Stacks Tags [08BS](https://stacks.math.columbia.edu/tag/08BS) and
   [079V](https://stacks.math.columbia.edu/tag/079V); their restriction and unbounded
   sections constructions agree with this argument. Repeated searches with Loogle
   (`"mapHomologicalComplexHomologyIso"`), LeanFinder (uniqueness with units invertible
   on K-injectives), and repository `rg` found generic ingredients and the upstream
   `Functor.preservesKInjectiveComplexes_comp`. Replaced the duplicate private
   composition helper by that existing instance. The open-restriction helper packages
   the original exact-adjunction dependency; it introduces no postponed result.
4. **Route and pruning: pass.** The proof follows the shortest available general
   uniqueness route and retains both original `proof_deps`, using ordinary sections
   and exact extension-by-zero/restriction. Original public imports support the
   existing definitions, and the added upstream import is proof-only. Checked
   `dag/units/sk-thm-picard-duality.json`: its `realized` record is unchanged (the
   existing statement and step lists are empty), and this below-unit comparison
   does not replace any unit step. `No longer needed` accounts for the replaced
   direct import and duplicate helper; no old dependency node or module was pruned.
5. **DAG agreement: pass.** Only the existing node's `proof` and `proof_origin` differ;
   `proof_deps` remains the union of step uses. The updated final step describes the
   actual localizer derivability, two units, uniqueness isomorphism and component
   factorization equation. The statement, Lean record, chapter and unit are unchanged.
   No new nodes are necessary for split-off obligations, since none were introduced.

Second reading changed only the proof-only upstream import, removal/application of the
duplicate composition helper, and restoration of signature whitespace; updated this
report accordingly. Closed one original hole, added zero, split off zero.
