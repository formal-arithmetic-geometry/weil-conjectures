## What changed

Proved `AlgebraicGeometry.Scheme.perfectRestriction_classes_small` in
`Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall`, with its original signature
and public visibility unchanged. Added two fully proved private helpers: transport of
a derived localization across an abelian equivalence, and identification of exact open
restriction with derived pullback followed by preservation of perfectness.

The proof constructs the needed open-scheme localization in the original morphism
universe, supplies local structures using `nonempty_derivedOpenLocalization`, computes
the composite immersion's image, and applies `pW`. Exact restriction preserves
quasi-coherence by `schemeDerivedQCoh_openRestriction_iff`. The existing
`derivedPullback_preserve_perfect` proves the perfectness part after a comparison
written using uniqueness of adjoints and uniqueness of left derived functors. Two
fully faithful lifts into the perfect quasi-coherent category give an injection of
skeletons. `small_of_injective` finishes the argument.

Added proof imports `Sheaf.AlgebraicGeometry.DerivedOpenLocalization`,
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh`,
`Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`,
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`. Updated the original node's proof,
proof dependencies and proof origin to record this route. All elaboration options are scoped to individual declarations, and required
instances are local to the proofs. No new public declarations,
new modules, new nodes, definitions, changed statements, or forced adaptations.

Sources checked: the existing Lean implementations and node signatures, Mathlib's
`Modules.overEquiv`, `Modules.overFunctorEquiv`, localization transport, full-subcategory
lifts and skeleton injection APIs, and the official Stacks pages for 08CM, 08DR and
09UA. The unit `sk-thm-picard-duality` has no realized node at this item; its route is
unchanged. The proof uses no choice of a point and covers empty and total opens.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.perfectRestriction_classes_small`
(node `lem-perfect-restriction-classes-small`). No `sorry` remains in this module.
No holes were added or split off. Both private helpers have complete Lean proofs.
This is a proof from existing library declarations; it does not claim that all
transitive dependencies of those declarations are free of `sorry`.

## No longer needed

Removed redundant direct proof imports
`Sheaf.AlgebraicGeometry.DerivedCategory`,
`Sheaf.AlgebraicGeometry.PerfectComplex`, and
`Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen`.
Their declarations remain needed and available through the unchanged public import
`Sheaf.AlgebraicGeometry.PerfectGluingEndpointProperties`; none of these modules or
nodes is removed from the transitive import closure. Thus no mathematical dependency
node or whole module is pruned.

The argument does not require an explicit range of a small family of representatives:
the fully faithful lifted functor injects the restriction skeleton directly into the
small perfect quasi-coherent skeleton. It also does not require a new lemma for
iterated open-site localization or a new perfect-restriction statement. All original
four definition nodes remain needed. The second reading also removed redundant
new direct imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`Mathlib.CategoryTheory.Localization.Equivalence`; their required APIs are already
available through the retained imports. No whole module leaves the import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan names definitions for the geometric transport steps rather than
lemmas that actually provide them. Existing `DerivedOpenLocalization`,
`DerivedOpenRestrictionQCoh`, and `DerivedPullbackPerfect` provide the missing inputs.
The generic localization transport already appears as a private helper in
`SchemeIsoDerivedLocalizations`; its proved construction is reproduced locally
because that private declaration is unavailable to importers.

Ordinary `Scheme.Modules.restrictFunctor` has instances tied to the separate
`Scheme.Modules` category convention. On the shared `SheafOfModules` carrier, derive
exactness of tensor pullback from the exact over functor and over equivalence instead
of asking instance search for exactness of that ordinary restriction functor.
There is no mathematical statement dispute or interface change.


## Second reading by V3

1. **Existing interface: PASS.** Compared the sole delivered module with the
   read-only repository using `diff -u`. The original public theorem signature is
   byte for byte identical, and its visibility, public import, definitions and
   hypotheses are unchanged. Only proof imports, private proved helpers and the
   theorem proof were added. The sole node changes only `proof`, `proof_deps` and
   `proof_origin`; no change record is required.
2. **Proof and axioms: PASS with existing open dependencies.** The delivered file
   compiles without errors or warnings using `lcompile.py`. Text inspection found
   no `sorry`, forbidden declaration or hollow definition. Scratch `#print axioms`
   checks show only `propext`, `Classical.choice`, `Quot.sound` for localization
   transport, and those plus `sorryAx` for perfect restriction and the main theorem.
   The latter axiom comes from existing imported open proofs, not any new hole.
   The localization helper constructs its target and localization functor explicitly.
   Derived pullback is selected with its universal property, which determines it up
   to natural isomorphism; the proof uses precisely that isomorphism. There is no
   arbitrary witness from an unproved mere-existence statement.
3. **Split statements and edge cases: PASS.** No statements were split off, no new
   nodes or holes were added. Both private helpers are fully proved. Reviewed the
   exact-functor comparison, localization transport and orientations of the local
   perfect-model isomorphisms. Empty opens/schemes need no chosen point; total opens
   and `W = f.opensRange` use the same comparisons and image identity. Independent
   `rg` searches in both Lean roots and `msearch.py ... grep` for small skeletons,
   skeleton injections and localization-derived functors found the existing generic
   APIs used by this proof, with no shorter public specialized replacement. The
   existing identical localization helper is private and cannot be imported.
4. **Route and pruning: PASS after import repair.** The proof begins with the
   supplied small-on-open hypothesis, transports restriction into its small perfect
   quasi-coherent category, and uses Mathlib's fully faithful skeleton injection.
   All four original proof-dependency nodes remain used, so none is falsely reported
   pruned. The unit `sk-thm-picard-duality` has empty realized statement and step
   lists, which this delivery leaves unchanged. Removed the redundant newly added
   imports of `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
   and `Mathlib.CategoryTheory.Localization.Equivalence`; the pruned proof compiled.
   A scratch trial also removing `PointwiseLeftDerived` failed on
   `isLeftDerivedFunctor_of_inverts`, so that proof import is retained.
5. **DAG correspondence: PASS.** Checked every recorded dependency's Lean module
   and declaration, each step against the written proof, and equality of
   `proof_deps` with the union of step `uses`. The eight dependencies describe the
   actual transport, exact restriction, perfect pullback and skeleton argument.
   `proof_origin` identifies this route and its sources. No new node fields need
   validation.

Second-reading changes: removed two redundant private proof imports and corrected
this report's import list. The main proof, both helpers, existing signatures and
node record were retained. The inherited theorem docstring describes the older
standard-localization/range route; the updated DAG and report describe the actual
explicit transported-localization/direct-injection proof. Closed one original hole,
added zero holes, split off zero statements, pruned zero whole modules.
