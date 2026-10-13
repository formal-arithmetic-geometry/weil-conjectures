## What changed

Completed `AlgebraicGeometry.derivedRHomAlgebraModule_underlying` in
`Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule`, preserving existing public signatures,
visibility, definition bodies and public imports. Added the proof import
`Sheaf.AlgebraicGeometry.HomComplexSingleNatural`. The proof specializes the existing
natural derived-internal-Hom comparison at B[0], identifies its Hom complex with
termwise sheaf Hom, composes with exact restriction of scalars, and descends through Q
by full faithfulness. The private helpers `fixed_comparison` and `compose_comparisons`
are completely proved categorical arguments.

Refactored the existing underlying-functor equality through proved generic identities
and objectwise extensionality. Generic restriction-of-scalars lemmas supply the existing
finite-limit and finite-colimit proofs. Moved generic private helpers ahead of the
scheme-specific variables, and scoped the resolution-inversion instance binders so that
the fully explicit derived-functor definition does not elaborate duplicate ambient binders.
These changes address the previous attempt's compile timeout without splitting the file,
raising the time limit, changing definitions, or introducing new obligations.
Removed the unused private helper `ofPresheaf_eq` and redundant private KInjective import.
Updated the item's DAG proof and dependencies to record the completed argument.
The command-scope changes are recorded in
`coord/changes/DerivedRHomAlgebraModuleElaborationScopes.md`; no consumer is adapted.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.derivedRHomAlgebraModule_underlying`
(node `def-pc-derived-rhom-algebra-module`). Added zero holes; no sorry remains in the
item or is added elsewhere. All private helpers are completely proved. This is a proof,
not a decomposition. The comparison retains arbitrary unbounded complexes, both
derived-category universes, arbitrary schemes, and commutative quasi-coherent algebras.

## No longer needed

Removed the proof import `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
its declarations are already available through DerivedInternalHom → KInjectiveResolution →
DerivabilityStructureKInjectives. Removed the unused private helper `ofPresheaf_eq`.
All public imports remain. No DAG node or module is claimed globally pruned.
The proof uses `def-pur-derived-internal-hom` and `lem-sc-hom-complex-single-natural`;
no unit statement or proof step is bypassed, and `sk-thm-picard-duality` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier node recorded the underlying comparison as unfinished, but its proof dependencies
were empty and omitted the existing natural single-source chain comparison. Both are now
recorded. No new intermediate statements are needed. The source identification is Stacks
Tag 0BV1; the proof makes its construction explicit using the same canonical resolution
and the exact scalar-restriction factorization. The previous worker's timeout was reproduced.
Moving generic private helpers outside the concrete variable scope brought the complete
module below the 60-second limit (50.9 seconds in the first successful repair compile).

## Second reading by M1

1. Compared the complete delivered module and node with the repository using `diff`.
   Verdict: existing public signatures, visibility, definition bodies, and public imports
   are unchanged. The helper relocation and section boundaries affect elaboration only;
   the existing explicit Y, B, hB, w and wB binders remain. The scope change is declared
   in `coord/changes/DerivedRHomAlgebraModuleElaborationScopes.md`. No adapted modules
   or target changes are present.
2. Read the complete module and compiled it with the prescribed local launcher: clean,
   47.7 seconds. Compiled a scratch copy with `#print axioms` for all 27 public
   declarations: clean, 46.5 seconds, and each uses only propext, Classical.choice,
   Quot.sound. No sorry, axiom, unsafe, opaque, extern or implemented_by occurs.
   The algebra-valued Hom and localization data remain explicit constructions; the
   Nonempty isomorphism witnesses are eliminated inside proofs, never used to choose
   arbitrary data for a definition. Verdict: a complete proof of the sole old hole.
3. No statement is split off and no hole is added, so there are no new obligations to
   search for or test. Read the new private comparison helpers: fixed_comparison
   evaluates the curried natural isomorphism at op P, while compose_comparisons uses
   exact scalar restriction and fully faithful localization whiskering. Both are
   proved general categorical reductions, not restatements of the target. Their
   arguments impose no boundedness, nonzero-object, flatness, or scheme restrictions;
   zero B and zero complexes are included. Verdict: no unjustified new statement.
4. Read derivedInternalHom_comparison and homComplex_single_natural_iso in their
   source modules. The former accepts precisely the canonical resolution and its
   quasi-isomorphism/K-injectivity proofs used here; the latter is natural on all
   complexes and applies to B.toModule. The scalar-restriction equality uses the
   existing O-linearity theorem, with morphism equality checked after faithful
   forgetting. Searched the library for the comparison names and Mathlib for
   restriction-of-scalars preservation and the currying/complex-composition APIs.
   Also read DerivedInternalHomSingleComparison: it would require constructing a
   right-derived-functor transformation and its universal property, so it supplies
   no shorter route for this localization-defined functor. The direct composition
   with mapDerivedCategoryFactors is appropriate. All retained public imports serve
   existing signatures or definitions; the new proof import is private. The removed
   KInjective import is transitively available. Old proof_deps was empty, so no old
   dependency node is missing from No longer needed. The unit sk-thm-picard-duality
   has empty realized statement/step lists, which remain unchanged; no unit route is
   bypassed. Verdict: the route and pruning are appropriate.
5. Compared the node diff: only proof, proof_deps and proof_origin change. Its final
   step names exactly def-pur-derived-internal-hom and
   lem-sc-hom-complex-single-natural, matching the two substantive declarations
   invoked by the proof. The first two steps describe the inherited explicit action,
   homotopy-equivalence descent and faithful-forgetting argument. Verdict: the DAG
   agrees with the Lean; no new node or statement change is required.

Second reading changed only this report: no Lean repair was needed. Closed
AlgebraicGeometry.derivedRHomAlgebraModule_underlying; added zero holes. No module
is claimed globally pruned.
