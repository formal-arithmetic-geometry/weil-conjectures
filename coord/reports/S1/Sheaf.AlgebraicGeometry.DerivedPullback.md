## What changed

Completed the proof of `AlgebraicGeometry.exists_derivedPullback`, preserving its entire
signature and the definition `AlgebraicGeometry.derivedPullback`. The proof uses the direct
K-flat resolving-class construction from Stacks Tag 06YJ. It constructs the additive tensor
pullback using its existing adjunction, lifts resolutions and morphisms through the homotopy
quotient, applies `CategoryTheory.Functor.leftDerived_from_resolvingClass`, and specializes
its counit-isomorphism conclusion to K-flat representatives.

Added two separate intermediate theorem modules, each strictly a part of the argument.
`Sheaf.AlgebraicGeometry.InverseImageExactKFlat` states exact inverse image and preservation
of K-flat resolutions. `Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso` states only
preservation of quasi-isomorphisms between K-flat complexes by the underived tensor functor.
Both have complete proofs in words, sources, and dedicated nodes. Updated the item node's
proof, proof dependencies, and proof origin to match the Lean proof.

Added proof-only imports of these modules, the resolving-class theorem, and Mathlib's
additive-functor API. A local increase of `synthInstance.maxSize` is needed only to synthesize
the triangulated structure of the composite functor. No target, definition, or public import
of the original item changed. All three sandbox modules compile locally.

## Proved and sorry left

`AlgebraicGeometry.exists_derivedPullback` (node `def-pc-derived-pullback`) now has a complete
Lean proof from named dependencies. The item module contains no remaining `sorry`.
`AlgebraicGeometry.derivedPullback` remains its original choice definition.

The delivery adds exactly two sorries:

- `AlgebraicGeometry.exists_inverseImage_exact_kFlat`, node
  `lem-pc-inverse-image-exact-kflat-resolution`, module
  `Sheaf.AlgebraicGeometry.InverseImageExactKFlat`.
- `AlgebraicGeometry.tensorPullback_quasiIso_of_isKFlat`, node
  `lem-pc-tensor-pullback-kflat-quasi-iso`, module
  `Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso`.

The existing dependencies `CochainComplex.exists_isKFlatResolution` and
`CategoryTheory.Functor.leftDerived_from_resolvingClass` are intentionally used as stated;
their proofs are separate stage-3 items. This delivery does not close the transitive axiom
check for the target.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRings` / `lem-pur-derived-change-of-rings`;
- `Sheaf.Algebra.Homology.KFlatPullback` / `lem-pc-kflat-pullback-preservation`;
- `Sheaf.Topology.InverseImageStalk` /
  `lem-weil-pbc-topological-inverse-image-stalk`.

These modules are not needed directly for the assembly proof. Their mathematical content
remains in the proof plans of the two new preservation statements, so this is removal of
direct imports, not a claim that these three nodes can be discarded from the whole project.
`def-pc-quasi-iso-modules` is no longer a separate direct proof dependency of the item; it
remains a notion used to state the intermediate results. No unit statement or realized
unit step is bypassed. No global subtree is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped because directly composing derived change of rings appeared
to require an additional `HasDerivedCategory` instance at the inverse-image ring. The
original target does not supply that instance at universe `w`. The direct resolving-class
construction from the proof of Stacks Tag 06YJ avoids using that intermediate derived
category entirely. Local standard derived categories can still be chosen when proving the
underived change-of-rings preservation fact; their universe never enters the target.

Inference of `E` without an explicit shared-category type also selects the `Scheme.Modules`
category instances, which prevents Lean from finding the supplied derived-category instance.
The final proof explicitly types `E` using the shared `SheafOfModules` carriers.

Searches of the blueprint and the existing library found etale constant-coefficient
inverse-image exactness and ordinary-module tensor results, but no exact statement of
either new topological scheme-module preservation result. LeanSearch returned a service
error; this is recorded as unavailable, not as evidence of absence. Sources read online:
[06YJ](https://stacks.math.columbia.edu/tag/06YJ),
[06YC](https://stacks.math.columbia.edu/tag/06YC), and
[06YT](https://stacks.math.columbia.edu/tag/06YT).

## New nodes

`lem-pc-inverse-image-exact-kflat-resolution` records the original node's exact inverse-image
step and its inverse-image preservation of a K-flat resolution. Its edge cases include the
empty scheme and identity morphism; no flatness or surjectivity assumption is added.

`lem-pc-tensor-pullback-kflat-quasi-iso` records the preservation condition used by the
resolving-class construction. It assumes K-flatness of both complexes and a
quasi-isomorphism between them, and concludes only an underived quasi-isomorphism. It does
not assume or conclude existence of the derived pullback. No change record is required:
existing public interfaces are unchanged.

## Second reading by S1

1. **Existing interfaces: pass.** Read the repository and sandbox modules in full and
   compared them with `diff -u`. The complete signature of `exists_derivedPullback`,
   including both universe-w derived-category assumptions, every object/map equality,
   exactness and resolution clause for I, universal property, triangulated structure,
   and counit-isomorphism clause, is byte-for-byte unchanged. The entire definition
   `derivedPullback` is unchanged. All original public imports are unchanged. There
   are no changed existing statements or definitions requiring a change record.
2. **Lean proof and axioms: pass as a reduction.** Recompiled all three modules through
   lcompile in import order, without errors or warnings. Read the construction of E
   from its adjunction, the full homotopy quotient lifts, hres and hinv, and the final
   application of `leftDerived_from_resolvingClass`. No proof is hidden in a definition;
   only the two reported named intermediate theorems contain sorry. Scratch copies
   with `#print axioms` for all four declarations show exactly propext, Classical.choice,
   Quot.sound, and sorryAx. The latter remains through the open dependencies; this is
   not a claim of a transitively closed target. No forbidden declaration or attribute
   occurs in the delivered modules.
3. **Split statements: pass.** Read Stacks 06YJ (lemma-derived-base-change), 06YC
   (lemma-pullback-K-flat), and 06YT (sites-cohomology-lemma-K-flat-quasi-isomorphism).
   Exact inverse image and K-flat resolution preservation are strictly the I portion
   of the item, with no derived functor conclusion. Tensor preservation is just the
   inversion hypothesis for the resolving-class theorem. Both statements hold without
   flatness or surjectivity. For identity morphisms they reduce to preservation by the
   identity; for empty schemes the module category is trivial. On affine nonflat ring
   maps the two K-flat hypotheses are essential: arbitrary complexes would not give
   tensor preservation. The docstring's tensor square resolves the target ring and
   uses K-flatness on both vertical arrows; it is the argument of 06YT, not an appeal
   to exactness of tensor pullback. Inspected the statement of `derivedChangeOfRings`:
   its first clause is exactly the change-of-rings fact needed, and locally choosing
   standard derived categories introduces no extra hypothesis in the complex claim.
   Searched again with msearch grep, Loogle `QuasiIso`, and separate LeanFinder queries
   for exact inverse image and K-flat pullback quasi-isomorphisms, plus rg of lean/Sheaf,
   lean/WeilConjectures, and the upstream homology/module-sheaf files. Results provide
   generic sheaf pullback and quasi-isomorphism APIs, not either new concrete statement.
   These are not restatements of the full item. Closing either helper requires the
   exactness/complex-transport work recorded in its node, not a short overlooked lemma.
4. **Route and pruning: pass after import repair.** The proof follows the direct
   resolving-class construction in 06YJ: choose K-flat resolutions, invert morphisms
   between K-flat representatives, then obtain the derived functor and its counit.
   Read `dag/units/sk-thm-picard-semicon.json`; its statement and step concern the
   semicontinuity/Grauert argument and its realized lists are empty. No recorded unit
   statement or step is bypassed here. Compared old and new proof_deps: all four
   removed direct dependencies are accounted for in No longer needed; module pullback
   and K-flat resolution are retained. Stalk, K-flat pullback, and change-of-rings facts
   remain below the new helper nodes, so there is no claimed global pruning. Replaced
   the unused TensorPullback import in InverseImageExactKFlat by the narrower Scheme
   module API and InverseImageModule imports. Paper.DerivedHomMayerVietoris is needed
   for `moduleRings`; KFlat and the complex APIs occur in the signatures. Main-module
   additions are proof-only imports; new-module public imports serve their signatures.
5. **DAG agreement: pass.** Compared the existing node with the repository: only proof,
   proof_deps, and proof_origin change. Its four steps correspond respectively to the
   I witness, construction of E, hres/hinv, and the resolving-class application.
   Checked both new nodes' statements against every binder and conclusion in their
   Lean signatures, and checked their source, proof steps, dependencies, searches,
   created/blueprint, chapter/unit, and lean records. Their remaining sorries each have
   a named theorem, complete proof in words, and matching node. Added the missing
   module-docstring blueprint references to both new modules. No node statement or
   existing declaration docstring was changed.

Second reading changed only the unused import in InverseImageExactKFlat and the two
new modules' module-docstring blueprint references. The original proof is retained.
