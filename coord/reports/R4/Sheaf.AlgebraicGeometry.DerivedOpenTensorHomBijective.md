## What changed

Completed `AlgebraicGeometry.Scheme.derivedOpen_tensorHom_bijective` in
`Sheaf.AlgebraicGeometry.DerivedOpenTensorHomBijective` without changing its statement,
universes, visibility, or existing docstring. Added six proved private helpers for the
adjunction counit criterion, invariance under natural isomorphism, sheaf and complex
support criteria, their derived counterpart, and tensor stalk vanishing.

The key simplification is exactness: homology of the termwise counit is the counit
of homology, up to canonical isomorphisms. Localizing the complex adjunction gives
the derived counit criterion directly. Both tensor factors receive K-flat resolutions;
the first-variable comparison and second-variable stalk vanishing then apply without
symmetry. All representatives and resolutions are used only within theorem proofs.
Added proof-only imports of `Mathlib.Algebra.Category.Grp.Zero`,
and `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
Updated the node's proof, proof dependencies, and proof origin to match the compiled route.

The module compiles without warnings through `lcompile.py`. The support criterion covers
empty U (every cohomology stalk must vanish), whole U (the exterior condition is vacuous),
and zero objects. The tensor proof has no boundedness, quasi-coherence, or finiteness
assumption. The unit record has no realized node requiring the removed isomorphism.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.derivedOpen_tensorHom_bijective`
(node `lem-sc-derived-open-tensor-hom-bijective`).
No `sorry` remains in the delivered module. No holes or new modules were added.
All six private helpers are fully proved. This is a proof, not a decomposition.
The five retained stated proof dependencies supply exactness, the counit stalk formula,
K-flat resolutions, the tensor comparison, and tensor stalk vanishing.

## No longer needed

Removed the proof-only import `Sheaf.Algebra.Homology.OpenExtensionRestrictionIso`
and its node `lem-pc-open-extension-restriction-iso` from this item's proof dependencies.
The argument does not separately use invertibility of the adjunction unit or an
extension/restriction functor isomorphism. The right triangle identity already identifies
restriction on Hom with precomposition by the counit followed by the adjunction equivalence.
The removed module may remain needed by other items; no global unreachability is claimed.
No other dependency of the original plan is pruned.
The second reader also removed the redundant newly added proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
its declarations are already available through retained public import closures.
This removes no additional stated proof dependency.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned explicit unit cancellation and stalkwise
quasi-isomorphism glue are unnecessary: the counit criterion holds for any adjunction,
and exactness lets us apply the existing sheaf-level stalk computation directly to each
homology sheaf. Resolving both tensor factors also avoids the planned braiding transport.
No process or tool failure remains.

## Second reading by R4

1. PASS: compared the complete module with the repository using diff. The sole existing
   theorem signature, universe parameters, visibility, and docstring are byte for byte
   unchanged. The only new declarations are six private proved helpers. No public
   definition, statement, or public import changed; no change record is needed.
2. PASS: compiled the module with lcompile.py without errors or warnings. Compiled a
   scratch copy with #print axioms for the theorem and all six helpers: each uses only
   propext, Classical.choice, and Quot.sound, with no sorryAx. Scanned for sorry, axiom,
   unsafe, opaque, implemented_by, and extern: none. Representatives, resolutions,
   adjunction structures, and comparison isomorphisms are chosen solely within proofs;
   no definition acquires arbitrary witness data.
3. PASS: no statement is split off and no new hole is introduced. Read all six helper
   arguments and the five retained dependency statements. The general adjunction
   criterion follows from the triangle identity and coyoneda; the sheaf criterion
   follows from stalkwise detection. Empty U, whole U, zero factors, and an empty space
   cause no exception. Independent loogle and leanfinder searches for the counit/Hom
   bijection criterion and local rg searches found no replacement for the full route;
   existing Mathlib homology and isomorphism lemmas are used directly.
4. PASS: the reduction genuinely proves tensor stability from support and K-flatness;
   it does not rename the original hole. Resolving both factors correctly supplies
   first-variable K-flatness for the tensor comparison and second-variable K-flatness
   for stalk vanishing. The old proof_deps differ exactly by removal of
   lem-pc-open-extension-restriction-iso, listed above. Read the unit record
   dag/units/sk-thm-picard-duality.json: its realized statement and step node lists are
   empty, so no realized unit route is bypassed. Checked the three added proof imports
   by independent removal compiles: Grp.Zero and HomotopyCategory.Adjunction are needed;
   ExactFunctor is redundant and has been removed.
5. PASS: the node's proof steps, proof_deps, and proof_origin describe the compiled
   argument and exactly its five stated dependencies. JSON comparison confirms all
   other fields are unchanged. No new nodes or changed statements need review.

Second-reading changes: removed the redundant proof-only ExactFunctor import and
updated this report. No mathematical proof or signature repair was necessary.
