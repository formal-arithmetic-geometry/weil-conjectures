## What changed

Proved `AlgebraicGeometry.Scheme.isZero_sheafFiber_iff_of_same_image` in
`Sheaf.AlgebraicGeometry.GeometricStalkSupport`, preserving its complete signature.
Constructed the common separable closure and its embeddings, verified both geometric-point
factorizations, proved strict henselianity of the closure, and composed the existing
pullback-stalk and strictly henselian global-germ isomorphisms.
Updated the existing node's proof, proof dependencies and proof origin to match the Lean.
All proof imports are private imports. Local compilation passes without warnings.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Scheme.isZero_sheafFiber_iff_of_same_image`
(node `lem-kun-support-geometric-point-independent`).
No sorry remains in the delivered module, and no new sorry or node was added.
The proof uses the existing stated theorem
`AlgebraicGeometry.Scheme.strictlyHenselianSections_geometricStalk_isIso`
(node `lem-weil-pbc-strictly-henselian-sections-stalk`), whose proof remains sorry in
its unchanged module. This delivery is a stage-3 reduction to that existing input.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.EtaleSupport`: the conclusion is simultaneous vanishing,
  so neither support definitions nor derived support infrastructure is needed.
- `Sheaf.Paper.InverseImageStalkGerm`: the germ compatibility is unused; import
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` directly instead.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`: redundant direct import,
  already available through the strictly henselian input.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: redundant direct import through
  `StrictlyHenselianSectionsStalk`; the henselian definition itself is still used.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: redundant direct import
  through the stalk comparison module; inverse image itself is still used.

The item's proof no longer needs nodes `def-kun-support`,
`lem-weil-pbc-inverse-image-stalk-germ`, or
`lem-exc-etale-embedding-extension-sepclosed`. The embedding step uses the existing
Mathlib leaf `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed` instead.
The comparison uses the existing closed node `lemma-openclosed-stalk-upperstar`.
These are removals from this item's dependency route, not claims that no other target
reaches the corresponding modules. The unit's statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned general embedding-extension
lemma and germ-compatible inverse-image theorem are stronger than this proof needs.
Lean distinguishes the inhabited default of the spectrum from the field closed point;
the proof transports between them using uniqueness of the spectrum point.
Explicit vector-space torsion-free instances avoid expensive typeclass search for the
transported second residue-field embedding; no heartbeat limit change is needed.

## Second reading by W2

1. PASS: Compared the sole delivered module with the repository using diff and
   checked the existing theorem signature byte for byte. Only its proof and private
   imports change; no declaration, definition, public import or target is altered.
2. PASS: Local lcompile.py compilation is clean (2.9 seconds). No sorry, axiom,
   unsafe, opaque, implemented_by or extern occurs in the delivered code. A scratch
   #print axioms reports propext, Classical.choice, Quot.sound and sorryAx, consistent
   with the explicitly reported existing strictly henselian sections-stalk input.
   Checked both residue-field factorizations, strict henselianity of the separable
   closure, the two germ isomorphisms and the directions of all IsZero equivalences.
3. PASS: No statement is split off and no new node or declaration is introduced.
   The common separable closure argument works in both positive characteristic
   (including imperfect residue fields) and characteristic zero; it does not assert
   that a separable closure is algebraically closed. Empty X admits no given points.
4. PASS: Independent LeanFinder, Loogle and library searches found no direct shorter
   theorem for arbitrary abelian sheaves. The upstream locally constant sheaf result
   has extra hypotheses. The proof uses the existing general pullback-stalk iso
   directly and only the isomorphism part of the strictly henselian input. The three
   retained imports supply the statement, the global germ input and the comparison;
   proof imports are private. No longer needed lists exactly all three removed old
   proof dependencies and all removed imports. The unit record has empty realized
   statement/steps lists; its statement and route are untouched.
5. PASS: The node changes only proof, proof_deps and proof_origin. The dependencies
   are exactly the union of the proof steps' uses, with the embedding and stalk
   comparison leaf declarations verified against their records and Lean code.

Second reading changed only this report: no repair of the Lean proof or node was needed.
