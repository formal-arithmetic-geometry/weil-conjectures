## What changed

Proved `AlgebraicGeometry.ProEtale.isSheaf_latticeCoefficientPresheaf` from
Mathlib fpqc descent for continuous functions, forgetting ring structure,
restricting the topology, and removing the universe lift.

Completed step 1 of the main theorem: constructed the embedding of each lattice
pair, proved its injectivity by local finite bases and local injectivity of
sheafification, and proved the exact image criterion and uniqueness of
intertwining isomorphisms. The coefficient inclusion is injective even over empty
objects; no rank positivity or nonempty-object hypothesis is used here.

Completed the constant-matrix constructions and calculations in step 4. The
standard finite free integral sheaf has an explicitly constructed scalar-extension
isomorphism, normalized on its basis. Constant invertible matrices act by sheaf
automorphisms, giving actual finite free lattice pairs with precisely the required
`matrixLatticeImage` on every test object. Equal integral matrix cosets give equal
images. Over a nonempty object, evaluating continuous coefficients at a point
recovers equality of cosets from equality of images. Zero rank and empty objects
are included in the construction and the forward invariance statement.

Added private proof imports of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`,
`Mathlib.RingTheory.Flat.Basic`, and `Mathlib.LinearAlgebra.TensorProduct.Pi`.
Updated the main node's steps 1 and 4 and their dependencies. No existing signature
or definition changed. The added public lemmas and scoped proof commands are
recorded in `coord/changes/lattice-pair-image-classification.md`.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.ProEtale.isSheaf_latticeCoefficientPresheaf`.

Eight additional proved public declarations:

- `AlgebraicGeometry.ProEtale.IntegralLatticePair.equivalent_iff_image_eq`
- `AlgebraicGeometry.ProEtale.IntegralLatticePair.intertwiningIso_unique`
- `AlgebraicGeometry.ProEtale.integralLatticePair_equivalent_iff_image_eq`
- `AlgebraicGeometry.ProEtale.matrixLatticeImage_eq_of_coset_eq`
- `AlgebraicGeometry.ProEtale.matrixLatticeImage_coset_eq_of_eq`
- `AlgebraicGeometry.ProEtale.matrixLatticeImage_coset_eq_iff`
- `AlgebraicGeometry.ProEtale.exists_latticeFreeScalarExtensionIso`
- `AlgebraicGeometry.ProEtale.exists_matrixIntegralLatticePair`

The only remaining `sorry`, unchanged from the original module, is
`AlgebraicGeometry.ProEtale.integralLatticeSheaf_locallyConstant`
(node `lem-weil-pbc-lattice-sheaf-locally-constant`). It still needs global descent
and the class presentation, compatibility of restrictions and rationalizations,
the empty-cover passage, general local matrix coordinates and the open-stabilizer
argument, and the normalized constant-sheaf comparison. Step 1 and the actual
constant-pair/image calculations of step 4 are now available as proved lemmas.

Added holes: none. One of two original holes is closed. The main theorem is not
reported as proved or reduced to new holes.

`#print axioms` was checked for the coefficient theorem and all eight added public
lemmas: each uses only `propext`, `Classical.choice`, and `Quot.sound`. The combined
file with the final two axiom checks compiled in 49.9 seconds. The delivery dry run
printed OK, passing compilation and preflight except for the second reading that
the independent second worker supplies. Nothing was pushed.

## No longer needed

None. The unfinished main theorem still needs its descent and local coset
classification route, so the original dependencies are retained. No module or
node is pruned and no split-off obligation is added. Two unused private formula
helpers from the new proof were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing upstream continuous-ring-presheaf
sheaf theorem restricts its coefficient type to `Type 0`, so it cannot directly
prove the universe-polymorphic coefficient theorem here. Mathlib's underlying
fpqc continuous-map theorem supplies the proof without changing that interface.

Image injectivity needs local injectivity of the module sheafification unit
before applying the local finite-free coordinate calculation. Sectionwise
injectivity of the unsheafified tensor unit alone would not suffice. The proof
explicitly refines these two covers and uses separatedness.

## New nodes

`lem-weil-pbc-lattice-pair-image-classification`: the completed first step, with
the exact image criterion, unique intertwining isomorphisms, and the prescribed
coefficient-inclusion specialization. Its three declarations are proved.

`lem-weil-pbc-matrix-lattice-coset-invariance`: coset invariance of matrix lattice
images, the nonempty evaluation converse, and their equivalence. Its three
declarations are proved. The nonempty hypothesis is necessary only for the
converse; the main theorem's empty-cover argument remains open.

`lem-weil-pbc-lattice-free-scalar-extension`: the standard finite free
scalar-extension comparison and its basis normalization. Its single public
theorem is proved by an explicit isomorphism.

`lem-weil-pbc-constant-matrix-lattice-pair`: construction of an actual finite free
integral lattice pair with the exact constant-matrix image formula on every
slice object. Its single public theorem is proved by explicit constructions.

All four nodes come from the corresponding local calculations in Bhatt--Scholze,
Proposition 6.8.4(6), pp. 59--60. Each includes the statement, complete proof in
words, dependencies, Lean attachment and recorded searches. None adds a `sorry`.

## Second reading by F2

1. **Signatures and accidental changes.** I diffed the delivered module against
   the repository version. The existing declarations, including all definitions
   and the main theorem statement, are byte-for-byte unchanged; the only edits
   to existing code are the coefficient-sheaf proof and private proof imports.
   The added public declarations are documented in the change record, and no
   target statement or definition was changed. Verdict: pass.

2. **Proof and axioms.** I compiled the module with
   `python3 /home/ubuntu/weil-launcher/lcompile.py`; it completed without errors
   or warnings. The coefficient theorem and all eight added public declarations
   were checked with `#print axioms`; each uses only `propext`,
   `Classical.choice`, and `Quot.sound`. The sole remaining `sorry` is the
   pre-existing main theorem, and no forbidden declaration or hollow definition
   was introduced. Verdict: pass.

3. **Split-off statements.** I read each of the four new node files and the
   corresponding docstrings. Their hypotheses cover the edge cases claimed
   (zero rank and empty objects; nonemptiness only for the evaluation converse),
   and each statement is a strict intermediate calculation used by the proof,
   rather than a restatement of the main theorem. Searches recorded in the node
   files found no existing declaration duplicating them. Verdict: pass.

4. **Route and pruning.** The coefficient sheaf proof uses the Mathlib fpqc
   continuous-map sheaf theorem. The image, matrix, scalar-extension, and
   constant-pair proofs use the shortest available local constructions and the
   stated intermediate nodes. Every old proof dependency remains needed by the
   unfinished main-theorem route, so no import or node can be pruned. Verdict:
   pass.

5. **DAG and unit route.** The modified main node records the completed step 1
   and step 4 dependencies, while the four split nodes carry matching Lean
   declarations, proof text, sources, and dependencies. The unit and its route
   remain unchanged; the unfinished steps are still represented by the original
   main node. Verdict: pass.

I changed only this report: I added this second-reading record. The module,
nodes, and change record required no repair.
