## What changed

Proved `AlgebraicGeometry.Spec.map_surjective_baseChange` without changing its signature.
Added the proof-only import `Mathlib.AlgebraicGeometry.PullbackCarrier`.
The proof registers the given surjectivity as an instance, rewrites the desired map using
`pullbackSpecIso_inv_fst R R' S`, and uses surjectivity of the pullback projection and of
an isomorphism. Updated the existing node's proof, proof_deps and proof_origin to this route.
Both dependencies are existing Mathlib leaves; this changes no unit statement or realized step.
The second reading updated the docstring to the actual scheme-pullback proof recorded in the node.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Spec.map_surjective_baseChange`
(node `lem-weil-pbc-spec-surjective-base-change`). No sorry remains in the delivered module,
and no new holes or declarations were added. This is a proof, not a decomposition.

## No longer needed

The earlier route's proof dependencies are not needed by this proof:
- `lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`
  (`Mathlib.RingTheory.Spectrum.Prime.RingHom`, `PrimeSpectrum.nontrivial_iff_mem_rangeComap`);
- `def-weil-pbc-localization-at-prime`;
- `def-weil-affine-spectrum` as a proof dependency (it remains a statement dependency);
- `lem-weil-pbc-tensor-cancel-base-change`
  (`Mathlib.RingTheory.TensorProduct.Maps`, `Algebra.TensorProduct.cancelBaseChange`).

No original import was removed: both public imports support the unchanged statement.
No Sheaf dependency module is imported. The generic Mathlib import may transitively include
some of the APIs above; the pruning claim is about the node's argument dependencies,
not disappearance of those Mathlib modules from the target import closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's searches had already found scheme-level surjectivity stability, but deferred it
because identifying the affine pullback needed additional work. Mathlib's projection identity
makes that work one rewrite. The stronger ring-level lemma in
`WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale` also exists, but its larger module
is unnecessary. LeanFinder, Loogle, and direct source searches confirmed the smaller route.
Arbitrary commutative rings, including zero rings, are covered by the Mathlib scheme result;
no flatness, nontriviality, or field hypothesis is introduced.


## Second reading by N3

1. **Visible declarations: pass.** Compared the complete delivered module and node
   with the repository using `diff`. The sole existing theorem's signature is byte
   for byte identical, including universes, all three commutative rings, both
   algebra structures, the surjectivity hypothesis, and the tensor inclusion
   conclusion. No definition, statement, or public import changed. No change
   record is needed.
2. **Proof: pass.** Compiled the module with `lcompile.py` and compiled a scratch
   copy with `#print axioms AlgebraicGeometry.Spec.map_surjective_baseChange`.
   The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are
   no remaining sorries, forbidden declarations, or data constructions in this
   module. The anonymous `let := h` registers the supplied surjectivity instance;
   it chooses no witness. Read `Pullbacks.lean:725–743`,
   `PullbackCarrier.lean:436–450`, and `Morphisms/UnderlyingMap.lean:59–71`:
   the rewrite has exactly the required tensor inclusion, and the inferred
   instances give the surjective inverse isomorphism, projection, and composite.
3. **Split statements: pass, none.** No new declaration, node, or hole was added.
   Independently searched with `msearch.py ... grep` for the projection identity,
   and `rg` in both Lean roots for tensor-product spectrum surjectivity. Read
   `PrimeSpectrum.comap_surjective_tensorProduct_left` in
   `WeilConjectures/RingTheory/ProEtale/WeaklyEtaleIndEtale.lean:96` as an
   alternative; the existing three-line Mathlib proof avoids that larger import.
   Zero rings are not excluded: if the new base has empty spectrum the result
   is vacuous, and if the original source has empty spectrum the hypothesis
   forces the original base spectrum empty. No nontriviality or flatness is used.
4. **Route and pruning: pass.** The argument starts at the target and closes it
   entirely with Mathlib. The public imports provide the signature's scheme-map,
   surjectivity, and tensor APIs; the only new import, `PullbackCarrier`, is
   proof-only and provides the needed base-change instance and affine identity.
   `No longer needed` lists all four old proof dependencies. Inspected
   `dag/units/sk-thm-p1.json`: this auxiliary node is absent from its `realized`
   statement and steps, and no node realizing those steps is bypassed or altered.
   Both replacement dependencies are already Mathlib leaves, including the
   affine lemma's projection compatibility clause. No Sheaf module was pruned
   from imports; pruning here concerns the four old argument dependencies only.
5. **Node agreement: pass.** JSON comparison confirms only `proof`, `proof_deps`,
   and `proof_origin` changed. The dependency list is exactly the union of the
   steps' `uses`. Read both cited Mathlib-leaf nodes: scheme surjectivity stability
   supplies the first projection (with factors ordered R', S), and affine
   fibre-product identification supplies the stated isomorphism and projection
   identity. The final elementary step is composition with a surjective
   isomorphism. No new-node requirements apply.

**Second-reading repair:** replaced the stale fibre-ring proof in the theorem's
Docstring with the actual three-step scheme-pullback proof, and updated the report
accordingly. The compiling proof and node metadata required no changes. Closed
one original hole, added zero holes; no decomposition.
