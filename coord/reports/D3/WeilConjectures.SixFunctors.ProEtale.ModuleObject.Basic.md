## What changed

Filled the theorem-level proof of `AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt`.
The proof extracts a finite effective-epimorphic family from a coherent sieve, proves joint
surjectivity on `Spec (LocallyConstant T ℤ)` using the existing prime-spectrum description,
proves weak etaleness by cancellation against the structure maps, and applies the affine
quasi-compact cover construction. The image sieve is then compared with the pushed-forward
input sieve. Added one proof-only import of
`WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant` for the prime-spectrum
surjectivity lemma.

The seven upstream `instance` declarations in this module remain byte-for-byte unchanged.
The stage-3 gate rejects changing their proof bodies because they are non-theorem declarations;
they therefore remain for a later compatible repair.

## Proved and sorry left

Hole closed: 1 of 8, by declaration name:

- `AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt` — proved.

Holes left: 7 of 8, unchanged from the base module:

- `AddCommGrpCat.hasFunctorialFlatResolution`;
- `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`;
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt`;
- `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`;
- `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar`;
- `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`;
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`.

No holes were added and no split-off theorem was introduced.

## No longer needed

The proof uses the existing finite-cover, weak-etale, affine-spectrum and pro-etale-site
nodes recorded by the cover-preservation node. No old proof dependency is removed. The
three helper imports used by the rejected upstream-instance repair are absent from this
partial delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier worker's eight proofs compile and use only the permitted axioms, but the current
stage-3 gate refuses body changes to upstream `instance` declarations regardless of unchanged
type and instance behavior. The valid theorem proof is delivered independently; the seven
instance proofs must be supplied through a route accepted by that gate.

## Second reading by D3

1. **Interfaces: pass.** Compared the delivered module with the repository version. The only
   existing declaration whose body changes is the named `coverPreserving_profiniteToProEt`
   lemma; its signature is identical. The sole added import is plain and proof-only.
2. **Proof and axioms: pass.** Basic compiles cleanly with `lcompile.py`; the completed lemma
   has no `sorry` or forbidden declaration and its axiom probe uses only `propext`,
   `Classical.choice`, and `Quot.sound`.
3. **Split statements: pass.** No new statement or hole is added. The proof uses existing
   declarations and handles empty targets and finite families through the coherent-sieve
   interface.
4. **Route and pruning: pass.** The proof follows the node's finite-family, spectrum,
   weak-etale, quasi-compact-cover and generated-sieve steps. No unit-route import is
   removed; the one required proof import is plain.
5. **Nodes: pass.** Only the cover node's proof/proof-dependency fields are updated, and they
   match the delivered proof. No new node or change record is needed.

Second reading changed the report and retained only the valid theorem-level proof.
