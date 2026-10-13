## What changed

Replaced the sorry in `AlgebraicGeometry.exists_affineBaseChangeTildeGlobalComparison`
with transport from the fixed tensor construction to the supplied arbitrary model.
The original signature and docstring are unchanged. Two proof-only imports were added:
`Sheaf.Algebra.Homology.AffineBaseChangeTildeCanonicalGlobalComparison` and
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence`.

The algebraic model-independence theorem compares two universal derived functors by
Mathlib's `Functor.leftDerivedNatIso`. Its cohomology isomorphism respects both tensor
factors by naturality and the recorded scalar-action equations. Tensor induction lifts
it to the tensor algebra. The two pure-tensor formulas identify the ordinary maps;
the universal counit equation identifies their comparison maps. Extension/restriction
adjunction then proves compatibility with their localized comparisons. The parent maps
this source isomorphism through restriction and tilde and composes with the fixed-model
source coordinate. Associativity and functoriality prove the original square.

The remaining geometric calculation is separately stated for the library's fixed model,
not for an arbitrary universal derived functor or arbitrarily presented tensor action.
The model-independence argument has been removed from that calculation. This keeps the
unit route and all geometric hypotheses. No other existing module was adapted, and no
new data definition or choice from an unproved mere-existence statement was introduced.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_affineBaseChangeTildeGlobalComparison`
(node `lem-pc-affine-base-change-tilde-global-comparison`), by a complete transport proof.

New proved theorem: `ModuleCat.baseDerivedTensorCohomologyModel_localized_independence`
(node `lem-pc-base-derived-tensor-cohomology-model-localized-independence`).
Its private tensor-linearity helper is also proved.

Added and remaining sorry:
`AlgebraicGeometry.exists_affineBaseChangeTildeCanonicalGlobalComparison`
(node `lem-pc-affine-base-change-tilde-canonical-global-comparison`).
This is the fixed-model affine calculation; it does not contain the arbitrary-model
universality and scalar-action transport, which are proved separately. One upper hole
closed and one lower hole added: a decomposition, with net hole count zero, not a claim
that the geometric comparison is proved without remaining dependencies.

## No longer needed

No imports removed. The three original public imports are needed by the unchanged
statement. No geometric module or DAG node is claimed pruned from the targets' closure.
The original geometric proof dependencies are now attached to the fixed-model
calculation rather than directly to the transport proof. Arbitrary-model uniqueness
needs no K-flat resolution, affine vanishing, scheme mates or stalk comparison.

## Where the brief, the DAG or earlier work was wrong

The previous missing-object-file blocker is resolved: the unchanged item compiled on
the project server against its published build. The earlier arbitrary-model interface
gap is real, but the recorded universal counits, scalar actions and pure-tensor formulas
suffice to prove the required model-independence theorem. No stronger hypothesis on M
or any ring map was needed.

The cited Stacks TeX files are absent in this machine's read-only literature directory.
The official pages https://stacks.math.columbia.edu/tag/06Y6 and
https://stacks.math.columbia.edu/tag/0DJ8 were consulted instead. Tag 08IB is a
scheme base-change lemma, not a tag in more-algebra.tex; the new algebraic theorem
uses Tag 06Y6 for independence of choices. LeanSearch returned Internal Server Error;
LeanFinder and local searches were used, with unavailable service recorded as such.

Edge cases: model independence assumes no K-flatness, Tor independence, nonzero ring
or boundedness. Tensor induction and the universal counit equation apply unchanged to
zero rings and zero complexes, all degrees and identity scalar extensions. The
geometric fixed-model statement retains every original hypothesis and uses the same
actual coordinate definitions. The unit's realized statement and steps were unchanged.

## New nodes

`lem-pc-base-derived-tensor-cohomology-model-localized-independence` records the purely
algebraic, proved comparison of any two tensor cohomology models, with their localized
comparison maps. Its module is
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence`.

`lem-pc-affine-base-change-tilde-canonical-global-comparison` records the geometric
calculation for `ModuleCat.baseDerivedTensorCohomologyModel`, with the fixed construction
and canonical target coordinates. Its module is
`Sheaf.Algebra.Homology.AffineBaseChangeTildeCanonicalGlobalComparison`.
No change record is necessary: the existing statement and its public imports are unchanged.

## Second reading by Q2

1. The delivered global-comparison module was diffed against the repository version. The
   target theorem's signature and docstring are byte-for-byte unchanged; only two plain
   proof imports and its proof body were added. Verdict: pass.

2. All three delivered modules compile in import order with `lcompile.py`. The global
   theorem has no `sorry`; the only remaining `sorry` is the named fixed-model theorem,
   with the matching split node and source proof documentation. No axiom, unsafe,
   opaque, extern, or hollow definition was introduced. Verdict: pass.

3. The new model-independence statement is strictly a lower algebraic component: it
   compares two already supplied universal models and their localized comparison maps,
   without scheme hypotheses. The fixed-model theorem removes arbitrary-model transport
   from the geometric calculation. The statements are true in zero-ring and zero-complex
   edge cases and retain exactly the hypotheses of their nodes. No duplicate library
   declaration was found. Verdict: pass.

4. The proof uses `Functor.leftDerivedNatIso`, the recorded counit and scalar-action
   equations, tensor induction, and extension/restriction adjunction; the parent proof
   then transports the fixed-model square. This keeps the unit's fixed-model route while
   pruning no required imports. Verdict: pass.

5. The item and both new nodes agree with the Lean declarations: proof steps and
   `proof_deps` cite the canonical calculation and model-independence theorem, and the
   node records preserve the original target statement. The canonical node remains split
   with its named `sorry`; no unrelated node or module was changed. Verdict: pass.

Changed during second reading: appended this review only; no Lean declarations,
statements, definitions, imports, or DAG fields were changed.
