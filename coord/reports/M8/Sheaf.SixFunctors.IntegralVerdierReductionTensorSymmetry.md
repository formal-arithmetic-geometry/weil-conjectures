## What changed

Proved `WeilConjectures.IntegralVerdier.reduction_tensor_symmetry` in
`Sheaf.SixFunctors.IntegralVerdierReductionTensorSymmetry`, preserving its signature.
The proof checks the signed chain square on scalar-unit total tensors, localizes
it, cancels the normalization isomorphisms, and transports along K-flat
representatives. All auxiliary lemmas are private and proved.

Added the private proof import
`import all Sheaf.SecSmoothPurity.ModuleTensorExtensionEquation` to reuse its
proved two-factor scalar-extension generator extensionality lemma. The public
import remains unchanged. Local transparency hints keep the completed ring
limit and tensor structures folded while exposing their coefficient wrappers.
Updated the item's node proof, dependencies and proof origin to match the Lean.
The delivered module compiled cleanly through `lcompile.py` in 59.6 seconds.
A textual comparison confirms that its public theorem signature is unchanged.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.IntegralVerdier.reduction_tensor_symmetry`
(node `lem-sf-integral-verdier-reduction-tensor-symmetry`).
One of one holes closed; zero holes added; zero split-off statements.
No `sorry` remains in the delivered module.

## No longer needed

The planned direct proof dependency `lem-sf-ringed-derived-native-tensor`
(`Sheaf.CategoryTheory.RingedDerivedTensorNative`) is unnecessary: the supplied
normalization and signed-symmetry representative fields give the needed tensor
models directly, and the existing K-flat resolution theorem supplies the
representatives. It was never imported by this module, and no import is removed.
No module is withdrawn. This only prunes the item's direct DAG dependency; it
makes no claim that other consumers or transitive dependencies are unused.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was mathematically usable. Its reference to native
derived tensor was broader than needed, and it omitted the existing two-factor
scalar-extension extensionality lemma used to implement its generation step.
The node now records that lemma and the actual K-flat resolution and
scalar-reduction/adjunction dependencies. No statement or definition needed
repair, and no target or unit route changed.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralVerdierReductionTensorSymmetry": "8f4bb061b704972800edd444466397932d2e1251"}, "own_failed": ["Sheaf.SixFunctors.IntegralVerdierReductionTensorSymmetry"], "results": {}, "time": "2026-10-28T10:38:48+0800", "transitive": 0, "version": 1}
```

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
