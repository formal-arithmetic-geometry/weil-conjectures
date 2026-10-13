## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_coherent_idealPower_torsionFree_product`
without changing its signature, definitions, original public imports, or docstring.
The proof constructs the existing multiplication image, lifts sections on the complement
by tensoring with a power-ideal section mapping to one, and proves torsion-freeness by
naturality, a zero intersection, and sectionwise injectivity.

Added two proved modules:
- `Sheaf.AlgebraicGeometry.CoherentIdealPowerStableAnnihilator`, containing
  `AlgebraicGeometry.Scheme.Modules.exists_coherent_idealPower_stable_annihilator`.
  This proves the stabilization part of the original argument, including zero ideal
  product and containment of every locally annihilated section. Its private helpers
  prove Noetherian annihilator quasi-coherence by clearing denominators for a finite
  set of affine ideal generators, affine-to-global vanishing and subobject containment,
  and the tensor multiplication range formula.
- `Sheaf.AlgebraicGeometry.CoherentIdealProductIntersectionBound`, containing
  `AlgebraicGeometry.Scheme.Modules.coherent_ideal_product_intersection_bound`.
  This proves the Artin-Rees inclusion for an arbitrary quasi-coherent submodule using
  Mathlib's `Ideal.exists_pow_inf_eq_pow_smul`, a finite affine cover, the existing
  affine intersection inclusion theorem, and gluing. Its proof adapts the already
  proved kernel version to a general monomorphism.

All added imports are proof-only. Updated the original node's proof, proof_deps and
proof_origin, and supplied nodes for the two new public theorems. No existing module
other than the assigned module was adapted. The unit record has empty realized lists;
its statement and proof route are unchanged.

The sources checked were [Stacks 01YB](https://stacks.math.columbia.edu/tag/01YB),
[Stacks 01YA](https://stacks.math.columbia.edu/tag/01YA), and
[Stacks 01Y8](https://stacks.math.columbia.edu/tag/01Y8), together with the existing
annihilator and affine intersection modules and their source docstrings.

## Proved and sorry left

Closed the assigned module's one hole:
`AlgebraicGeometry.Scheme.Modules.exists_coherent_idealPower_torsionFree_product`
(node `lem-pc-coherent-ideal-power-torsion-free-product`).

The two new declarations are also proved:
`AlgebraicGeometry.Scheme.Modules.exists_coherent_idealPower_stable_annihilator`
(node `lem-pc-coherent-ideal-power-stable-annihilator`) and
`AlgebraicGeometry.Scheme.Modules.coherent_ideal_product_intersection_bound`
(node `lem-pc-coherent-ideal-product-intersection-bound`).

No sorry remains in any delivered file; no holes were added or split off. This closes
one hole rather than moving it to another declaration. Existing imported open theorems
remain the project's separate items; this report does not claim the target closure is
axiom-free.

## No longer needed

No original import was removed. The following planned dependencies are no longer
needed by this proof, and were not imported:
- `lem-weil-pbc-coherent-artin-rees` / `Sheaf.AlgebraicGeometry.CoherentArtinRees`:
  the general equality is replaced by the proved fixed-exponent intersection inclusion.
- `lem-weil-pbc-sections-annihilated-by-ideal` /
  `Sheaf.AlgebraicGeometry.SectionsAnnihilatedByIdeal`: only the actual annihilator
  construction and affine criterion are needed; the bundled stalk conclusions are unused.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` /
  `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`: its quotient
  and restriction clauses are unused. The necessary multiplication range calculation
  is proved privately from the tensor and image comparisons.

The proof also does not use `Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorSystem`,
`Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorQuasicoherent`,
`Sheaf.AlgebraicGeometry.AnnihilatorQuasicoherent`, or
`Sheaf.AlgebraicGeometry.ArtinReesAffineComparison`. Their broad interfaces and cyclic
import paths are avoided by the proved narrower arguments. This is pruning for this
item's proof route; other target branches may still require those modules.

The original Noetherian ACC, finite-type ideal, and recursive-power-comparison nodes
remain needed. The complement proof additionally uses the ideal-zero-set and
ideal-power-complement nodes. No statement-level dependency or unit step is removed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct, but two existing APIs cannot be imported here.
`tools/import_direction.py may` rejects both `CoherentArtinRees` and
`IdealPowerAnnihilatorSystem`: their import closures already reach the assigned module.
For example, the Artin-Rees path runs through `ArtinReesAffineComparison`,
`Modules.IdealTimesQuasiCoherentAffineSections`, upstream `Modules.ClosedImmersion`,
upstream higher-direct-image modules, the coherent integral filtration modules, and
`IdealPowerTorsionFreeSectionCarrier` back to this module.

The annihilator path runs through `IdealPowerAnnihilatorQuasicoherent`,
`AnnihilatorQuasicoherent`, and `FinitePushforwardCoherent` into the same higher route.
The delivery avoids both cycles without modifying anyone else's module. The existing
Noetherian ACC and affine intersection inclusion modules have safe import directions.

Edge cases checked against the argument: exponent zero annihilates only zero; the
zero ideal stabilizes at its first power; the unit ideal has zero annihilator; zero
modules are immediate; empty affine covers and empty finite generating sets use
exponent zero and the sheaf axiom. No extra nonempty, proper-ideal, positive-exponent,
or integral-scheme assumption was introduced.

## New nodes

`lem-pc-coherent-ideal-power-stable-annihilator` is the first part of the source
argument: a uniformly killed submodule containing all power annihilators. It has no
complement, high-product torsion-freeness, or restriction conclusion. Its Lean proof
uses actual annihilator subsheaves, Noetherian ACC and the multiplication image;
there is no definition choosing data from an unproved existence assertion.

`lem-pc-coherent-ideal-product-intersection-bound` is the Artin-Rees inclusion for a
general monomorphic submodule and a prescribed exponent. It has no annihilator,
complement, or torsion-freeness assumption or conclusion. It is proved from algebraic
Artin-Rees and the existing affine comparison. Neither new node restates the assigned
theorem. Both have genuine search records in `searches.jsonl` and full source proofs.

No change record is needed: no existing interface, definition, or target changed.

## Second reading by N3

1. **Visibility and unchanged interfaces.** Compared the delivered item module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; the two additional declarations are new split-off nodes documented above. Verdict: pass.
2. **Compilation and proof status.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. Searched the delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and `debug.skip`; none occur (the word “sorry” appears only in prose). Verdict: pass.
3. **Statements and new nodes.** Checked both new theorem statements against their source arguments and edge cases (zero and unit ideals, exponent zero, empty covers/generators). Each is strictly narrower than the assigned target and needed by its proof, with a matching DAG node and source/proof record; neither duplicates an existing library theorem. Verdict: pass.
4. **Pruning and route.** The proof follows the existing unit route through stabilized annihilators, multiplication images, the complement, and the intersection inclusion. Imports are proof-only additions; no original public import was removed, and the report records unused planned dependencies and avoided cyclic modules. Verdict: pass.
5. **DAG agreement.** Updated proof, proof dependencies, and proof origin agree with the Lean proof; the new node `lean` records match their declarations. The unit statement and route remain unchanged. Verdict: pass.

I changed only this report section after the first delivery dry run, then re-ran the delivery checks.
