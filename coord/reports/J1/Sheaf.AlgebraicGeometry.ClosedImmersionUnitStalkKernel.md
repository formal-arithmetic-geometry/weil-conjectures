## What changed

Proved `AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_stalk_kernel` with its
signature unchanged. The proof combines the existing tensor multiplication stalk range
formula with two new, fully proved intermediate theorems. Proof-only imports are
`StalkTensorMultiplicationRange`, `ClosedPushforwardStalks`,
`ClosedImmersionIdealStalkRange`, and `ClosedImmersionUnitStalkKernelOnImage`.
All original public imports remain needed by the statement or its monoidal instance.

`ClosedImmersionIdealStalkRange` computes the ideal stalk directly on affine germs,
both on and off the closed image. `ClosedImmersionUnitStalkKernelOnImage` uses the
canonical pullback and pushforward stalk comparisons, tensor right exactness over
the surjective local ring map, and adjunction uniqueness. Both new modules contain
complete proofs. The structure-module stalk identification in the main module is
a proved private helper, following the inaccessible private helper in
`IdealModuleProductStalk`; importing that larger product-and-powers theorem is unnecessary.
The existing node and two new node records match these proofs.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_stalk_kernel`
(node `lem-weil-pbc-closed-immersion-unit-stalk-kernel`).

Also proved both new declarations:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_ideal_stalk_range` and
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_stalk_kernel_on_image`.
There are no remaining or added `sorry`s in any delivered module; zero holes split off.
This is a proof, not a decomposition into new unproved statements.
The zero module, identity immersion, empty immersion, and points outside the image are
included; the off-image branch is an explicit proof using a subsingleton pushforward stalk.

All three modules compile together through `lcompile.py --all`, without warnings.
The delivery dry run printed OK: compilation and preflight passed, except for the
second reading reserved for the next worker. Nothing was pushed.
The resumed worker recompiled the inherited complete attempt against the current library,
checked the proof and node interfaces, corrected the pruning report, and explicitly disabled
auto-implicit variables in both new modules.

## No longer needed

Removed the original proof-only direct import
`Sheaf.Algebra.Homology.ModuleStalkExact`. Also moved the original proof-only import
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` into the new on-image lemma module,
where its comparison is used. Every original public import is retained for the
unchanged statement or its monoidal structure. In particular `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
provides the scheme-module monoidal instance used in the statement.

Pruned the planned proof dependency `lem-weil-pbc-module-stalk-exact`
(module `Sheaf.Algebra.Homology.ModuleStalkExact`) from this node's proof route:
the ideal-stalk calculation is proved directly by affine germ representatives.
It was a direct import of the original item. No claim is made that
other target branches stop reaching it. No other planned dependency is discarded:
closed pushforward stalks, the ideal sheaf, closed immersion, tensor multiplication,
pullback stalks and tensor pullback are used directly or by the proved intermediate modules.
No import of `IdealModuleProductStalk`, `IdealModuleMultiplicationStalkRange`, or
`StalkImageRange` is needed; multiplication itself is handled by
`StalkTensorMultiplicationRange` without passing through a categorical image.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or existing signature was changed. The planned use of stalk
exactness was unnecessary. The existing proof dependencies did not themselves identify
the geometric unit kernel or the stalk ideal: the two new lemmas supply those comparisons
with complete proofs. Sources read: Stacks 08KS and 0098, together with the current
`ClosedPushforwardStalks` and `TensorPullbackStalk` interfaces. LeanSearch was unavailable
(Internal Server Error); LeanFinder, Loogle, source grep and the imported blueprint search
were used. The existing node's `created.item` is a module name, so the automatic
blueprint ancestor traversal returns none; the new records preserve the intended ancestry
through the closed-immersion quotient dictionary to `thm-weil-pbc-finite-etale-lifting`.

## New nodes

`lem-weil-pbc-closed-immersion-ideal-stalk-range`, module
`Sheaf.AlgebraicGeometry.ClosedImmersionIdealStalkRange`: fully proved equality of the
ideal stalk range with the local ring kernel on the image and top outside it. It is
independent of a coefficient module and of tensor multiplication.

`lem-weil-pbc-closed-immersion-unit-stalk-kernel-on-image`, module
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitStalkKernelOnImage`: fully proved kernel
calculation using only the local ring kernel and the unit; it neither mentions nor
assumes the ideal multiplication result. Its algebra helper is proved from Mathlib
right exactness. No change records or forced adaptations are needed.

## Second reading by J1

1. I compared the delivered item module with the repository version. The target
   declaration signature and all existing declarations are byte for byte unchanged;
   only proof imports, a private helper, and the target proof changed. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`. There are no
   `sorry`s, axioms, unsafe declarations, or hollow definitions. The proofs use only
   the permitted classical and quotient axioms. Verdict: pass.

3. I checked both split-off statements against the affine germ and tensor
   right-exactness arguments, tested image and off-image branches (including empty,
   identity, zero-module, and zero-ring cases), and searched the library for duplicate
   declarations. Both statements are true and strictly simpler than the parent.
   Verdict: pass.

4. I checked the proof from the target downward. The route uses the stalk tensor
   multiplication range, closed-pushforward stalk comparison, the closed-immersion
   ideal stalk calculation, and the on-image unit-kernel lemma. The former stalk
   exactness import is genuinely unnecessary and was pruned. Verdict: pass.

5. I checked the parent and new DAG records against the Lean declarations and the
   realized unit route. The parent proof and dependency fields follow the actual
   proof, and both new nodes carry complete sources, proof steps, searches, and Lean
   records. Verdict: pass.

I changed the report only by adding this second-reading record. No Lean or DAG repair
was needed after the checks above.
