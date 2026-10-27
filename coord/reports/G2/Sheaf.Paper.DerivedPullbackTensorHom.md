## What changed

Reduced `WeilConjectures.rationalDerivedTensor_existsUnique` to the separate
constant-scalar bilinearity of the actual normalized integral completed tensor.
The original theorem signature, every existing definition, and every existing
public import are unchanged. The two new imports in the item are the private
proof imports `Sheaf.Paper.IntegralCompletedTensorBilinear` and
`Sheaf.CategoryTheory.BilinearScalarLocalization`.

The new proved generic construction explicitly extends any given bilinear
bifunctor action with `TensorProduct.lift`, `LinearMap.baseChange`, the inverse
`distribBaseChange` equivalence and currying. Its objects are the literal original
integral outputs. Its pure-tensor formula is proved, not assumed. Four tensor
inductions prove the composition law; the identity law uses the original
functor's identity law. Uniqueness uses functor extensionality with the prescribed
object transports, then two tensor inductions and the specified HEq generator
formula. The generic theorem is
`CategoryTheory.ScalarLocalization.bilinearFunctor_existsUnique`; it has no
remaining hole. A private lemma restricts ambient integral bilinearity to the actual
constructible full subcategories by their Hom linear equivalences.

Added the single prerequisite theorem
`WeilConjectures.integralCompletedTensor_bilinear` in its own module and node.
It concerns only the integral arrow action; it asserts neither existence of a
rational functor nor any localized functor laws or uniqueness. It is strictly
one step of the integral-to-rational argument. The theorem determines its
bilinear map on every input arrow, so choices from it determine that map uniquely.
The docstring explains finite reductions, tensor balancing, Roos coordinates,
localization and normalized descent. Zero maps, zero scalars, zero objects and
torsion inputs require no cancellation or flatness hypothesis on the inputs.

Searches used leanfinder for bilinear functor localization, loogle for
`TensorProduct.curry`, leansearch for derived tensor linearity, and grep over
Mathlib and both project roots. The results give the ordinary tensor/base-change
API used in the proof, but no bilinearity theorem for this normalized completed
tensor. `DerivedCompletedTensorBilinearity` uses a different reflector-based
model. `CompletedTensorScalarLinearity` proves first-variable scalar preservation
on constructibles, but imports the item and cannot be imported back; it also
lacks separate additivity and second-variable scalar preservation.

## Proved and sorry left

The item initially had four holes. Its
`WeilConjectures.rationalDerivedTensor_existsUnique` hole is closed by a complete
Lean construction from the new integral prerequisite. This is a decomposition,
not an axiom-free proof: one upper hole closed, one strictly smaller lower hole
added, net hole reduction zero.

The three unchanged holes in the item, all attached to
`def-weil-derived-pullback-tensor-hom`, are:

- `WeilConjectures.commonStageDerivedPullback_existsUnique`;
- `WeilConjectures.commonStageDerivedTensor_existsUnique`;
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.

The only added hole is
`WeilConjectures.integralCompletedTensor_bilinear`, attached to
`lem-sf-integral-completed-tensor-bilinear` in
`Sheaf.Paper.IntegralCompletedTensorBilinear`.
The new public
`CategoryTheory.ScalarLocalization.bilinearFunctor_existsUnique` is fully proved.
There are no holes in the new generic scalar-extension construction or in the
restriction to constructible endpoints. No existing proof has been replaced by
sorry, and no hole has been added inside a definition or private declaration.

Validation: all three final modules compiled cleanly and passed the remote per-file
compilation gate, with no errors, warnings or remaining profiling options.
The first parent compile exposed a simplification issue in the pure-tensor lemma;
writing its input spaces as explicit tensor modules fixed it. A profiling run
then compiled the complete construction successfully within the enforced limit.
The first final delivery attempt then took 64 s and was refused without a push.
After the tensor-coordinate definition had already been improved, the fully proved
generic portion was extracted into its own module, preserving its complete proof
and the original item interfaces. All profiling options have been removed; the
final delivery recompiles this revised set and runs the required preflight and
axiom probes. Static checks confirmed exact
new-node/signature agreement, line widths, proof-dependency unions and absence
of a new prerequisite dependency path back to the parent.

## No longer needed

None. No existing imports or DAG dependencies are removed. The original five
proof dependencies remain used by the existing pullback, Hom and comparison
proofs; module base change and scalar-localization composition also serve the
new tensor proof. The rational tensor reduction requires no common-stage
coherence theorem, but the three common-stage declarations and their statements
remain in the item. No node or module is withdrawn and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current blueprint node is now at
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/`
`sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md`.
It defines all coefficient cases uniformly using pulled-back condensed rings,
and explicitly no longer defines the adic operations from finite reductions.
The assigned Lean module and the existing node's primary statement instead
retain the older finite-reduction/Roos, rational-localization and common-stage
construction. This mismatch is already represented by the node's
`blueprint_update`. This delivery preserves the assigned Lean statements and
reports that it proves part of that legacy construction; it does not resolve or
silently overwrite the mathematical-interface migration.

The existing node's proof plan described the rational tensor hole as unfinished
and had no standalone integral completed-tensor bilinearity declaration.
The new node supplies exactly that missing integral prerequisite. The existing
pullback and Hom routes remain intact; the tensor steps have been appended and
the obsolete claim that rational tensor is still unfinished has been removed.

## New nodes

`lem-sf-integral-completed-tensor-bilinear`: separate constant-valuation-ring
linearity of the existing normalized ambient completed tensor's arrow action.
Source: the K-flat tensor construction in Stacks, `sites-cohomology.tex`, flat
resolutions (including Tag 06YS), and the existing normalized finite-reduction/Roos
construction in `def-pur-integral-derived-operations` and
`lem-pur-integral-operations-well-defined`. The detailed proof and actual searches
are recorded in the node and docstring. This is the integral step only; all
scalar extension and localized categorical laws are proved in the parent.
`lem-pc-kflat-resolution` is used as a generic tool for flat-term K-flat
representatives, as already done throughout the integral construction, not as a
replacement for a unit step. No change record is needed: no existing public
interface, definition body, instance or attribute has changed.

`lem-sf-bilinear-functor-scalar-localization`: the fully proved generic extension
of an arbitrary bilinear functor to the raw scalar-localized category, with literal
objects, the pure-tensor formula, functor laws and uniqueness. It is extracted
from the proof already checked in the item, after the concrete item exceeded the
60 s final gate despite the definition improvement. It introduces no sorry and
requires only the existing module-base-change and scalar-localization composition
API. Its module is `Sheaf.CategoryTheory.BilinearScalarLocalization`.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
