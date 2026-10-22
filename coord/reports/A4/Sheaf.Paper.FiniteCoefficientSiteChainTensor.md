## What changed

Proved `WeilConjectures.finiteHomNuChainTensor_existsUnique` by specializing a normalized
tensor comparison for finite coefficient rings. Added two proved results: the ordinary
intrinsic comparison preserves pure tensors, and its termwise extension preserves signed
total tensors with the unique generator normalization. Both new modules have matching DAG
nodes. No adopted source library module is modified.

The ordinary proof combines the strong monoidal site inverse image, the sectionwise
constant-module encoding, and the existing normalized scalar module-sheafification tensor
comparison. The chain proof uses the total-bifunctor comparison and its summand identity.
Uniqueness follows from coproduct extensionality and the two adjunctions, then etale
tensor-generator extensionality.

Replaced the body of `FiniteHomNuChainTensorNormalization` by the equivalent categorical
summand normalization through the ordinary comparison API. Its complex and isomorphism
arguments are inferred from the generic API. The published tensor-existence instances
supply the implicit totalization arguments, which are propositions. The canonical
isomorphism retains its original explicit type. The old witnesses are fixed by their
heterogeneous equalities. The new summand identity implies the resulting local generator
equation by naturality and the ordinary tensor formula. Conversely, the two adjunctions
and tensor extensionality recover the summand maps from those local generator equations.
The change record includes the old and new bodies and users. The termwise functor has an
explicit annotation of its existing inferred type. The canonical isomorphism is still
chosen from its unique normalized existence statement. The original scalar-arrow public
import remains; the new chain API is public because the normalization definition uses it.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.finiteHomNuChainTensor_existsUnique` (node
`def-sf-finite-coefficient-site-chain-tensor`).

The two new results are proved in this delivery:
`AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicTensor_generators` (node `lem-sf-
finite-intrinsic-tensor-generators`) and
`AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicChainTensor_existsUnique` (node
`lem-sf-finite-intrinsic-chain-tensor-generators`). Every private helper is proved. No new
holes or unfinished split results are introduced. Existing dependency theorems are used
with their published statements, including etale tensor existence and scalar-
sheafification tensor comparison.

## No longer needed

No original import, declaration, module, or node is withdrawn. The new chain proof does
not need `TensorColimitsIndependentCoefficients`: it uses coproduct preservation of the
comparison functor, rather than a tensor-colimit theorem. The item's original node had no
numbered proof or proof dependencies. Its statement dependencies and unit route are
retained.

`IntrinsicRealizationTensorComplex` and `ProEtaleIntrinsicTensorComparison` are not
imported: their existence results do not expose the pure-tensor equation required here.
They remain in the library; no claim is made about their other consumers.

## Where the brief, the DAG or earlier work was wrong

The original node described the construction but had no numbered proof route. The ordinary
normalized comparison is a separate tensor-sheaf result; bare existence of some tensor
isomorphism does not determine the required map on sections. The new chain result also
retains the normalization rather than merely an abstract tensor isomorphism.

Large inferred types in the existential normalization repeatedly unfolded the termwise and
total-complex constructions during kernel checking. Typed section maps, the equivalent
categorical predicate, and a proof of the total summand equation provide an API for those
constructions. No mathematical hypothesis or conclusion is weakened. Empty schemes, zero
complexes and the zero finite ring remain included; no flatness or boundedness is
introduced.

## New nodes

`lem-sf-finite-intrinsic-tensor-generators` records the ordinary normalized tensor
comparison, using Stacks 0GMW and 03EK. Its statement works for arbitrary commutative
rings; the chain result uses the finite realization equivalence and its additivity to pass
to totalization.

`lem-sf-finite-intrinsic-chain-tensor-generators` records the signed-total comparison for
finite rings normalized by the ordinary comparison on every summand, using Stacks 03EK and
06YN. It uses the two proved zero-map instances to form the totalization. The coefficient
item supplies finiteness; its representative-data formula identifies the normalization
with the original recorded local generators. Both nodes' statements are proved here, with
zero postponed lemmas.

Change record: `coord/changes/finite-hom-nu-chain-tensor-normalization.md`.

Validation: both new modules, the assigned item, and the unchanged direct consumer
`FiniteCoefficientSiteHomArrow` compile through `lcompile.py`. The chain module took 44.9
seconds, the item 57.0 seconds and the consumer 32.2 seconds. The consumer was checked
from an identical sandbox copy and is not delivered.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
