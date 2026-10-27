## What changed

Repaired `AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_compatibility`:
the old signature asserted a false equality for arbitrary unnormalized tensor and
pullback isomorphisms. The replacement constructs the tensor comparison and uses the
canonical coefficient pullback comparison. Its proof descends the normalized chain
comparison, checks the representative diagram explicitly, and reflects equality by
fully faithful restriction to flat K-flat representatives.

`Sheaf.Paper.ProEtaleCoefficientPullback` houses the existing `identityRestriction`
and `pullback` definitions, moved verbatim with the same fully qualified names and
bodies, their ordinary/chain comparisons, and the proved localization factorization.
The existing parent `Sheaf.Paper.ProEtaleCoefficientTensorTransport` publicly imports
this support module and applies the repaired theorem. Its theorem statement is unchanged.
The ring-isomorphism transport module remains a proof dependency: it is not newly
publicly exported by the parent or compatibility module.

## Proved and sorry left

The original module had one `sorry`, in the false universally quantified statement
`AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_compatibility`.
That false statement is repaired, not counted as proved. The normalized replacement
has a complete Lean proof from the imported chain-square lemma. The existing parent
`AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison` has a complete
proof of its unchanged statement.

The delivery adds one hole, named
`AlgebraicGeometry.Scheme.CoefficientTensorChain.restriction_tensor_chain_square`,
node `lem-pbc-coefficient-restriction-tensor-chain-square`. This is a decomposition and
statement repair, not an unconditional proof of the original false signature.
It asserts only an equality of specified chain maps for a transport already normalized
on pure tensors and totalization summands. Existence of that transport and preservation
of flat K-flat representatives are proved by the existing `ringIso_tensor_transport`.
The ordinary fields of that transport are all the chain-square calculation uses.

`AlgebraicGeometry.Scheme.CoefficientTensorTransport.pullback_factors` is proved from
the exact-derived identity, composition and natural-isomorphism normalization equations;
it adds no hole. The auxiliary
`AlgebraicGeometry.Scheme.CoefficientTensorChain.tensorIso_naturality` is proved from
`RingIsoTensorTransport.total_naturality` and the specified total tensor-map formula.
`AlgebraicGeometry.Scheme.CoefficientTensorTransport.pullback_pair_factors` and
`AlgebraicGeometry.Scheme.CoefficientTensorChain.restriction_tensor_localized_square`
are proved product/localization consequences. The representative calculation is
proved in `Sheaf.Paper.ProEtaleCoefficientTensorRepresentativeSquare`, theorem
`AlgebraicGeometry.Scheme.CoefficientTensorTransport.representative_square`;
this module split keeps each kernel check within the per-file budget.
The new tensor isomorphism is constructed from the proved transport; no data is
chosen from the unproved chain square. There are no holes inside definitions or
private declarations.

Compiler validation: the final clean compile passed without warnings. Timings were
28.1 s for coefficient pullback, 44.3 s for chain data, 58.7 s for the representative
square, 18.1 s for the item, 6.6 s for its adapted parent, and 19.7 s for the unchanged
direct consumer `Sheaf.Paper.CompletedTensorProjectionCoefficientTransport`.
The unchanged consumer was byte-compared to the current repository source and its
temporary verification copy removed. No profiler settings remain.

## No longer needed

Removed the parent's proof import
`Sheaf.Paper.ProEtaleCoefficientTensorComparisonExists` and its dependency
`lem-pbc-coefficient-restriction-tensor-comparison-existence`. The old proof chose an
arbitrary tensor isomorphism and then used an invalid universal compatibility assertion.
The replacement constructs the normalized isomorphism and proves its square together.
A recursive import comparison rooted at the parent removes precisely this one existing
module; its file and proved declaration remain untouched.

The item's old direct dependency `lem-weil-pbc-site-derived-tensor-descent` is replaced
by the already proved representative-descent and fully-faithful-whiskering APIs. This
is not a claim that the general site tensor descent module disappears transitively.
The geometric tensor comparison and coefficient adjunction nodes remain needed. No unit
statement or unit proof step is bypassed. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old signature universally quantified arbitrary rho and b.
Even with b fixed, replacing rho by its negative negates just the right-hand side.
Over integer coefficients on a nonempty geometric point, evaluated at degree-zero
rank-one modules, that composite is an isomorphism distinct from its negative.
The old docstring called rho normalized but its type recorded no normalization.
The parent's existence lemma likewise returned only an isomorphism, without a
normalization equation. Its valid existence conclusion cannot justify that application.
The repair keeps the parent's actual goal and constructs a comparison with the needed
normalization instead. The change is recorded in
`coord/changes/J1-coefficient-tensor-normalization.md`.

The remaining chain square uses the independent-universe sheaf tensor presentation;
a bilinear universal property restricted to equal site object/Hom universes would
not directly apply on this pro-etale site. Its edge cases include c the identity,
zero rings, zero complexes, empty sites, and unbounded complexes: no nonzero or
boundedness assumption is used by the pure-tensor and coproduct argument.

## New nodes

`lem-pbc-coefficient-restriction-tensor-chain-square` is the one remaining source
step. Its module contains the normalized natural chain tensor isomorphism constructed
from the proved ring-isomorphism transport, followed by the equality of its chain maps
with the two ordinary geometric tensor comparisons. No arbitrary derived input or
derived tensor-model compatibility equation appears in its conclusion.

`lem-pbc-coefficient-pullback-factorization` records the proved factorization of the
canonical derived pullback comparison on every complex. Its support module also owns
the two moved definitions and the ordinary and termwise comparisons. It is a proved
node, not another split-off hole.

`lem-pbc-coefficient-restriction-tensor-representative-square` records the proved
calculation on flat K-flat pairs, conditional on the normalized comparison already
constructed by descent. It makes no existence assertion and says nothing about
arbitrary derived inputs. It adds no hole; it separates the representative diagram
from the descent and equality-reflection steps to meet the per-file compile limit.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
