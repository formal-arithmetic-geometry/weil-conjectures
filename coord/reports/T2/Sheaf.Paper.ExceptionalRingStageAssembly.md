## What changed

The item now constructs the finite and integral operations, their ambient left
realizations, the specified finite exceptional realization, the prescribed integral
compact-support identification, and the displayed integral normalization. It uses
`exists_sfFiniteExceptionalOperations` and the smaller integral preservation/
right-adjoint assertion `exists_integral_support_adjoint`. The integral left
functor is the actual full-subcategory lift of ambient compact support; its right
adjoint is chosen by its universal property, not as an arbitrary witness.
Left shifts are inherited through the full ambient inclusion; triangulatedness is
reflected through that inclusion. The right adjoint receives its adjoint shift,
which gives exactness and shift-compatible units and counits.

Scalar composition records are constructed by lifting the ambient
tensor associator through the fully faithful target
inclusion. Their normalization equations follow from the map/preimage identity.
These constructions apply to the supplied scalar realizations and require no
additional geometric hypothesis.

`Sheaf.Paper.ExceptionalRingScalarMates` states the remaining scalar-only step for
already constructed operations with shift-compatible ambient realizations. It
supplies endpoint scalars, their finite/completed normalizations and the normalized
counit mates, together with normalized scalar identity records. The item combines
this statement with the proved constructions;
it constructs the operation records from the finite theorem and the integral
left-adjoint predicate, and proves tensor composition.
Existing public signatures, definitions and public imports are unchanged. All three
modules compiled together through lcompile; the only reported warning was a long
docstring line, since wrapped. The operation construction and scalar composition
also compiled in a focused probe. No shared module was adapted.

## Proved and sorry left

Closed in the item:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_stage_assembly`
(node `lem-sf-ring-stage-assembly`). The item has zero remaining textual holes.

Added two holes:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_integral_support_adjoint`
(node `lem-sf-integral-support-restricted-right-adjoint`), and
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_scalar_mates`
(node `lem-sf-ring-scalar-mates-for-realized-operations`). Each whole proof is
`by sorry`, in a separate new module, with the source and proof steps in its docstring
and node. No definition or private helper contains a hole.

This is a decomposition: one upper hole closed and two strictly smaller
holes added, net minus one. It proves the finite/integral operation and realization
construction and the scalar associator construction; it does not claim a
sorry-free geometric proof of the whole assembly.

## No longer needed

No original import is removed, and no module is withdrawn or claimed globally
pruned. The item's direct proof dependencies on finite scalar mates, system
transport and the higher integral reconstruction/scalar interfaces are replaced
by lower normalized reconstruction, finite-free completed scalar comparison and
proper/open system realization in the two smaller nodes. Finite scalar mates and
system transport remain needed. The higher reconstruction and integral-scalar
records (Sheaf.SixFunctors.ExceptionalIntegralReconstruction,
lem-sf-exceptional-integral-reconstruction;
Sheaf.Paper.ExceptionalIntegralScalarMates,
lem-sf-exceptional-integral-scalar-mates) are not needed on this route because
their shift-data dependencies return
to the assembly. This is not a global module-pruning claim. Finite operation bounds
remain part of the existing theorem; the assembly uses its supplied operations,
rather than introducing further bounds.
No rational, closed-coefficient or refinement module is imported by this proof.

## Where the brief, the DAG or earlier work was wrong

The integral reconstruction module imports IntegralExceptionalInverseImage,
which imports the higher coefficient assembly and hence this item: a direct
import closes a cycle. FiniteTorStability also reaches this item. The former
module is held by Z9, so its unrelated public interface cannot be refactored in
this delivery. The new integral lemma isolates only preservation and existence
of a right adjoint to the fixed ambient functor, keeping its actual lift,
realization, shifts, exactness and tower normalization in the proved assembly.

The dependencies do supply the advertised geometric statements, but their records
are not interchangeable. In particular the scalar-mate theorem asks for
`ExceptionalIntegralScalar.Transported`, with equality-normalized reconstruction,
while integral reconstruction supplies its own systems and realization record.
The remaining scalar lemma includes that change of presentation and the choice
of the same endpoint scalars for every compactification. It assumes existing
operations and constructs only scalar data; it does not restate their existence.

The finite exceptional presentation is also not definitionally the specified-c
right adjoint: sfFiniteExceptional chooses a compactification from the proof of
HasCompactification, and this choice need not equal c. The proof uses
Etale.rightDerivedLowerShriekIso, transports the adjunction and applies
rightAdjointUniq, then whiskers by the site and intrinsic-coordinate functors.
This is the existing unbounded comparison result
`lem-amb-unbounded-compact-support-comparisons`, used as a tool; no new
compactification-comparison statement or hole is added.

The finite ambient proper/open realization also uses a different named
presentation from `sfIntrinsicCompactSupport`; the proof explicitly composes its
published comparison rather than identifying these presentations by name.

Edge cases retained: empty schemes and compactifications, residue coefficient
level, arbitrary nonflat allowed quotients, distinct ramified exponents, arbitrary
integer shifts, both endpoints, and no absolute separatedness of X or Y. Scalar
composition is proved for any actual coefficient-map equality; identity normalization
is retained in the scalar-only subproblem. A separate concrete identity construction
ran into kernel timeouts; it is not included among the proved parts.

## New nodes

`lem-sf-ring-scalar-mates-for-realized-operations` is the scalar restriction and
counit-mate part of ring assembly, with the operations and ambient realizations
supplied as inputs. It adds normalized scalar unitors but neither operation
existence nor scalar associators. Its proof follows the finite and integral scalar constructions, full
inclusion, right-adjoint uniqueness, system evaluation and ramified cofinal
reconstruction. Searches of the DAG and current blueprint found no equivalent
node with this input/output separation. LeanSearch found sheaf/module scalar
adjunctions; Loogle found `Adjunction.rightAdjointUniq`; Mathlib grep found no
ring-stage scalar assembly theorem. The generic tools do not provide the geometric
normalization and preservation assertions.

`lem-sf-integral-support-restricted-right-adjoint` isolates the one-stage
integral geometric existence step. It supplies only a preservation proof and
the left-adjoint predicate for a fixed functor. The finite system adjunction,
uniform bounds, normalized reconstruction and full-faithful transport prove it.
The same mathematical conclusion is implicit in integral reconstruction, but
its current module import creates the cycle documented above. LeanFinder found
only condensed-category adjunctions, Loogle the generic adjoint-choice API, and
Mathlib grep no integral constructible compact-support adjunction.

The new nodes use the lower tools
`lem-pur-normalized-reconstruction-adjunction-calculus` and
`lem-weil-finite-free-completed-scalar-comparison` from the purity unit: the first
provides the actual reduction/total-limit equivalence and its adjunction transpose
formula, and the second identifies the published completed scalar functor. These
are the same underlying tools used in the original integral route, without its
cyclic shift-data interface. No tool approvals were added by the worker.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
