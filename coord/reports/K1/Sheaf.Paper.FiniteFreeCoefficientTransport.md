## What changed

Completed the three theorem proofs in
`Sheaf.Paper.FiniteFreeCoefficientTransport`, retaining every existing public
signature, definition, import, and coefficient presentation. Added one private
proof import, `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, for
`proEtaleConstantInverseImageMap_naturality`.

The quotient kernel is a direct application of the existing
`WeilConjectures.integralScalar_quotient_kernel`: the actual datum's ideal is
definitionally its uniformizer ideal. The completed map comes from the natural
transformation of strict finite quotient systems and Mathlib's limit functor.
Its projection equations and uniqueness are `limMap_π` and `limit.hom_ext`.

For naturality, private proved helpers identify the specified finite constant
comparison with sheafified constant functions and show that it commutes with
every quotient ring homomorphism. Naturality of the canonical constant inverse
image then gives the finite coefficient square. The completed square follows
on each limit projection, and adjunction-unit naturality gives the required
direct-image square after forgetting commutativity. No inverse image is assumed
to preserve a limit in this argument.

Updated the item's existing node
`def-weil-pbc-actual-finite-coefficient-transport` with these proof steps and their
actual dependencies. No other module or public interface changes.

Searches: Lean Finder for the unique map of inverse-limit coefficient sheaves
returned general gluing and condensed-sheaf facts, with no exact coefficient
transport theorem. Loogle for `CategoryTheory.Limits.limit.lift` returned the
limit construction and projection API used here. The launcher's grep search
returned no hits; direct `rg` on the adopted and statement libraries found the
already proved integer kernel and the analogous lifted construction in
`PbcScalarExtension`. That construction uses different ULift coefficient types;
this proof applies the same elementary limit argument to the specified actual
rings. The canonical finite inverse-image naturality theorem is reused directly.

## Proved and sorry left

Closed all three original holes, all attached to
`def-weil-pbc-actual-finite-coefficient-transport`:

- `AlgebraicGeometry.Scheme.finiteFreeCoefficientQuotientKernel`.
- `AlgebraicGeometry.Scheme.finiteFreeCompletedCoefficientMap_existsUnique`.
- `AlgebraicGeometry.Scheme.finiteFreeCompletedCoefficientMap_naturality`.

Holes added: zero. Holes remaining in the item: zero. Split-off statements: none.
All newly added helpers are private and proved. Imported theorem dependencies
retain their own independently tracked proof status.

## No longer needed

None. All three original public imports supply the unchanged statements and
constructions. No import, DAG node, module, parent dependency or unit route is
withdrawn. The existing lifted coefficient construction is not substituted for
the supplied actual valuation rings.

## Where the brief, the DAG or earlier work was wrong

The item's definition node had empty `proof` and `proof_deps`, although its module
contained three named theorem holes. Its declaration docstrings describe the
correct elementary argument; the node now records that argument precisely.
There is no mathematical statement correction or definition repair.

The argument allows n = 0, ramified extensions, identity embeddings and empty
schemes: it uses only the existing kernel inclusion, ring-homomorphism
composition, adjunction naturality, and universal properties, with no added
nonemptiness or unramifiedness assumptions. The canonical choice of completed
map is now justified by the proved uniqueness theorem, and all scalar and
restriction definitions keep their existing normalizations.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
