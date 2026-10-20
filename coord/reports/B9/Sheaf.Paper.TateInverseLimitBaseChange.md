## What changed

Proved all twelve original holes in `Sheaf.Paper.TateInverseLimitBaseChange`.
The limit comparison uses `limit.post`, `limMap`, and projection uniqueness.
The tensor comparison uses the sectionwise extend/restrict-scalars Hom equivalence,
module sheafification, and the canonical inverse-image adjunction. Finite quotient
modules are constructed by factoring the scalar representation through the
surjective quotient map, then extending the action along the constant-sheaf unit.
The finite square follows on adjunction units of pure tensors. The identity and
composition laws use the existing normalized identity mate and the unchanged
`exchangeModuleComposition` used by `tatePullbackComp`.

All 35 existing public declaration signatures, all existing public definition
bodies, and all public imports are preserved. Added proved private helpers and
one proof import, `Mathlib.Algebra.Module.Hom`. A local irreducibility attribute
keeps the private inverse tensor construction folded after its API is proved;
explicit module arguments and the direct sheafification Hom equivalence avoid
expensive elaboration. No public interface or other module is changed.
The node's proof, proof dependencies, and proof origin now describe this route.
Preflight additionally requires a record for the private instances and added
local commands: `coord/changes/B9-tate-base-change-proof-commands.md` documents
their scope and the zero-consumer downstream check. No consumer is adapted.

## Proved and sorry left

Closed 12 of 12 original holes, all in namespace `AlgebraicGeometry.Scheme`
and node `lem-pur-tate-inverse-limit-base-change`:

- `tateInverseLimitBaseChange`
- `tateTensorMap_existsUnique`
- `tateReduction_existsUnique`
- `tateFinitePresentation_exists`
- `tateInverseLimitFiniteTensorBaseChange`
- `tatePullbackId_existsUnique`
- `tateLimitMap_id`
- `tateLimitMap_comp`
- `tateTensorMap_id`
- `tateTensorMap_comp`
- `tateFiniteAlgebraMap_existsUnique`
- `tateInverseLimitCanonicalFiniteTensorBaseChange`

Zero holes remain, zero holes are added, and zero statements are split off.
The complete module compiled via `lcompile.py`; final validation is recorded by
the delivery tool. Existing imported theorem holes remain the project's stated
proof dependencies, rather than new holes of this delivery.

## No longer needed

Removed these four proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`

The proof does not use `det-pe-topos-functoriality-inverse-image` or
`lem-pur-proetale-inverse-image-tensor-comparison`; these are removed from this
node's proof dependencies, and the obsolete top-level tool-use approval for
`det-pe-topos-functoriality-inverse-image` is withdrawn. The former would supply
an additional compositor, whereas the existing public definition already uses
`exchangeModuleComposition`; its normalization suffices. The latter addresses
a different tensor presentation: the Hom equivalence proves the needed scalar
extension formula, its uniqueness, and coherence directly. No cochain tensor
or monoidal structure is used. The inverse-image declarations are already
available through retained public imports, so their additional proof import
is redundant. These are local dependency removals; no claim is made that their
modules leave every target's transitive import closure. No modules are deleted.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed, and no target or existing definition was changed.
The planned abstract tensor-comparison dependency was unnecessary for the
scalar-extension tensor used in this item. The unit record has no realized
statement or steps, and this proof implements the node's limit, finite square,
and coherence conclusions using the same canonical public comparisons.

The retained earlier report described unverified partial work; it is replaced
by the completed proof and actual zero-hole count. The interrupted provider
calls did not deliver anything. Some initial requests received no compile-server
answer; later timeouts were repaired by explicit arguments and abstraction
barriers, without increasing the server's time limit or splitting the module.
The completed packet passed two dry-run compile/axiom checks and server preflight.
A subsequent push attempt timed out before pushing; a profiling copy of the same
final source then compiled in 34.1 seconds, with costs spread across typeclass
inference, tactics, kernel checking, and linting. No profiler options are retained
in the delivered module, and the compilation limit is unchanged.

The resumed dispatches rewrote the reference-clock metadata: retained attempt
markers are `.brief2`, `.brief3`, `.brief4`, and `.brief5`. The original session
start was 2026-10-19 16:05 UTC, while the retained reference start is
2026-10-19 18:21 UTC. No budget or launcher file was edited by this worker.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
