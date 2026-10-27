## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.spRootBasisLevel` by an explicit
normalized linear map on the given slice and a proof that it is invertible.
The theorem signature, public import, coefficient objects, module actions, root
module and unit route are unchanged. Only this module and its own DAG node change.

The map sends each section `b` to the specified image of `b tensor zeta` in the
actual integer sheaf tensor. Lax monoidal naturality and associativity prove
linearity for the specified integral coefficient action. The coefficient quotient
is killed by `ell^(n+1)` at the point; additivity of its actual inverse image
carries this identity to X. For any group A killed by N, the map
`A -> A tensor_Z ULift(ZMod N)`, `b -> b tensor 1`, is explicitly bijective:
the inverse sends `b tensor a` to `a.down` acting on b. Integer representatives
prove both inverse identities. Tensor the constant cyclic sheafification unit
with the coefficient presheaf, restrict to the slice, tensor the supplied basis,
and apply the sheaf tensor comparison. These maps are locally bijective. Their
composite is exactly the constructed map because the unit sends 1 to 1 and
`he` sends 1 to the restricted zeta. A locally bijective map of sheaves is an
isomorphism, and the module forgetful functor reflects isomorphisms.

All auxiliary declarations are proved private helpers in the item module. The
Mathlib APIs are already available through the existing public import closure,
so no import is added. No new module, public declaration, definition repair,
change record, or consumer adaptation is required.

The complete proof passed server single-file compilation without errors or
warnings in 24.4 seconds, below the 60-second limit. The two redundant private
Mathlib imports were then removed after checking that both occur in the existing
public import closure; delivery checks compile this exact final packet again.
The original theorem signature was compared verbatim, all lines fit within
100 characters, and the only changed node fields are proof, proof_deps and
proof_origin.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.spRootBasisLevel`, node
`lem-sp-root-basis-level`. There are zero sorry bodies in the delivered module,
zero new holes, and zero split-off statements. Counts: 1 of 1 original holes
closed; net one hole removed. Existing dependencies are used with their published
interfaces. No additional axiom or hole in a definition is introduced.

## No longer needed

No existing import is removed and no whole library module is withdrawn or pruned.
The trial private imports `Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`
and `Mathlib.Algebra.Module.ZMod` were redundant and removed; their APIs are
already available through public dependencies.
`Sheaf.Paper.SpEllCoefficientTower` remains necessary for the theorem's statement
and its coefficient and slice definitions.

Removed from this node's proof dependencies:

- `lem-sp-ell-quotient-finite-discrete`: quotient annihilation follows directly
  from the ideal generator; finiteness and continuity are not used by this proof.
- `lem-weil-pbc-finite-discrete-condensed-ring-constant` and
  `lem-weil-pbc-finite-discrete-scheme-ring-constant`: the actual coefficient
  sheaf is retained throughout; it need not be conjugated to constant B.
- `lem-sp-module-slice-sheafification-independent-ring`: restriction preserves
  local bijectivity by cocontinuity of `Over.forget`, so no comparison between
  module sheafifications is required.

The old integer/residue scalar-extension comparison is replaced by the explicit
cyclic tensor insertion calculation. `Scheme.constantZMod_scalarTensor` and
`spIntegralTwistLevel_comparison` are not used. Their declarations and their
modules' existing imports are preserved. The coefficient limit theorem is also
not used: the proof concerns only one level.

These are local proof-dependency reductions, not claims that the existing
coefficient-definition module or its other proofs have left the targets' closure.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The old plan included unnecessary comparisons with a
constant finite coefficient ring and an independent module-sheafification
comparison. Only the constant cyclic root scalar ring needs sheafification;
local equivalences and the pointwise cyclic tensor calculation suffice.

Checked the edge cases: N is positive at n=0; the cyclic tensor calculation also
works for the zero coefficient group; all local-bijectivity and normalization
arguments allow empty slice objects. No invertibility hypothesis on ell is
added, because the prescribed root basis is already a hypothesis.

The required searches were repeated through LeanFinder, Loogle, the search grep
service, and direct searches of Mathlib, WeilConjectures and Sheaf. They found
ordinary tensor unit formulas and the existing unnormalized comparisons, but
no theorem providing the required normalized slice module map. The proof uses
the existing tensor localization, local-bijectivity and module reconstruction
APIs and elementary cyclic-group algebra. It introduces no further obligation.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
