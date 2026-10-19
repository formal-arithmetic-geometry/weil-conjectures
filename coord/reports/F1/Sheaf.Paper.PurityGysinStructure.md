## What changed

Prove `WeilConjectures.PurityFiniteSetting.gysin_structure` with its complete existing
signature. Factor six evaluation/comparison definitions through five explicit generic
functor-operation helpers to avoid repeated kernel conversions; their values and types
are definitionally unchanged. The five existing object abbreviations stay unchanged. Add proof-only imports of the helper
modules `PurityGysinConstant`, `PurityConstantFiniteTor`, `PurityConcentratedEdge`, the
existing affine-line support geometry and finite-ctf isomorphism closure, and the derived
heart API. Every pre-existing public import and public declaration is retained.

The localization calculation proves the shifted exceptional value is the constant
coefficient complex, using the existing retracted-support comparison and relative
Kummer conclusions. The long exact sequence, shift and truncation calculation is proved
in Lean. The degree-zero restriction is invertible by the composition of adjunction
units and uniqueness of the left adjoint, without assuming an unproved equality of
coefficient-pullback maps. A second helper proves finite-Tor constructibility of the
constant complex by the tensor unit, then the existing intrinsic comparison theorem.
A third proves that every cocycle-normalized edge is invertible at the lowest nonzero
cohomology degree, using bounded-below injective representatives and preservation of
kernels by global sections.

The main proof transports constructibility and concentration through the constant
isomorphism, uses the identity etale cover for rank-one local constancy, and proves the
specified evaluation map bijective using the derived heart and the two sheaf
adjunctions. The supported-cohomology isomorphism has exactly the required normalized
forward factors. Surjectivity then gives the morphism corresponding to the actual
boundary of the coordinate Kummer class.

## Proved and sorry left

Original hole closed: `WeilConjectures.PurityFiniteSetting.gysin_structure`
(node `lem-pur-gysin-structure`), 1 of 1 original holes. No holes added or split off.
The three new public helpers `WeilConjectures.PurityFiniteSetting.gysin_shifted_constant`,
`WeilConjectures.PurityFiniteSetting.constant_finiteTor`, and
`AlgebraicGeometry.ProEtale.RetractedSupport.edge_isIso_of_isGE` are proved.
There are zero `sorry`s in the four delivery modules. Existing imported theorems may
still depend on `sorry`, as intended by stage 3; this delivery does not claim their
transitive axiom closure is finished.

All four delivery modules compiled together without warnings in import order
(`scratchpad/final-all-current.log`): edge 11.1 seconds, finite Tor 32.2 seconds, shifted
constant 37.4 seconds, and main theorem 32.2 seconds. The unchanged original orientation consumer compiled against these fresh artifacts in
47.8 seconds (`scratchpad/orientation-original-single.log`). The original uniqueness
consumer exceeded 60 seconds without a type diagnostic; no consumer is adapted. A
whole-predicate definitional equality probe also exceeded the limit while elaborating
the old expression. These limits are recorded rather than claimed as successful checks.

## No longer needed

No pre-existing imports were removed: all were public imports supporting the existing
interface and have been preserved. No existing module is withdrawn. The following
old proof dependencies are not directly used by `gysin_structure`; their portions
are now carried by the indicated concrete helper or the already stated normalized
retracted-support comparison, rather than imported as unused stand-alone results:

- `def-weil-exceptional-inverse-image`, `lem-pur-support-localization-triangle`,
  `lem-exc-proetale-closed-exact`, `lem-pc-right-derived-functor-triangulated`,
  `def-weil-derived-direct-image`, `prop-pur-kinjective-resolutions-exist`,
  `def-weil-pbc-proetale-site`, `lem-weil-derived-direct-image-composition`, and
  `lem-pur-closed-support-exceptional-comparison`: the existing
  `lem-pur-retracted-support-localization-comparison` already supplies the distinguished
  triangle for the actual transported exceptional value, including its normalized
  support isomorphism. Their internal dependencies remain work of that comparison.
- `lem-pur-finite-kummer-level`: its much larger arithmetic assertion is unnecessary
  here; coefficient finiteness and prime/exponent invertibility are already supplied
  by the finite setting, and coefficient-pullback invertibility by the affine-line datum.
- `prop-pur-gm-relative-kummer`, `lem-weil-pbc-dplus-injective-representative`,
  `lem-sp-grothendieck-enough-injectives`, `lem-sf-derived-homology-long-exact`,
  `lem-sf-derived-concentrated-single`, `def-weil-derived-tensor`,
  `lem-sf-exact-functor-derived-triangulated`, `def-weil-finite-torsion-constructibility`,
  `def-weil-finite-tor-amplitude`, and `def-weil-abstract-derived-category`: used where
  appropriate in the new proved helpers or retained statement interface; no extra
  stand-alone import is needed in the main proof.
- `lem-pur-supported-hom` / `Sheaf.Paper.SupportedCohomologyHom`: the explicitly normalized
  support comparison and the lowest-degree edge calculation directly give the required
  isomorphism. The full supported-Hom theorem is not needed.

The main node drops the obsolete tool approvals for `lem-pur-finite-kummer-level`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`, `lem-exc-proetale-closed-exact`,
`lem-sf-exact-functor-derived-triangulated`, `lem-pc-right-derived-functor-triangulated`,
`prop-pur-kinjective-resolutions-exist`, `lem-weil-derived-direct-image-composition`,
`lem-weil-pbc-dplus-injective-representative`, `lem-sp-grothendieck-enough-injectives`,
`lem-sf-derived-homology-long-exact`, `lem-sf-derived-concentrated-single`,
`lem-weil-pbc-closed-immersion-proper`, `lem-kun-dimension-finite-type`,
`lem-sf-proetale-constructible-origin`, and `thm-sf-ambient-adjoint-class`.
Their direct uses were replaced as described above; some remain transitive dependencies
of existing comparison results. No claim is made that all these modules leave the
whole targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier retained status note said `gysin_shifted_constant` still contained a
`sorry`; the retained Lean source actually had a complete but unvalidated proof
candidate. It needed explicit affine-line projection instances and explicit morphisms
in isomorphism cancellation. The original main candidate transported finite-Tor
constructibility in the wrong isomorphism direction and assumed an isomorphism-closure
instance that is not registered globally; use the existing finite-ctf closure theorem.
The initial tensor-unit calculation specialized all categorical constructions to the
large concrete quotient ring and timed out in kernel checking. Its mathematical
calculation now runs over an abstract coefficient category before specialization. A
private, proved equality relates the concrete Tor-amplitude predicate to its general
formula, avoiding repeated unfolding of the derived-category model. The derived
coefficient pullback is proved invertible by unfolding its recorded definition and
using its actual composition factors; a separately elaborated specialization caused
unnecessary conversions through the K-flat construction.
The main evaluation/comparison definitions were factored as described above. The existing
statement and mathematical objects are unchanged. The broader derived-category and finite
setting experiments were rejected and are not part of the delivery.

The support-boundary correspondence only needs bijectivity of the displayed evaluation
map and invertibility of the normalized support identification: the proof works for
any boundary map, and does not use the supplied exactness witness. This proves the
original conclusion with its original quantifiers.

## New nodes

`lem-pur-gysin-shifted-constant` (module `Sheaf.Paper.PurityGysinConstant`) carries the
localization and relative-Kummer computation in the source's first paragraph. Its
statement is strictly the concentration/trivialization part, without constructibility,
evaluation or supported-boundary conclusions. It is proved, with no hole.

`lem-pur-constant-finite-tor` (module `Sheaf.Paper.PurityConstantFiniteTor`) carries the
independent tensor-unit calculation in the first paragraph. It holds for every scheme
with the specified structure morphism, with no finite-type hypothesis. It is proved,
with no hole.

`lem-pur-concentrated-edge-iso` (module `Sheaf.Paper.PurityConcentratedEdge`) carries the
normalized edge identification from the second paragraph, using the first paragraph's
good truncation. It applies to any object bounded below by the displayed degree and
every normalized natural edge, not only the exceptional object. It is proved, with
no hole. Empty or disconnected schemes and the zero coefficient ring cause no
additional assumption in any helper. Searches found no existing matching statement;
the underlying homology, truncation, kernel and tensor APIs are reused.

Definition change record: `coord/changes/F1-gysin-evaluation-comparisons.md`. It includes
the old and new definitions and all 179 known consumers with their current holders.
No consumer source is adapted.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
