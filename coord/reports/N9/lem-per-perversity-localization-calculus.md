## Worker report

The saved module `Sheaf.Paper.PerversityLocalizationCalculus` states
`AlgebraicGeometry.Etale.perversity_localization_calculus`. Its sole postponed theorem has
proof `sorry`. All other declarations are actual constructions, predicates, or records
packaging this lemma's clauses; no data are chosen from an uncharacterized existence theorem.
No node statement or dependency list is changed, and no new or repaired dependency node is needed.

Source checked: ILO, Travaux de Gabber, Exposé XVII §5.2, Definition 5.2.1,
Proposition 5.2.2(a)--(d), printed p.287, and the first reduction in §5.3.1(a), p.288.
The saved source extract `source.txt` includes these pages. The node deliberately states the
integer-valued finite-coefficient specialization of that source. Its proof is retained in
the theorem docstring, including the empty-scheme case and the supported-cone argument.

Hypothesis and clause correspondence:

- Prime ell and n >= 1 are `hell : Nat.Prime ell` and `hn : 1 ≤ n`.
  `PointwisePerverseCoefficients ell n` is `ULift (ZMod (ell ^ n))`, an isomorphic
  universe lift of the specified ring, with no rationalization or coefficient extension.
- `PointwisePerverseContext` contains the actual scheme X, `IsNoetherian X`,
  invertibility of ell at every structure-sheaf stalk, the function `p : X → ℤ`,
  and `Specializes x y → p x ≤ p y`. Invertibility on stalks is the usual
  invertibility of ell on X. Contexts impose no excellence or dimension bound.
- `PointwisePerverseDerived` is the ordinary `DerivedCategory.Plus` of small étale
  module sheaves. It has no constructibility or finite-Tor-dimension restriction.
- `PointwisePerverseLE` tests the geometric stalk of H^a M at every algebraically
  closed field-valued point in every integer a > p(x). `PointwisePerverseGE` tests
  H^a of `pointwisePerverseCostalk` at every a < p(x). The latter first restricts
  to the actual `Scheme.strictLocalization s`, then uses the existing
  `derivedSupportedEtaleSections` on the complement of its closed point.
  Thus it uses exactly the geometric-fibre formula for the costalk specified by the
  node; it does not replace the costalk by an arbitrary functor.
- `PerversityLocalizationCalculus.t`, `upper_iff`, and `lower_iff` give the t-structure
  and identify its two degree-zero classes with precisely those tests. Its heart and
  truncation are Mathlib's `t.heart.FullSubcategory` and `t.truncLE 0`.
- A pseudo-open morphism is `IsPointwisePseudoOpen`: an embedding of topological spaces
  and invertibility of every `f.stalkMap y`. By the inverse-image stalk formula and
  stalkwise detection of sheaf isomorphisms this is precisely invertibility of the
  structural sheaf morphism f⁻¹O_X → O_Y, together with the specified embedding.
- `pseudo_exact` gives both t-exactness implications for the canonical derived inverse
  image, under the equality `C.p = B.p ∘ f`. `pseudo_lower` gives preservation of
  the lower class by the canonical right derived direct image.
- `heartAdjunction` is an adjunction between the actual hearts. `inverseFactors`
  identifies its left adjoint with ambient inverse image and `extensionFactors`
  identifies its right adjoint with ambient pushforward followed by upper truncation.
  Full faithfulness is given by `full_extension` and `faithful_extension`, and the
  invertible counit by `counit_isIso`. T-exactness also expresses exactness of the
  induced heart inverse image. `unit_eq` and `counit_eq` normalize both adjunction maps
  by the ambient derived adjunction and the truncation inclusion.
- `composition` supplies the inverse-image comparison normalized by
  `upperStarCompDerivedPlus`; the extension comparison is required to be its
  `conjugateIsoEquiv` mate under the composite and direct heart adjunctions.
  This is the canonical transitivity isomorphism, with unit and counit compatibility.
- `IsPointwisePerverseRestriction` is the disjunction of an étale map, a localization
  `X.fromSpecStalk x` up to source isomorphism, and a strict localization
  `Scheme.strictLocalizationToBase s` up to source isomorphism.
  `restriction_exact` gives both bounds for the pulled-back perversity.
- `generic_locality` assumes an integral base, a generic point eta, and all stalks
  normal domains. `eeta` and its equation identify j with the actual generic-point
  inclusion. The base-changed generic scheme is `pullback j h`, with its canonical
  projections, so no component or generic fibre is omitted. The isomorphism beta is
  constrained to be the ordinary adjunction exchange, using the canonical inverse-image
  composition comparisons. The isomorphism e compares the two perverse-truncated
  ambient functors and is normalized by the two upper-truncation inclusions.
  Since the source and target are heart objects, this is exactly the heart comparison
  in the node, expressed after the fully faithful heart inclusion.
- `generic_components` identifies the image of the base-changed generic scheme with
  the set of points generic in their irreducible component. It makes the preceding
  comparison's componentwise meaning explicit, without choosing one component.
- `punctured_local` uses a strictly henselian local ring A and an isomorphism from X
  to Spec A identifying x with its closed point. U is exactly the complement of x,
  and g is its canonical inclusion up to the supplied source isomorphism.
  L is a heart object with `DerivedCategory.IsLE L.obj.obj (B.p x)`.
  The resulting isomorphism compares g_*^p L with ordinary truncation of Rg_* L;
  its equation identifies both maps into Rg_* L. The final `IsIso` says that the
  ordinary truncation inclusion becomes invertible after restricting to U.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-weil-pbc-strict-henselization-limit`: `Sheaf.AlgebraicGeometry.StrictHenselization`, `AlgebraicGeometry.Scheme.strictHenselizationRing`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`.
- `def-pur-etale-supported-kernel`: `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`, `AlgebraicGeometry.Etale.supportedKernel`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-pur-etale-derived-supported-sections`: `Sheaf.AlgebraicGeometry.EtaleSupportedSections`, `AlgebraicGeometry.Etale.supportedEtaleSections`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`.
- `def-weil-t-structure`: `Mathlib/CategoryTheory/Triangulated/TStructure/Basic.lean`, `CategoryTheory.Triangulated.TStructure`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`.
- `def-weil-pbc-geometric-stalks`: `Sheaf.AlgebraicGeometry.PointedEtaleStalk`, `AlgebraicGeometry.pointedEtaleStalk`.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.upperStar`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.lowerStar`.

The derived category record's primary declaration is its torsion predicate, but its
module's documented ordinary categories are `DerivedCategoryModule` and
`DerivedCategory.Plus`; this module uses exactly that underlying category, without
using the unrelated torsion predicate as a replacement for D+. No interface repair
is necessary. The strict-henselization record's `strictHenselizationRing` and
`strictHenselizationScheme` are aliases for the upstream `strictHenselization` and
`strictLocalization` used here. Current missing local upstream sources were read
through the authorized `scompile.py --source` interface.

Proof-dependency modules with recorded declarations are imported privately.
The two still unstated abstract inputs (`lem-per-set-generated-sheaf-aisle` and
`lem-per-supported-generators-costalk-detection`) have no module to import.
The generic bounded-below derived adjunction is used through the existing
`upperStarLowerStarAdjunction` and `.derivedPlus` API.

Edge cases checked: empty X and empty punctured U (zero categories, no minimum over
an empty set); the zero complex; negative and unbounded integer values of p (no
assumed finite range); n=1 and ell=2; arbitrary scheme universe u with coefficient
objects in u+1; no chosen distinguished irreducible component of the restriction;
identity morphisms, isomorphic sources, and empty étale restrictions. Quantifying
geometric fields in the same universe as schemes follows the dependency's geometric
point convention and includes algebraic closures of every residue field.

Searches retained from the previous worker and checked against current source:

- `msearch.py ... leanfinder "pointwise etale perversity localization t-structure
  pseudo-open immersion perverse extension"`: eight hits for ordinary étale schemes,
  sites and ordinary IsGE, no matching localization calculus.
- `msearch.py ... leanfinder "pointwise perverse t structure etale sheaves localization
  functor"`: ordinary derived-category bounds and representatives, no match.
- `msearch.py ... loogle "IsPerverseLE, IsPerverseGE, rightDerivedLowerStarPlus"`:
  no hits, unknown identifier IsPerverseLE in the Mathlib index.
- `msearch.py ... loogle "TStructure, DerivedCategory.Plus"`: no hits under that
  short unqualified TStructure name.
- `msearch.py ... grep "perverse|Perversity|pseudoOpen"`: no Mathlib hits.
- Direct `rg` with that expression in `WeilConjectures` and `lean/Sheaf` finds
  existing dimension-support/dual-cosupport notions in Etale.Perverse.Basic and
  QbarPerverseSubcategories. Their signatures were read: those fix dimension
  perversity and Verdier-dual cosupport, rather than an arbitrary integer-valued p
  and strict-local supported costalk. They do not state this node's theorem.
  The pseudo-open strict-local-fibre theorem supplies a proof input only.
- Direct `rg` of this exact node id in upstream `WeilConjectures` finds no declaration.

No statement correction or STATEMENT-DISPUTED flag is needed.

## Self-check for maintainer review

I reopened the node, module, source extract, and dependency interfaces. The saved
packet initially had no lean record or report. I supplied both, scoped the necessary
heartbeat budget to individual declarations, and added the recorded proof imports.
This is the dispatched worker's self-check; independent review is performed by the
maintainer, as specified by the dispatch brief. No independent second reading is claimed.

## Validation result

The saved module without the newly required proof imports compiled in both sandbox
and library modes (37.6 s / 40.1 s), revealing only the unscoped heartbeat-option
linter warning. That option has now been scoped to its two declarations.
The final module includes all recorded proof imports. Two subsequent scompile.py
checks and the required deliver2.py --no-push all stop before elaboration with:

```text
INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or lacks)
the live module Sheaf.Paper.EtaleSupportAisleGenerators; not the delivery's fault,
retry after the next published live build.
object file .../Sheaf/Paper/EtaleSupportAisleGenerators.olean ... does not exist
```

This import is the recorded module of lem-per-etale-support-aisle-generators and is
required by the stage-2 import contract. Its source is present. The authorized wrapper
refuses because its published artifact is absent. No dependency import was discarded,
no library or launcher file was modified, and no global build was attempted.
The dry run printed COMPILE FAILED on the server, nothing pushed.
The final module has not yet completed a clean compile with its required proof imports.

## Resumed validation (2026-10-18 UTC)

Retained the saved packet and first ran the prescribed
`deliver2.py N9 lem-per-perversity-localization-calculus --no-push`.
It again exited 1 before elaboration with `COMPILE FAILED`, identifying the missing
published `Sheaf.Paper.EtaleSupportAisleGenerators.olean` artifact. A separate prescribed
`scompile.py N9 lem-per-perversity-localization-calculus` check of the saved module
confirmed the same `INFRASTRUCTURE RETRY (stale live olean)` and exited 75.

Reopened the dependency's current node record and source. The record still names
`Sheaf.Paper.EtaleSupportAisleGenerators` and its declaration
`AlgebraicGeometry.Etale.supportFiltrationClass_isLeast`; its source is present.
The item still cites it as a proof dependency, so its private import remains required
by stages/2-statements.md §3.7. This is a missing published build artifact, rather than
an unusable mathematical interface that a dependency module could repair.
No import was removed, no launcher script or shared source was changed, and no global
build was attempted. Nothing was pushed. The packet remains ready for a retry after
the dependency artifact is published.

## Further dispatched retry (2026-10-18 UTC)

The required initial dry run again exited 1 before elaboration, reporting the missing
published `Sheaf.Paper.EtaleSupportAisleGenerators.olean`. The separate prescribed
`scompile.py` invocation on the retained module exited 75 with the same explicit
`INFRASTRUCTURE RETRY (stale live olean)` diagnostic. The authorized `--source`
query successfully returned that dependency's current source, confirming that source
availability does not resolve the missing published artifact. The completed tool
results were checked after the provider interruption; no successful delivery or
pending mutation was reported. The Lean module and node record are retained unchanged.
No dependency import was removed and nothing was pushed.

## Provider-interruption continuation (2026-10-18 UTC)

Checked the saved report and process list before rerunning any wrapper: no delivery
or compile process remained, and the saved report recorded no push. The prescribed
initial `deliver2.py N9 lem-per-perversity-localization-calculus --no-push` completed
with exit 1, `COMPILE FAILED on the server, nothing pushed`. The separate prescribed
`scompile.py` check of the retained module completed with exit 75. Both stopped
before elaboration with the same explicit diagnostic:

```text
INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or lacks)
the live module Sheaf.Paper.EtaleSupportAisleGenerators; not the delivery's fault,
retry after the next published live build.
```

The missing object is the published
`Sheaf/Paper/EtaleSupportAisleGenerators.olean`. Checked the current dependency
record: it still names that module and `AlgebraicGeometry.Etale.supportFiltrationClass_isLeast`.
The current item still cites it in `proof_deps`, so the private import remains
required by stages/2-statements.md §3.7. The sandbox node differs from the current
shared node only in `lean`, and no repair note exists for this item. This is the
wrapper's explicit infrastructure refusal; changing the mathematical statement or
removing its required import would not repair it. No Lean or node changes were made,
no live sources or launcher tools were modified, and nothing was pushed.

## Dispatched retry (2026-10-18 21:07 UTC)

Retained the packet and first ran the required `deliver2.py N9
lem-per-perversity-localization-calculus --no-push`. It exited 1 with
`COMPILE FAILED on the server, nothing pushed`, before elaboration. The prescribed
single-file `scompile.py` check independently exited 75 with:

```text
INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or lacks)
the live module Sheaf.Paper.EtaleSupportAisleGenerators; not the delivery's fault,
retry after the next published live build.
```

The missing published object remains
`Sheaf/Paper/EtaleSupportAisleGenerators.olean`. Its source is present in the shared
checkout; the dependency node still records that module and
`AlgebraicGeometry.Etale.supportFiltrationClass_isLeast`. It remains a proof dependency
of this item, so stages/2-statements.md §3.7 requires retaining its private import.
This is the wrapper's explicit infrastructure refusal rather than an elaboration
failure or an unusable dependency interface. No Lean declaration or node record was
changed, no tool or shared source was modified, and nothing was pushed.


## Interrupted-turn continuation (2026-10-18 21:12 UTC)

Retained the saved packet and inspected the report before starting the required
`deliver2.py N9 lem-per-perversity-localization-calculus --no-push`. Its process
completed with exit 1: `COMPILE FAILED on the server, nothing pushed`. The separate
prescribed `scompile.py` check completed with exit 75. Both stopped before
elaboration with the explicit wrapper refusal:

```text
INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or lacks)
the live module Sheaf.Paper.EtaleSupportAisleGenerators; not the delivery's fault,
retry after the next published live build.
```

The missing published object is `Sheaf/Paper/EtaleSupportAisleGenerators.olean`.
Reopened the current dependency record and its source signature: it still records
`Sheaf.Paper.EtaleSupportAisleGenerators` and
`AlgebraicGeometry.Etale.supportFiltrationClass_isLeast`. The item still lists
`lem-per-etale-support-aisle-generators` in `proof_deps`, so its private import
remains required. The sandbox node differs from the current shared node only in
`lean`, and no repair note exists for this item. This is a missing published
artifact, not an elaboration defect or an unusable mathematical interface.
No Lean or node files were changed, no launcher or shared files were modified,
and nothing was pushed. Both wrapper results were collected before ending the turn.

## Dispatched validation retry (2026-10-18 21:15 UTC)

Inspected the retained report first and ran the required `deliver2.py N9
lem-per-perversity-localization-calculus --no-push`. It exited 1 before elaboration
with `COMPILE FAILED on the server, nothing pushed`. The prescribed single-file
`scompile.py` independently exited 75 with the same explicit tool refusal:

```text
INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or lacks)
the live module Sheaf.Paper.EtaleSupportAisleGenerators; not the delivery's fault,
retry after the next published live build.
```

The published `Sheaf/Paper/EtaleSupportAisleGenerators.olean` remains missing.
Checked the current dependency node and source: they still name this module and
`AlgebraicGeometry.Etale.supportFiltrationClass_isLeast`. The item still lists
`lem-per-etale-support-aisle-generators` in `proof_deps`, requiring its private import
under stages/2-statements.md §3.7. No repair note exists, and the sandbox node differs
from the shared node only in `lean`. This is the wrapper's explicit infrastructure
failure rather than an elaboration defect. No Lean or node changes were made,
no shared or launcher files were modified, and nothing was pushed. Both wrapper
processes completed and their results were collected.

## Successful resumed validation (2026-10-18 UTC)

The interrupted dry-run session was no longer available and no wrapper process for
this item remained. Reran the prescribed dry run with its output retained in the
sandbox. It completed with exit 0 and printed:

```text
OK (dry run): commit 6c89ec351a passes the preflight and compiles; nothing pushed
```

The previously missing published dependency artifact no longer prevents compilation.
The saved Lean module was retained unchanged, including every required proof import.
Reopened the current node, the entire module, and the saved ILO XVII §§5.2–5.3 source
extract. Rechecked the hypothesis and clause correspondence above: finite coefficients,
Noetherian schemes, invertibility, specialization inequality, stalk and costalk bounds,
normalized heart adjunction, composition mates, restriction and generic comparison,
and the punctured-local ordinary truncation comparison. No mismatch was found.
Checked again that the sandbox node differs from the current shared node only in
`lean`, its recorded signature is verbatim, every source line is within 100 characters,
and the only postponed theorem has its proof docstring and `sorry`. No repair note
exists for this item. This is the author's self-check; independent mathematical review
remains with the maintainer. The earlier infrastructure failures above are historical
and are superseded by this successful preflight and compilation.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
