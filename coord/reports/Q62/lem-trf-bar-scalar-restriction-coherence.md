## Worker report

The module `Sheaf.CategoryTheory.BarScalarRestrictionCoherence` states all parts of
lem-trf-bar-scalar-restriction-coherence. Its primary declaration is
`CategoryTheory.PresheafBar.exists_unique_derivedScalarComparison`; the `lean.declarations`
list contains its accompanying specification records and theorem clauses. Every theorem
has exactly `by sorry`. Definitions have complete data, and no definition selects data
from a postponed existence theorem. There is no statement correction and no disputed claim.
The statement dependency `def-trf-presheaf-bar-resolution-data` owns the existing
`Resolution`, generator maps and complexes in the landed PresheafBarResolutionData module.
The augmented-resolution existence theorem remains a proof dependency only.

Read the item's full statement, all seven proof steps, all statement-dependency records,
their source declarations and docstrings, and the two proof-dependency interfaces. The
source read is `literature/stacks-project/sites-cohomology.tex`, examples
`example-left-derived-colimits` (08PG) and `example-morphism-categories` (08PH), including
the alternating differential and the explicit `(u(U_bullet), t(x))` formula. The
coefficient restriction and normalization refinements are the node's explicitly agent
written refinement, not an assertion that Stacks states these extra identities verbatim.
The prescribed CompactObject example is now a withdrawn module; the landed
PresheafBarResolutionData supplies the current module/header pattern.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Size convention; small categories | Explicit universes `u v r s t wR wS wT wA wAR wAS`; categories `E D J : Type u` with `SmallCategory`; coefficient modules in `max u v`. No nonemptiness or finiteness assumption. |
| Arbitrary commutative rings and maps | Independent `R : Type r`, `S : Type s`, `T : Type t`, `CommRing` instances, `rho : R →+* S`, `sigma : S →+* T`. |
| A(E,R) is the module-presheaf category on the identity-cover site | Existing `PresheafBar.Presheaves`, definitionally `Eᵒᵖ ⥤ ModuleCat R`; its recorded docstring identifies the constant-ring bottom-topology module sheaves. No substitute category is introduced. |
| L_U(M), B, their incoming-arrow restrictions, faces, alternating differentials, augmentation | Existing `Resolution.L`, `freeIso`, `B`, `termIso`, `restriction_eq`, `face_eq`, `differential_eq`, `a`, `augmentation_eq`, with the actual raw maps `freeTerm`, `term`, `ι`, `face`, `differential`, `augmentation`. These are not restated in this module. |
| K and its coefficient-end face, zero positive terms | Existing `Resolution.K`, `colimitTermIso`, `colimit_face_eq`, `colimit_differential_eq`, `positive_zero`; actual `colimitTerm` and `colimitι`. |
| C is colimit over E opposite | Existing `PresheafBar.C`, definitionally `CategoryTheory.Limits.colim`, and `Resolution.b`. |
| Restriction preserves underlying groups and maps with restricted action | Mathlib `ModuleCat.restrictScalars`; objectwise restriction is exactly Mathlib `Functor.whiskeringRight`. No new restriction functor is defined. |
| Natural B and K isomorphisms | `ScalarComparison.beta` and `.kappa` are natural isomorphisms of cochain-complex valued functors. `exists_scalarComparison` states existence for independent ring universes. |
| Identity on generator coefficients | `beta_generator` uses the actual incoming-arrow inclusion `ι`; `kappa_generator` uses `colimitι`. Both are conjugated by the existing term-coordinate isomorphisms. |
| Augmented compatibility | `ScalarComparison.augmented` is the equality beta followed by restricted a, with the standard single-complex comparison, equals a of the restricted presheaf. |
| Total left derived colimits are defined everywhere | `NormalizedModel.LC`, `.epsilon`, `.universal`; `.defined` is essential constancy of the full homotopy-category denominator pro-diagram at every object, precisely the recorded triangulated-left-derived notion. |
| Left acyclicity means the canonical single-object comparison is invertible | `NormalizedModel.acyclic` states `IsIso (epsilon.app (singleFunctor ... 0).obj term)` for every B term. It does not assert preservation of projectives. |
| Assume the canonical comparisons m, with the displayed formula | `NormalizedModel.m` is a natural isomorphism. `.normalization` is literally `inv (LC.map (Q.map a)) ≫ epsilon.app B ≫ Q.map b`, the node's formula in Lean's diagrammatic order. The `colimitAdditive` field is the ordinary structural additivity needed to form the termwise colimit functor, not a new mathematical restriction on E or R. |
| Canonical natural derived scalar isomorphism | `exists_unique_derivedScalarComparison` quantifies the two normalized models and the specified scalar comparison, and returns a unique natural isomorphism alpha between the two indicated derived-colimit functors. The localization choices for the two presheaf categories are independent `wAR`, `wAS`; those for modules are `wR`, `wS`. |
| Conjugation by m is exactly Q(kappa) | The theorem's normalization equation is `alpha ≫ Dr(m_S) ≫ factors = m_R ≫ Q(kappa)`. The `factors` is Mathlib's canonical `mapDerivedCategoryFactors`, not a free comparison. Uniqueness expresses the word canonical, since every factor on the right of alpha is invertible. |
| Semilinear natural t for u | `t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars rho`; components are exactly R-linear maps into restricted G, which is the node's semilinearity. |
| Reindex chain and apply t to coefficient | `SemilinearMap.map` is a cochain morphism and `.formula` evaluates it on the actual generators as `(c ⋙ u, t.app (op c.right) x)`. |
| Factor through same-ring map and scalar isomorphism | `exists_semilinearMap_factorization` returns both the same-ring and semilinear maps and their exact factorization by `k.kappa.hom.app G`. |
| Composite data (vu, sigma rho, st) | `semilinearMap_composition` takes rho, sigma, t, s, and the composite a with the explicit component equality `ha`. The conclusion is equality on every element in every degree under the identity-on-groups iterated restriction. Rings have independent universes. |
| Identity data | `semilinearMap_identity` fixes every element in every degree. The underlying identity scalar restriction is Mathlib's usual one. |
| Scalar coherence of beta and kappa | `scalarComparison_composition` states both equations in every degree, evaluated in each presheaf object for beta. |
| Identities persist under normalized derived comparisons | `normalizedMap_coherence` gives composition and identity for the node's conjugation formula. `normalizedMap_restrictScalars` gives the compatibility with Dr and its canonical localization identification. `scalarNormalizedMap` writes the precise semilinear formula, and `scalarNormalizedMap_composition` gives the actual equation `A_1 ≫ Dr_rho(A_2)` as the normalized chain composite in the iterated restriction identification. Together with `semilinearMap_composition` this is the specified composite; using `scalarComparison_composition` gives the alpha coherence. |
| Restriction is exact | The existing finite-limit and finite-colimit instances from `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` (lines 41 and 46), plus Mathlib's existing Additive instance. These retain independent ring and module universes. |
| Preserve cone roofs for connecting maps, including their sign | `restriction_preserves_cone_roofs` takes any cone denominator q, states preservation of its QuasiIso property, and states equality of the restricted `mappingCone.triangle.mor₃` with the new one after the canonical cone/shift comparisons. Mathlib's mor₃ is the signed arrow of the recorded derived-category convention. Its second conjunct states the corresponding connecting-map equality using `triangleOfSESδ`. Both conclusions quantify all relevant roofs/sequences. |
| No flatness or preservation of projectives | Neither appears as a binder, instance, record field, or premise. |

Dependency declarations used:

- `Sheaf.CategoryTheory.PresheafBarResolutionData`, owned by
  `def-trf-presheaf-bar-resolution-data`: `CategoryTheory.PresheafBar.Resolution`,
  `Presheaves`, `ι`, `colimitι`, `C`, and the documented coordinate/augmentation fields.
  Its formulas include all L/B/K notions. This module imports only the definition
  owner, and makes no choice from the separate `exists_resolution` theorem.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; the
  general ringed-site meaning underlying the presheaf identification, imported through
  the existing resolution module, not replaced by an extra sheaf category.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings` and
  Mathlib's bottom topology, already used by the resolution module.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colim`, colimit inclusions;
  the ordinary colimit in the reused `C` and `b`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and `Qh`.
- `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`:
  `Functor.IsTriangulatedLeftDerivedValue`/`IsTriangulatedLeftDerivedDefinedAt` and the
  exported `IsEssentiallyConstantProDiagram`. `NormalizedModel.defined` expands exactly
  their denominator diagram so no additional saturation hypothesis is imposed.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`,
  `mapDerivedCategoryFactors`, its shift structure, and exact-functor localization. This
  is the recorded Mathlib match for lem-sf-exact-functor-derived-triangulated.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `ModuleCat.restrictScalars`, its
  existing Additive instance, `preservesLimit_restrictScalars`,
  `preservesColimit_restrictScalars`, and the identity/composition restriction interfaces.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` and its public imports:
  `CochainComplex.mappingCone`, `mappingCone.mapHomologicalComplexIso`,
  `mappingCone.triangle`, and `DerivedCategory.triangleOfSESδ`.

The size-convention node is metatheoretic and explicitly has no declaration to import.
The proof dependencies are available as public imports because their types are actually
used in these statements. `DerivedColimitBar` is transitively imported by the already
landed Resolution; its owning definition node supplies `categoryBarDelete`. The maintainer
must not add a reverse proof import from that module to this one: it would close an
import cycle. This delivery does not import the bar-system existence theorem as a premise.

Edge cases checked before writing and again on the finished signatures:

- Empty E: generator domains are empty; there is no hidden chosen object. All B/K terms
  are zero. The assertions concern the zero maps and canonical zero-object comparisons.
- One-object identity category: all identity arrows and their degenerate chains are retained;
  the node is the unnormalized complex, not a quotient by degenerate chains.
- Degrees 0, -1 and -2: the reused face convention restricts coefficients only at the last
  face; signs are unchanged by restriction. The degree-zero augmentation square is an
  explicit field, not inferred solely from a homology isomorphism.
- Positive degrees: all identity/composition statements quantify every integer degree and
  use the existing zero-positive-terms condition, so they do not omit these degrees.
- Zero ring, zero coefficient module, and the nonflat map Z → Z/2: all formulas still
  use the same additive maps and restricted scalar action. No tensor, flatness or
  projective-preservation premise is present.
- Nonfaithful u and v: direct sums are mapped by the coefficient generator rule; collisions
  add coefficients. No injectivity of the chain reindexing is assumed.
- Identity and arbitrary composable ring maps: composition equations concern all coefficients
  in every degree, with action sigma(rho(a)), not just equality on cohomology.
- Large coefficient rings relative to modules: Mathlib's `ChangeOfRingsExact` instances quantify
  `ModuleCat.{v}` independently of r and s. This avoids the larger-module-universe condition
  of Mathlib's coextension/extension adjunction instances. No site universes are equated.
- Connecting maps: the cone roof equation uses the actual signed mor₃, retaining its minus
  sign and the standard shift comparison; its denominator remains a quasi-isomorphism.

Searches actually run with the prescribed msearch.py wrapper (Q62/item search log):

- LeanFinder: `Category bar resolution commutes with scalar restriction and semilinear
  functor maps compose` — 8 hits, including generic monoidal scalar restriction and
  ModuleCat restriction-composition naturality; no complete bar/derived statement.
- Loogle: `ModuleCat.restrictScalars` — 12 hits, including restrictScalars, its identity
  isomorphism and adjunction infrastructure; used the existing functor.
- Mathlib grep: `restrictScalars|barComplex`, subdirectory `Algebra/Category/ModuleCat` —
  25 capped hits, scalar and sheaf restriction interfaces; no normalized bar statement.
- LeanSearch: `Scalar restriction commutes with the category bar resolution and normalized
  derived colimit comparisons` — 8 hits including restrictScalars,
  preservesColimit_restrictScalars, and presheaf scalar restriction; no complete match.
- Project rg: `bar.*[Ss]calar|[Ss]calar.*[Bb]ar|normalized.*[Bb]ar|categoryBar` in both
  `lean/Sheaf` and `lean/WeilConjectures`: found DerivedColimitBar's general system and
  DerivedColimitChangeRings' extension-of-scalars comparison, but neither states this
  independent augmented-resolution scalar-coherence theorem. Reused PresheafBarResolution.
- Project node-id grep in `lean/WeilConjectures`: no match. Name collision search in
  `dag/lean_names_upstream.json`, `lean/Sheaf/CategoryTheory`, and
  `lean/WeilConjectures/CategoryTheory`: no full namespace collision; unrelated namespaces
  contain their own ScalarComparison records, which are different notions.

Compilation uses only scompile.py. A run encountered local disk exhaustion; the wrapper's
required confirmation against current server sources succeeded (13.8 seconds, exit 0).
Subsequent revisions receive fresh single-file server compilation and delivery preflight.

## Second reading by Q62

A second pass by the same dispatcher-started worker compared the full node and finished
module, rather than claiming an independent worker review; the dispatcher's explicit
instruction prohibits starting another agent, and the maintainer performs the independent
review. It checked all rows of the hypothesis/clause table against the source declarations.

This pass replaced an initial common-ring-universe family record with the pairwise
`SemilinearMap` record and theorems for independently sized R, S and T. It also separated
the two presheaf localization universe parameters, preserved the full everywhere-defined
Stacks condition, added the explicit derived semilinear-composition equation, and retained
both beta's augmentation equation and the signed cone-roof equation. It checked that a
pair of arbitrary maps was never substituted for the coefficientwise maps: each is a
cochain morphism with its required generator formula. All construction records have real
fields; all existence assertions remain theorems with sorry, and no data is chosen from them.

The repair uses the landed definition owner and removes redundant exactness theorem copies as
requested below. All scalar comparison records and their theorem statements are unchanged.
The natural-language statement and split of the item are intact.


## Repair of returned head b5545c21537e

1. **H2:** Current main now contains `def-trf-presheaf-bar-resolution-data`, whose
   own module `Sheaf.CategoryTheory.PresheafBarResolutionData` defines the exact
   `Resolution`, `Presheaves`, `ι`, `colimitι`, `C` and all construction helpers.
   Read its record, declarations and Resolution fields. The augmented-resolution
   theorem now imports that owner, owns only `exists_resolution`, and cites the
   definition node in `stmt_deps`. This delivery imports the definition module
   directly and cites its definition node instead of the theorem in `stmt_deps`.
   The existence theorem remains a proof dependency only. The earlier sandbox
   definition and dependency-node copies are superseded by these landed records
   and removed from this packet; no existing dependency record is overwritten.
2. **H4:** Deleted `restrictScalars_finiteLimits`, `restrictScalars_finiteColimits`,
   their instance-attribute line and their `lean.declarations` entries. Imported
   `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`, whose instances at
   lines 41 and 46 apply with arbitrary ring and module universes. No comparison
   formula, hypothesis, degree, identity/composition clause or sign changed.
3. **Advisory:** The second pass above is identified as this worker's self-check.
   No separate worker review is claimed; the maintainer reviews independently.

The previous launcher refusal is resolved by the landed theorem dependency edge.
The stale sandbox ownership record pointed to the old theorem module; adopting
the current landed definition module repairs that preflight conflict. The item
statement is unchanged and no new node or dependency module is delivered.

## Validation

The revised direct-definition import compiled with `scompile.py` in both sandbox
and library checks, with no errors or unexpected warnings. The only item-node
changes from current main are its Lean record and addition of the landed definition
node to `stmt_deps`. The primary Lean signature remains verbatim in the record.
The prescribed delivery dry run checks the rebased packet and server compilation
before the delivery push.
