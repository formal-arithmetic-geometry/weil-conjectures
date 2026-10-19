## Worker report

The module `Sheaf.Paper.DerivedCompleteIntegralDetailed` defines the object property
`WeilConjectures.boundedConstructibleDerivedCompleteIntegral` and its full subcategory
`WeilConjectures.boundedConstructibleDerivedCompleteIntegralCategory`. Both are real
constructions. There are no new theorem declarations or postponed proofs in the item module.
The node statement is unchanged. The five additional statement dependencies are already
landed prerequisites of the canonical reduction/completeness interface, supplied as paired
dependency overlays under §1(B), not new mathematical notions.

Clause-by-clause correspondence:

- The convention of a prime `l ≠ p` is `[Fact l.Prime]` and `hl : l ≠ D.p`, where
  `D : FiniteFieldDatum.{d}` is the global convention already used by the completed
  coefficient and derived-completeness dependencies. No structure morphism from `Y` to
  the finite-field base, nor finite-type, separatedness or invertibility on `Y`, is imposed.
- A finite extension of `Q_l` is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its valuation ring and chosen uniformizer, hence
  `A_{E,n}`, are precisely those in `Padic.coefficientExtensionRing`, imported through
  the recorded completion and reduction modules; no alternate coefficient ring is defined.
- The arbitrary scheme is `Y : AlgebraicGeometry.Scheme.{u}`. As in the recorded finite
  torsion and support declarations, the scheme and coefficient field share an ambient
  universe. The finite-field datum has its independent universe `d`; the small site's
  objects have universe `u+1` and its morphisms have universe `u`, with coefficients and
  module sheaves in universe `u+1`. In particular these site universes are not identified.
- The ambient derived category of modules over the completed coefficient sheaf is exactly
  `completedIntegralDerivedCategory l E Y D hl`. It is not the derived category of
  modules over the discrete constant sheaf of the valuation ring.
- The first defining condition is `IsDerivedComplete l E Y D hl K`, using the recorded
  canonical reduction tower and the distinguished Roos triangle predicate.
- For every positive level, membership in `D^b_c(Y,A_{E,n})` is
  `intrinsicFiniteTorsionConstructible l E (n + 1) ... Y
  ((integralDerivedReduction l E Y D hl n).obj K)`. The bound proof is the explicit
  `Nat.succ_le_succ (Nat.zero_le n)`. The reduction index `n : ℕ` denotes exponent
  `n+1` exactly as in the recorded reduction module, so exponent zero is never tested
  and every positive exponent is tested. The intrinsic finite torsion predicate is
  the recorded dependency declaration, containing finite support and constructibility
  of every cohomology sheaf.
- A single pair of integers independent of the level is `∃ r s : ℤ, r ≤ s ∧ ∀ n : ℕ, ...`.
  For every degree `i`, membership in the recorded `proEtaleCohomologicalSupport` of
  the reduction implies `r ≤ i ∧ i ≤ s`, precisely containment in the closed interval.
  There is no additional boundedness condition on `K` or its integral cohomology.
- `ObjectProperty.FullSubcategory`, via `.FullSubcategory`, gives the full category of
  those objects. No triangulated closure instance is asserted; that is the separate
  node `lem-weil-integral-constructible-triangulated`, as the item requires.

Dependency declarations used directly:

- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `WeilConjectures.completedIntegralDerivedCategory`,
  `WeilConjectures.completedIntegralModuleSheaves`, and its canonical inverse-limit
  coefficient sheaf and projections.
- `Sheaf.Paper.DerivedComplete`: `WeilConjectures.IsDerivedComplete`.
- `Sheaf.Paper.IntegralDerivedReduction`: `WeilConjectures.integralDerivedReduction`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`:
  `AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport`.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`:
  `CategoryTheory.ObjectProperty.FullSubcategory`.

I opened the full source, signatures and docstrings of these declarations and the
additional dependency packet's declarations. The added nodes supply the K-flat
predicate and resolutions, universal derived change of rings, canonical reduction tower,
and its independence identities used to interpret the completeness condition.

Edge cases checked before writing: `n=0` in the Lean quantifier means exponent one;
all positive exponents occur. The intervals may include arbitrary negative degrees,
and the singleton interval `r=s` is allowed. A reduction with empty cohomological
support satisfies the interval condition vacuously, with `[0,0]` available when all
supports are empty. No nonemptiness assumption on `Y` is made. No nonzero-cohomology,
finite Tor-amplitude, termwise bounded representative, or integral-amplitude condition
is imposed. The definition does not manufacture triangulated closure.

Searches for an existing definition (2026-10-15):

- `msearch.py leanfinder`: "bounded constructible derived complete integral complexes
  whose finite reductions have uniformly bounded cohomological support" returned eight
  cohomological t-structure and derived-localization results (`isGE_Q_obj_iff`, `isLE_iff`,
  `isGE_iff`, and related instances), none defining this integral subcategory.
- `msearch.py loogle`: "CategoryTheory.ObjectProperty.FullSubcategory, DerivedComplete"
  returned no hits, with unknown identifier `DerivedComplete`. The actual Mathlib
  full-subcategory construction was inspected in its source and reused.
- `msearch.py leansearch`: "derived complete bounded constructible integral category"
  returned "service unavailable: Internal Server Error"; this is an unavailable search,
  not evidence of nonexistence.
- `msearch.py grep`: `DerivedComplete|derivedComplete` in Mathlib `Algebra/Homology`
  returned no hits.
- `rg` in Mathlib, upstream `WeilConjectures` and project `lean/Sheaf` for
  `IsDerivedComplete|boundedConstructibleDerivedCompleteIntegral` found the recorded
  sheaf completeness predicate and a different module-complex completeness predicate,
  but no definition of this bounded constructible integral category. Searching upstream
  for the exact node id found no declaration. Searches for `FullSubcategory` and
  `boundedConstructible` found finite-level/etale categories and rational-coefficient
  framework categories with different objects, none with this completed integral
  ambient category and the stated three conditions.

The blueprint source at order 1459 was opened, along with the corresponding integral
category definition in the slopmaster2 sketch. No node statement fault was found.
The source's triangulated claim was already separated by stage 1; this delivery follows
that recorded statement exactly. No STATEMENT-DISPUTED flag is needed.

Validation: the first scompile exposed stale/incompatible K-flat artifacts in an imported
reduction/tower module, despite the current recorded source having independent coefficient
universes. After supplying the required source packet together, all eight final files compiled
separately, both as sandbox modules and at their declared module paths, without errors or
warnings. This includes the full-subcategory declaration. The three original coefficient,
finite torsion and support modules are used directly from the published library. Final
metadata and the full packet are checked by the prescribed dry run. No build of the library is requested.

## Dependency modules

Each overlay retains the published declarations and mathematical bodies. Its module
comment documents the source packet, and its node changes only in `lean`, with a note.
The packet is necessary because an imported artifact can otherwise bind the old,
site-sized `CochainComplex.IsKFlat` while its recorded source expects independent
coefficient universes. Recompiling the exact coupled interfaces together resolves this
without a new mathematical assumption or arbitrary replacement map.

- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlat` retains `IsKFlat` and
  `IsKFlatResolution`, including their separate coefficient universe and tensor
  localization infrastructure. Its recorded source is the generalized definition;
  the incompatible compiled artifact used the older specialization.
- `lem-pc-kflat-resolution`:
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` retains the K-flat
  resolution theorem, with flat terms and degreewise epimorphic augmentation, compiled
  against that same generalized K-flat predicate.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` retains the
  sectionwise tensor functor, exact left-derived universal pair and its canonical
  K-flat computation. No mere arbitrary functor or Nonempty isomorphism is substituted.
- `def-weil-integral-derived-reduction`: `Sheaf.Paper.IntegralDerivedReduction` retains
  the derived functor selected from its universal derived pair, counit, exactness and
  resolution comparisons. Its old artifact's K-flat predicate had an incompatible
  coefficient universe; the paired sources restore the recorded general signature.
- `lem-weil-integral-reduction-tower-well-defined`:
  `Sheaf.Paper.IntegralReductionTowerWellDefined` retains the pure-tensor formulas,
  uniquely specified unit and transition maps, and canonical comparison identities.
  It is rebuilt against the same reduction/counit and K-flat interfaces.
- `def-weil-integral-reduction-tower`: `Sheaf.Paper.IntegralReductionTower` retains
  the canonical augmented tower and its maps; it is rebuilt against those same
  K-flat resolution and well-definedness interfaces.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedComplete` retains the existential
  distinguished Roos triangle with first map fixed by the canonical reduction cone.
  It is rebuilt against the paired tower interface, not redefined by an arbitrary
  morphism to a chosen derived-limit object.

No new nodes or source-based statement corrections are required.

## Second reading by NB

I read the node statement, its blueprint source at order 1459, and the complete
signatures of all five statement dependencies. The item introduces a prime `l`
distinct from the global characteristic `D.p` (`[Fact l.Prime]`, `hl : l ≠ D.p`),
a finite extension `E` of `Padic l` (`[Field E]`, `[Algebra (Padic l) E]`,
`[FiniteDimensional (Padic l) E]`), and an arbitrary scheme `Y`. The Lean
declaration renders these as `D`, `l`, `hl`, `E`, and `Y` in
`boundedConstructibleDerivedCompleteIntegral`; the global datum is required to
make the source's `p` and `l ≠ p` meaningful and is the interface used by the
completed coefficient construction. No finite-type, separatedness, base-map,
or invertibility hypothesis on `Y` is added.

The node's first conclusion clause is that an object `K` of
`completedIntegralDerivedCategory l E Y D hl` is `IsDerivedComplete`; Lean uses
exactly `IsDerivedComplete l E Y D hl K`. Its second clause is one pair
`r s : ℤ` with `r ≤ s`, independent of the reduction level; Lean has
`∃ r s : ℤ, r ≤ s ∧ ∀ n : ℕ, ...`. For each `n`, the positive quotient level
`A_{E,n+1}` is represented by `integralDerivedReduction ... n`, and Lean
requires `intrinsicFiniteTorsionConstructible ... (n + 1)` with the explicit
proof `Nat.succ_le_succ (Nat.zero_le n)`. This is exactly every source level
`n ≥ 1`, including level one. The final conjunct quantifies every `i : ℤ` and
requires membership in `proEtaleCohomologicalSupport` to imply `r ≤ i ∧ i ≤ s`,
which is precisely containment in one closed interval. The second declaration
is `ObjectProperty.FullSubcategory` on this predicate, matching the source's
full subcategory; no triangulated closure instance is asserted.

Dependency declarations match the node notions: `completedIntegralDerivedCategory`
and its coefficient module category come from `CompletedIntegralCoefficients`,
`IsDerivedComplete` from `DerivedComplete`, the canonical derived reduction from
`IntegralDerivedReduction`, intrinsic finite-torsion constructibility from
`IntrinsicFiniteTorsionConstructibility`, and support from
`ProEtaleCohomologicalSupport`. The seven paired dependency overlays retain the
canonical K-flat, change-of-rings, reduction-tower, and Roos-triangle interfaces;
none substitutes an arbitrary map or a mere existence witness. No new node or
statement correction was needed, and no mismatch was found in the item module.

Edge cases checked: the index `n = 0` is level one; all positive levels occur;
`r = s` is allowed; empty support satisfies the interval implication; degrees may
be negative; the zero object and an empty scheme are not excluded. The scheme
and coefficient field use the dependency declarations' shared ambient universe
`u`; the finite-field datum uses `d`. Site objects have universe `u+1` and
morphisms universe `u`, while the lifted coefficients and module values have
universe `u+1`; these site universes are not equated.

Independent searches: `msearch.py leanfinder` with "constructible integral
complexes with uniformly bounded reductions and derived adic completeness"
returned ordinary `IsAdicComplete` and `AdicCompletion` declarations, which are
module completeness, not this derived sheaf predicate. Loogle with
`ObjectProperty.FullSubcategory` returned unknown identifier and zero hits;
the actual Mathlib source was read and its construction is reused. LeanSearch
with "integral adic constructible derived category" returned service unavailable
(Internal Server Error). Independent `rg` searches for adic constructibility,
uniform amplitude, and integral completeness in Mathlib, the upstream
`WeilConjectures` sources, and `lean/Sheaf` found no exact predicate. In particular
I opened upstream `CategoryTheory/DerivedCategory/Complete/IntegralCoefficient`:
`DerivedCategory.derivedCompleteIntegral` is over `Sheaf J (ModuleCat O_E)`,
requires an embedding into `PadicAlgCl`, and asserts completeness alone. It does
not give this category over the completed coefficient sheaf or its two reduction
conditions, so is not a reusable exact match.

Validation: single-file calls without the siblings exposed the incompatible
published K-flat artifacts described in the worker report; those calls failed
and were not evidence of clean compilation. Passing all eight siblings together
through the prescribed wrapper resolves the dependency chain and compiles every
file separately. `deliver2.py --no-push` completed with
`OK (dry run): commit a5f598b0ba passes the preflight and compiles; nothing pushed`.
The only second-reader change is this independent review and the clarification
of the validation evidence; all Lean definitions and node statements are retained.
