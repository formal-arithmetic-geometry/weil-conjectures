## Worker report

The module `Sheaf.Paper.TraceFormulaTopologicalInvariance` states
`WeilConjectures.finiteUniversalHomeomorphism_traceFormula`, with one `sorry`.
Its helper `WeilConjectures.TraceFormulaTopologicalEquivalence` is a real
Prop-valued definition packaging exactly the conclusion: an equivalence of the
existing full finite-Tor constructible subcategories, naturally identified with
the existing pullback and the two existing direct images. It does not construct
another coefficient category or another operation. Both declarations belong to
`i-topology`; the helper introduces no independent mathematical notion.

The item statement is unchanged. I read its statement, six proof steps, all six
statement-dependency records and their actual declarations/docstrings, the current
blueprint proposition and proof in `main-20261015`, and the example compact-object
module and record. No statement correction or new node is needed. The Q117 route
note concerns an earlier stage-1 handoff, already reflected in the current reviewed
node; the preparation directory named there is absent on this machine. This
delivery follows the current Q13 stage-2 brief and preserves all existing citations.

Clause-by-clause correspondence:

* The coefficient conventions are the binder
  `T : TraceFormulaCoefficientConventions.{u}`. Its datum stores `p,a,q,k₀,k`,
  including the algebraic closure, and its coefficient datum stores a prime
  `T.coefficients.l` different from `T.datum.p`, with a fixed algebraic closure
  of the corresponding p-adic field. Its `extension` is the finite intermediate
  field, `coefficientField` is its recorded small model, and `coefficientRing`
  is exactly `O_E / ϖ_E ^ T.level`; `T.level_pos` is `1 ≤ T.level`.
  The stored model `T.X₀` is not used to restrict the schemes of this theorem.
  Any allowed coefficient datum can be packaged in such a `T` (choose, for
  example, the point over `k₀` for that otherwise irrelevant model).
* The geometric setting implicit in the cited conventions and explicit in proof
  step 1 is expressed by arbitrary `X Y : Over (Spec (CommRingCat.of T.datum.k))`.
  Their six typeclass binders are exactly separatedness, local finite type and
  quasi-compactness of each structure morphism. The last two together mean finite
  type. `r : X ⟶ Y` is a morphism over this same geometric field. In particular
  it need not descend to any specified finite-field model.
* "Finite" is `[IsFinite r.left]`, using the recorded Mathlib definition.
  "Universal homeomorphism" is the explicit hypothesis
  `(topologically IsHomeomorph).universally r.left`, exactly the inline
  specialization recorded on `def-weil-universal-homeomorphism`.
* `D^b_ctf(Y,A)` and `D^b_ctf(X,A)` are the existing
  `finiteTorConstructibleCategory T.coefficients.l T.coefficientField
  T.level T.level_pos Y` and its `X` counterpart. They include both intrinsic
  finite-torsion constructibility and the existing finite-Tor-amplitude condition.
  Neither condition is omitted or replaced by an abstract arbitrary predicate.
* "Pullback is an equivalence" is the existential `e : ... Y ≌ ... X`, with
  the first natural isomorphism identifying `e.functor`, after inclusion, with
  inclusion followed by `T.derivedPullback r`. Thus this is the recorded exact
  derived inverse image, and it really takes values in the indicated subcategory.
* "With inverse Rr_*" is the second natural isomorphism identifying
  `e.inverse`, after inclusion, with inclusion followed by
  `proEtaleConstantDerivedDirectImage r T.coefficientRing`. This is exactly
  the finite-level K-injective right-derived direct image used in the recorded
  `SfDerivedDirectImage` module, not an arbitrary supplied inverse functor.
* "Rr_* = Rr_!" is the third natural isomorphism, identifying this same
  inverse with `sfIntrinsicCompactSupport c T.coefficientRing`. Here `c` is
  any specified compactification of `r`, as in the compact-support definition.
  It is an arbitrary parameter, not an existence or independence hypothesis.
  These are natural functor identifications, rather than objectwise isomorphisms.
  In particular they identify the two direct images on precisely `D^b_ctf`.
  Finite morphisms have the proper compactification `(id,r)`, so this parameter
  does not make the claim vacuous. The finite coefficient instance passed to
  this existing construction is the named theorem
  `Padic.finite_coefficientExtensionRing ... T.level T.level_pos`.
* "Invertible unit and counit" is part of the equivalence type `≌`: `e.unitIso`
  and `e.counitIso` are natural isomorphisms and satisfy the equivalence triangle
  identity. Transport across the displayed natural identifications gives the
  adjunction between the recorded restricted operations. Any specified
  adjunction between those functors also has invertible unit and counit, since
  its left and right functors are equivalences. No extra adjunction-equivalence
  hypothesis is assumed.
* "This includes reduction" is the second conjunct, for every geometric `Y`:
  the helper is applied to `Y.left.nilradical.subschemeι`, whose source is
  `Y.left.nilradical.subscheme`. There is no hypothesis asking a caller to
  prove finiteness or universal-homeomorphism for reduction. It gives the same
  three functor identifications and equivalence, for every specified
  compactification of the reduction immersion.

Dependencies used, with their actual interfaces:

* `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `coefficientField`,
  `coefficientRing`, and `derivedPullback`. Its category abbreviations use
  `WeilConjectures.finiteTorConstructible` and
  `WeilConjectures.finiteTorConstructibleCategory` from
  `Sheaf.Paper.FiniteTorAmplitude`; these are used directly at arbitrary `X,Y`.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  The integral companion of that dependency is not required by this item.
* `Mathlib.CategoryTheory.MorphismProperty.Limits`:
  `CategoryTheory.MorphismProperty.universally`;
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`:
  `AlgebraicGeometry.topologically`; `Mathlib.Topology.Homeomorph.Defs`:
  `IsHomeomorph`.
* `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `AlgebraicGeometry.Scheme.nilradical`,
  `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` and `subschemeι`.
* `Sheaf.Paper.SfDerivedDirectImage`:
  the finite-level operation `proEtaleConstantDerivedDirectImage`, reexported
  from `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
  In particular `sfFiniteDerivedDirectImage` applies this functor to a finite
  scalar reduction; we use its underlying functor on arbitrary finite objects.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`, the exact existing
  intrinsic realization of the compact-support dependency (see below).
* Recorded proof interfaces are imported for pro-etale sheaf invariance, the
  geometric setup, the constant-ring identification, exact pullback, the
  functor-package attachment, and reduction. The proof docstring spells out
  all six DAG steps. `thm-sf-ctf-stability` and `sk-d-six` have no recorded Lean
  declaration yet; no extra hypothesis replaces these future proof inputs.
  The inherited `prop-functor-package` Lean attachment concerns Weil-complex
  base change and does not itself state all the package clauses in the node.
  It is imported as recorded, but its stronger source claim is not silently
  taken as an added assumption in this stage-2 statement.

Searches performed on 2026-10-18:

* `msearch.py ... leansearch` with "Derived constructible sheaves are
  invariant under universal homeomorphisms of schemes": eight hits, including
  stability of étale maps and universally closed maps, a homeomorphism attached
  to a scheme isomorphism, and a presheaf comparison for topological spaces.
  None states the required derived pro-etale finite-Tor equivalence.
* `msearch.py ... leanfinder` with "Pullback along a finite universal
  homeomorphism is an equivalence on bounded constructible finite Tor amplitude
  proetale complexes": eight hits, including `IsFinite` base-change instances,
  étale pullbacks, and a sheaf-module coefficient-unit isomorphism; no exact
  derived-constructible equivalence statement.
* `msearch.py ... loogle` with `"ProEtale"`: twelve Mathlib hits defining the
  big pro-etale topology, precoverage, stability, subcanonicality and comparisons
  with étale/fpqc topologies; no topological-invariance theorem.
* `msearch.py ... grep` with
  `universalHomeomorphism|UniversalHomeomorphism|topological.invariance` in
  `AlgebraicGeometry`: zero Mathlib hits. Direct `rg` of the same subject in
  Mathlib's algebraic geometry sources likewise found no exact theorem.
* `rg` in the source project's `WeilConjectures`, the side project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, and `grep -rn i-topology`
  in the upstream pro-etale sources, found and led me to read
  `ProEtale/UpperLowerStar/TopologicalInvariance.lean` and
  `ProEtale/TraceFormula/Frobenius.lean:570-617`. The former gives sheaf
  equivalences; the latter gives ambient derived equivalence and unit/counit
  invertibility, while its finite-Tor assertion depends on an arbitrary
  `GeometricOperations A s` package with its own `G.ctf`. That package is not
  the recorded intrinsic `finiteTorConstructible` property and cannot be
  introduced as a hypothesis here. Thus these declarations do not already
  state this item's full concrete assertion. The existing side
  `proEtaleSheaf_topological_invariance` concerns set sheaves only.
* New names `TraceFormulaTopologicalEquivalence` and
  `finiteUniversalHomeomorphism_traceFormula` were checked for collisions in
  Mathlib, the source project, the side library and the upstream-name index.
* The compact-support dependency's current upstream source was read using
  `scompile.py --source
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`.
  Its signature confirmed the endpoint mismatch discussed below, while the
  existing intrinsic compact-support module supplies the exact needed form.

Edge cases checked before the statement: identity maps; the empty scheme and
its reduction; reduced schemes; nonreduced finite-type schemes such as dual
numbers; Frobenius on a positive-dimensional scheme in characteristic `p`;
all positive levels including `n=1`; nontrivial nilradicals; and the zero
complex. No nonemptiness, smoothness, regularity, étaleness or fixed dimension
is imposed. `n=0` is excluded by the source coefficient conventions, not by an
extra hypothesis. Finite Tor amplitude remains an explicit condition even
for finite non-field coefficients. There is one explicit universe `u`, with
the recorded pro-etale site in object universe `u+1`, morphism universe `u`,
and the coefficient modules in their recorded larger universe; no site
universe equality or finiteness-of-space assumption is imposed.

No `STATEMENT-DISPUTED` issue was found. The sole new theorem's proof is
`sorry`; the helper contains real data and no postponed proof. The module
passed the prescribed per-file `scompile.py` check with no errors or warnings.
Delivery preflight and the required final compile are run by `deliver2.py`.

## Dependency modules

`def-compact-support-direct-image-detailed`: this is a lean-only section 1(B)
repair to an exact existing declaration; there is no new dependency module.
Its old `rightDerivedLowerShriekOfCompactification` lives between derived
categories of fixed-ring `ModuleCat`-valued sheaves. The coefficient
conventions for this item instead use the existing intrinsic
`SheafOfModules` category over the canonical constant-ring sheaf. The existing
`AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` in
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` is exactly the same
compactification formula: termwise exact `j_!`, then K-injective `Rg_*`,
through the canonical published coefficient realization, on those endpoints.
The dependency's `lean` record is repointed to it with `existing: true` and
a note. Its statement, source, compactification scope and every other field
are untouched; its earlier fixed-scalar realization remains available.
The main module's clean compile checks this repaired interface against the
actual consumer. No arbitrary coefficient isomorphism or arbitrary inverse
functor is assumed.

## Second reading by Q13

An independent reading, done at the maintainer review (2026-10-18), with the node, its six
statement dependencies, the module and every declaration used open. The worker's text was
not used as a guide.

The node's statement, item by item, with the Lean that renders it and the verdict:

1. Setting (def-trf-coefficient-conventions; proof step 1): `A = O_E/ϖ_E^n`, `n ≥ 1`, `ℓ ≠ p`,
   with `X, Y` separated finite-type schemes over `k = F̄_q`. Lean: the binder
   `T : TraceFormulaCoefficientConventions.{u}` (with `T.coefficientRing =
   Padic.coefficientExtensionRing ℓ E T.level` and `T.level_pos : 1 ≤ T.level`), and
   `X Y : Over (Spec (CommRingCat.of T.datum.k))` with `IsSeparated`, `LocallyOfFiniteType`
   and `QuasiCompact` on each structure map. Correct. Nothing stronger is assumed. The stored
   `T.X₀` is not used. Since every separated finite-type scheme over `k` is allowed, the
   statement covers the convention's `X₀ ×_{k₀} k` and is no weaker.
2. `r : X → Y` finite: `(r : X ⟶ Y) [IsFinite r.left]`, the recorded Mathlib `IsFinite` of
   def-weil-finite-integral-morphism. Correct.
3. `r` is a universal homeomorphism: `(topologically IsHomeomorph).universally r.left`,
   the inline form recorded on def-weil-universal-homeomorphism. Correct.
4. `D^b_ctf(Y,A)` and `D^b_ctf(X,A)`: `finiteTorConstructibleCategory … Y` and `… X`, i.e.
   the full subcategory of `intrinsicFiniteTorsionConstructible ⊓ HasFiniteProEtaleTorAmplitude`
   in `proEtaleDerivedCategory _ T.coefficientRing`. This is the same predicate as
   `T.boundedConstructibleFiniteTor` of the conventions module, at an arbitrary scheme.
   Correct.
5. `r^*` is an equivalence: `∃ e : D^b_ctf(Y) ≌ D^b_ctf(X)` with
   `e.functor ⋙ ι_X ≅ ι_Y ⋙ T.derivedPullback r.left`. Here `derivedPullback (f : Y ⟶ Z) :
   D(Z) ⥤ D(Y)` is the recorded finite pullback, so the direction `Y → X` is right. Correct.
   This also says that `r^*` preserves `D^b_ctf`, as it should.
6. Its inverse is `Rr_*`: `e.inverse ⋙ ι_Y ≅ ι_X ⋙ proEtaleConstantDerivedDirectImage r.left
   T.coefficientRing`, the K-injective right-derived functor of the recorded module direct
   image. It is the finite-level functor that `sfFiniteDerivedDirectImage` of the recorded
   def-weil-derived-direct-image module applies. Correct.
7. `Rr_* = Rr_!`: `e.inverse ⋙ ι_Y ≅ ι_X ⋙ sfIntrinsicCompactSupport c T.coefficientRing` for
   every `c : Compactification r.left`. Here `sfIntrinsicCompactSupport c = (j_!)_der ⋙ R(c.g)_*`,
   built from the recorded intrinsic extension by zero (def-weil-extension-by-zero) and the same
   derived direct image. Correct.
   Check that it is true for every compactification (the upstream `Compactification` does not
   require `c.i` to be quasi-compact): `r = c.i ≫ c.g` with `r` universally closed and `c.g`
   separated, so `c.i` is universally closed. It is therefore an open and closed immersion, so
   `j_! = j_*`, and `R(c.g)_* j_* ≅ Rr_*`. The clause therefore holds with no etale-origin
   restriction. It is not vacuous, because `Compactification.ofIsProper r` exists.
8. Invertible unit and counit: these are `e.unitIso` and `e.counitIso`. Moreover, by 5 and 6,
   any adjunction between the restricted `r^*` and `Rr_*` is an adjoint equivalence, so its unit
   and counit are invertible. Correct, and no extra hypothesis is assumed.
9. "This includes reduction": the second conjunct, for every separated finite-type `Y` over `k`
   and every compactification of `Y.left.nilradical.subschemeι` (def-weil-pbc-scheme-reduction).
   No finiteness or universal-homeomorphism hypothesis is asked of the caller. Correct.

Edge cases: empty `X`/`Y` (both categories are zero, and the statement is true); identity `r`;
`n = 1`; nonreduced `Y` (dual numbers) and reduced `Y`, where `subschemeι` is an isomorphism;
the zero complex; Frobenius on `A^1_k`. `n = 0` is excluded by `T.level_pos`, as in the source.
Universes: a single universe `u` (`k`, `E` and all schemes in `u`, the site at `u+1/u` as
recorded); none is left unbound and no equality is forced.

Searches: the upstream `proEtaleSheaf_topological_invariance` only concerns set sheaves. The
slopmaster2 `TraceFormula/Frobenius` results live on fixed-ring categories, or through a
`GeometricOperations` package. Neither is this statement. The side tree has no other `i-topology`
declaration.

Dependency record (§1(B)): def-compact-support-direct-image-detailed is repointed, with
`existing: true` and a note, to `sfIntrinsicCompactSupport`. Its recorded statement is verbatim
the file's signature. This is the presentation whose endpoints are the intrinsic categories of
def-trf-coefficient-conventions, and whose ingredients are the recorded intrinsic extension by
zero and derived direct image. The base record (Q98, 2026-10-17) points to the fixed-ring
`rightDerivedLowerShriekOfCompactification`, which Q98's consumer still uses. Both are the same
`Rg_* j_!` in two presentations, and no landed module breaks. The maintainer should note that
this record has now alternated Q34 → N5 → Q98 → Q13.

Module: no hollow definition (the helper is a real Prop). Exactly one `sorry`. The module and
both declarations carry the source and `(blueprint: i-topology)`. The theorem docstring gives
all six proof steps. `lean.statement` is verbatim. `nt_compile.py` reported no errors or
warnings.

Changed: only this section (H11). The previous text was a placeholder, not a reading.
