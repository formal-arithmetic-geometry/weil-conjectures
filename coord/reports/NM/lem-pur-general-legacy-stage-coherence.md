## Worker report

Existing match, with no new Lean module. The node is recorded on
`Sheaf.Paper.AlgebraicallyClosedCoefficients`, with primary declaration
`WeilConjectures.AlgebraicallyClosedCoefficients.stageSystem_existsUnique`.
The record also lists `WeilConjectures.correctedTensorAssociator_formula`,
`WeilConjectures.AlgebraicallyClosedCoefficients.associator_formula`, and
`WeilConjectures.AlgebraicallyClosedCoefficients.associator_cocycle`:
together these give every assertion, rather than recording only the final consequence.
Only the item's `lean` field changes. Its recorded signature is copied verbatim
from the existing theorem, stopping before `:=`.

Source read: the whole current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`,
especially scalar extension and clause (4); the item's retained old argument 5 in
`source.note`; and the actual legacy source, lines 45–111 and 207–472. The item
intentionally fixes the older presentation, and the source module is that exact
presentation. The intrinsic/general stage modules found during search concern
other predicates and are not used as a replacement.

Hypothesis and clause correspondence:

- Global datum: the section variable `D : FiniteFieldDatum.{d}` supplies the prime
  characteristic, exponent, finite base field, and chosen algebraic closure; its
  structure was read in `Sheaf.Paper.FiniteFieldFiber`.
- Prime different from the characteristic: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- Chosen coefficient closure: `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. Mathlib's `Padic` is the Cauchy completion, and
  `IsAlgClosure` requires algebraicity and algebraic closedness.
- Arbitrary scheme: `(Y : AlgebraicGeometry.Scheme.{u})`; there is no morphism
  from Y to the finite-field closure and no geometric finiteness hypothesis.
- Index fields: `Index l Ω := Padic.FiniteCoefficientFields l Ω`, the subtype of
  finite-dimensional intermediate fields, with its inclusion order.
- Canonical small models: `Coefficient.{u} l Ω E := Shrink.{u} E.val`.
  `coefficientSmall` uses finite-basis coordinates to furnish `Small.{u} E.val`;
  `coefficientFinite` transports finite dimensionality. The site universe u,
  closure universe v, and datum universe d are independent.
- Transported inclusion: `coefficientInclusion l Ω E L h` is literally
  `(Shrink.algEquiv (Padic l) L.val).symm.toAlgHom.comp
  ((IntermediateField.inclusion h).comp
  (Shrink.algEquiv (Padic l) E.val).toAlgHom)`.
- Specified integral presentation: `Stage D l hl Ω Y E` unfolds to
  `rationalConstructibleCategory D l hl (Coefficient l Ω E) Y`, whose definition
  in `Sheaf.Paper.RationalizationKaroubi` is `ScalarLocalization` of exactly
  `boundedConstructibleDerivedCompleteIntegralCategory`. Its predicate, read in
  `Sheaf.Paper.DerivedCompleteIntegralDetailed`, is `IsDerivedComplete` and
  `∃ r s : ℤ, r ≤ s ∧ ∀ n : ℕ, ...`, using `integralDerivedReduction ... n`
  at positive level `n + 1`, finite-torsion constructibility, and bounds r,s
  for every cohomological support. This is exactly the uniform-amplitude clause.
- Raw rationalization: `ScalarLocalization` leaves the integral objects intact
  and localizes Hom; no Karoubi completion is introduced in the stage definition.
- Scalar transition: `transition D l hl Ω Y E L h` is exactly
  `rationalScalarExtension D l hl (Coefficient l Ω E) Y
  (Coefficient l Ω L) (coefficientInclusion l Ω E L h)`.
- Specified associator: `tensorAssociator` applies `correctedTensorAssociator`
  to these three small models and the composition equality from
  `coefficientInclusion_laws`. The latter is precisely the recorded declaration
  of `lem-route-coefficient-inclusion-laws`.
- Direct equality transport: `correctedTensorAssociator_formula` says that
  `correctedTensorAssociator ... hij` equals
  `rationalConstructibleScalarComp ... ≪≫
  eqToIso (congrArg (rationalScalarExtension ... ) hij)`.
  Equality of the entire isomorphism includes both the forward and inverse maps.
  The helper's general field-map version is specialized by `tensorAssociator`.
- Named/sealed associator: `associator_formula` identifies `associator` with
  `tensorAssociator`; the unique-existence theorem does not pick arbitrary
  isomorphisms unrelated to the actual tensor construction.
- Cocycle: `associator_cocycle` quantifies over E,L,M,N, inclusion proofs h,k,m,
  and every object K. Its left side is `(transition ... M N m).map
  ((associator ... E L M h k).hom.app K) ≫
  (associator ... E M N (h.trans k) m).hom.app K`; its right side is
  `(associator ... L M N k m).hom.app ((transition ... E L h).obj K) ≫
  (associator ... E L N h (k.trans m)).hom.app K`. This is the displayed equation
  in its written composition order, componentwise for every object.
- Unique system: `stageSystem_existsUnique` states `∃! S : StageSystem (Stage ...)`
  with every `S.T h = transition ... h` and `HEq (S.assoc h k) (associator ... h k)`.
  Heterogeneous equality is needed before the transition equalities are substituted;
  afterwards it is ordinary equality. `StageSystem` has exactly T, assoc, and
  cocycle fields, with no unitor field or condition T at an identity be the identity.

Dependency declarations read and checked:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib `NumberTheory.Padics.PadicNumbers`: `Padic`; Mathlib
  `FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`; Mathlib
  `FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  its finite-dimensional instance, compositum, base, and properties theorem.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory`.
- `Sheaf.Paper.SfScalarExtensionComposition`: `WeilConjectures.sfRationalScalarComp`.
  These last three current dependency records concern the intrinsic presentation.
  The item's text explicitly specifies different legacy declarations and disclaims
  an identification. The exact existing match uses those named legacy declarations,
  already present, without restating or repairing any dependency node.
- `Sheaf.Paper.AlgebraicallyClosedCoefficients`:
  `WeilConjectures.AlgebraicallyClosedCoefficients.coefficientInclusion_laws`.
- `Sheaf.CategoryTheory.ExactStagePairData`:
  `CategoryTheory.StageSystem.ExactStagePairData`, which packages the existing
  `CategoryTheory.StageSystem` from
  `WeilConjectures.CategoryTheory.StageSystem.Basic`. This item uses only its
  underlying stage-system notion, not the additional exact-stage pair data.
- Proof input `lem-pur-legacy-rational-tensor-pentagon` has no Lean record yet.
  Its equation is already the third conjunct of the existing
  `WeilConjectures.rationalConstructibleScalar_coherence`, read in
  `Sheaf.Paper.ScalarExtensionComposition`; the existing cocycle proof specializes
  it through equality transport. No new module needs an unstated dependency.

Edge cases checked by inspecting the quantifiers and constructions: h,k,m need not
be strict inclusions, so repeated fields and all-identity chains are included;
there is no exclusion of the zero object or empty scheme. No equality of coefficient
closure and scheme universes is imposed. Positive reduction powers start at n+1;
the interval is chosen once before all n, including for zero objects. The finite
base coefficient field provides a nonempty index, and compositum gives directedness.
No choice of a unitor is introduced as part of the unique stage system.

Searches performed with `msearch.py`:

- LeanFinder: "Tensor scalar extension associators transported along inclusions of
  small coefficient field models satisfy the stage cocycle and determine a unique
  stage system". Eight hits, including `ModuleCat.extendScalars_assoc`,
  `ModuleCat.extendScalars_assoc'`, and `TensorProduct.AlgebraTensorModule.assoc`;
  none is the specified legacy constructible stage result.
- Loogle: `CategoryTheory.eqToIso`. Twelve generic equality-isomorphism hits;
  no exact legacy coefficient-stage theorem.
- Grep: `correctedTensorAssociator|stageSystem_existsUnique|associator_cocycle`.
  One Mathlib hit, the unrelated ring associator cocycle.
- LeanSearch: "Coherence of tensor scalar extension associators transported along
  equal coefficient maps and uniqueness of fixed stage system data". Eight hits,
  primarily module scalar-extension coherence; no exact constructible-stage match.
- Local `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no upstream declaration with these names;
  the Sheaf legacy module gives the exact match above. Other general/intrinsic
  coefficient stage modules have similar names but different category predicates.
  The item id itself has no existing source occurrence.

No statement correction, new node, dependency module, or disputed clause.
Validation: the delivery tool generates server `#check @...` probes for every
recorded existing declaration and sends them through `scompile.py`; there is no
new module to compile or proof to write. Dry-run and delivery results are recorded
by the prescribed tools.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
