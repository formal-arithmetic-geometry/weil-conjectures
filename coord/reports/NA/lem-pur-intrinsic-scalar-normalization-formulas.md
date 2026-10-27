## Worker report

This delivery states `lem-pur-intrinsic-scalar-normalization-formulas` in
`Sheaf.Paper.IntrinsicScalarNormalizationFormulas`. The node's statement,
statement dependencies, proof and proof dependencies are unchanged. There are
five theorem statements, all with `sorry`, and one helper definition with real
data. No new DAG nodes or dependency repairs are needed.

Source read: the whole current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md`;
`SfScalarExtensionComposition.lean`, especially the normalized comparison,
integral composition and rational composition declarations; and
`GeneralAlgebraicallyClosedCoefficientStages.lean`, the actual coefficient
models, integral transition shift normalization and rational associator.
The blueprint describes exact termwise derived scalar composition; the
intrinsic source modules fix the particular comparisons in this node.

Hypotheses and clauses, matched individually:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The arbitrary algebraic closure is
  `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
  The scheme is `(Y : AlgebraicGeometry.Scheme.{u})`, with `u` and `v`
  independent. Every variable and universe is explicitly declared; autoImplicit
  is disabled. There is no geometric structure map or finite-field datum.
- Finite subfields E, L, M and inclusions are `(E L M : Index l Ω)` and
  `(h : E ≤ L) (k : L ≤ M)`. `Index` is exactly
  `Padic.FiniteCoefficientFields`, not an arbitrary family of fields.
  `Coefficient.{u} l Ω E` uses the recorded finite-basis Small witness and
  `Shrink`; `coefficientInclusion` is the recorded conjugated inclusion.
- R_F is the recorded `completedIntegralCommRingSheafUnrestricted`, with
  the underlying ring-sheaf and module category used by `integralTowerModules`
  and `scalarReductionSource`. Ambient categories are the actual
  `DerivedCategory`; integral objects are
  `sfIntegralConstructibleCategory`. Their inclusion is
  `(sfIntegralConstructible ...).ι`, the full faithful ObjectProperty inclusion.
  The inclusion comparisons beta and coherent shifts are its inherited
  `commShiftIso`, enabled by `SfIntegralConstructibleTriangulated`.
- U is `integralTransition`, the published restricted completed extension
  with characteristic proof parameter zero. Its proof is
  `Nat.Prime.ne_zero (Fact.out : l.Prime)`. Q is
  `sfRationalConstructibleLocalization`, the raw ScalarLocalization functor.
  T and a are `transition` and `associator` in
  `GeneralAlgebraicallyClosedCoefficients`. No Karoubi completion appears.
- Chi is exactly `sfIntegralOrdinaryComparison`, with direction ordinary
  extension after inclusion to integral extension followed by inclusion.
  Ordinary module extension is the actual `integralOrdinaryScalar`, whose
  witness specifies `SheafOfModules.changeOfRings` on objects and maps.
  `intrinsicOrdinaryScalar_exact` states Additive, PreservesFiniteLimits and
  PreservesFiniteColimits for every coefficient inclusion. It applies to all
  sheaves, rather than only constructible objects.
- C^ord is `integralOrdinaryDerivedScalar`; its definition is literally
  `(integralOrdinaryScalar ...).mapDerivedCategory`. Thus the exact termwise
  construction uses the recorded `Functor.mapDerivedCategoryFactors`, with
  no extra chosen functor, resolution, or boundedness assumption.
- Alpha is the actual `integralOrdinaryDerivedScalarComp`. Its body is
  `(Functor.mapDerivedCategoryCompIso ...).symm ≪≫
  Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarComp ...)`.
  `intrinsicOrdinaryScalarComp_tensor` states the requested multiplication
  formula for every module N, every local object V, and every c, b, x:
  the nested `integralOrdinaryTensorSection` is sent to the generator with
  coefficient `c * integralCompletedScalarMap ... b`. This uses the actual
  sheaf tensor section map, including sheafification, not an abstract tensor
  associator without normalization.
- The helper `intrinsicIntegralScalarAssociator` is exactly
  `sfIntegralScalarComp` followed by `eqToIso (congrArg ...
  ((coefficientInclusion_laws l Ω).2 E L M h k))`. It has endpoints
  `integralTransition E L ⋙ integralTransition L M` and the transition E M
  for `h.trans k`. Its data is a composite of existing isomorphisms, not a
  theorem choice or an arbitrary comparison.
- The first displayed equation is `intrinsicIntegralScalarAssociator_image`.
  Its left side is inclusion `.ι.map` of that actual transported integral
  component. Its right side, in Lean's left-to-right order `≫`, is
  chi_LM inverse, ordinary extension of chi_EL inverse, alpha, chi_EM.
  On the right the final coefficient hom is the composed inclusion;
  `HEq` expresses the endpoint identification with the direct inclusion,
  as explicitly permitted by the node. In particular no equality cast is
  silently discarded from the definition of b.
- The second displayed equation is `intrinsicIntegralTransition_shift`.
  Its left side is inclusion of the prescribed U `commShiftIso n` component
  followed by the target inclusion `commShiftIso n` component beta. Its
  right side is chi at shifted K inverse, the `commShiftIso n` of the
  composite source inclusion followed by ordinary derived extension (h),
  and the ambient shift functor applied to chi at K. This is precisely
  beta o I(tau) = chi[n] o h o chi_shifted^{-1}. The shift is the actual
  `integralTransitionCommShift`, not an arbitrary exact-functor witness.
- The last displayed equation is `intrinsicRationalScalarAssociator_image`.
  Its left side is the specified stage `associator` at `Q_E.obj K`; its
  right side is `Q_M.map` of the very same transported integral compositor.
  `HEq` retains the object equalities of rational scalar extension.
- All statements quantify over every K, and the shift statement over every
  n : ℤ. Indices need not be distinct. No invertibility, finite dimension
  of Y, Noetherianity, finite base field, or idempotent completion is imposed.

Dependency declarations read and used (the mathematical signatures and
source docstrings were inspected, including construction bodies where they
fix a canonical choice):

- Mathlib.NumberTheory.Padics.PadicNumbers: `Padic`; and
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure / Basic:
  `AlgebraicClosure`, `IsAlgClosure`.
- Sheaf.NumberTheory.Padics.FiniteCoefficientFields:
  `Padic.FiniteCoefficientFields`, its finite-dimensional instance.
- Sheaf.Paper.AlgebraicallyClosedCoefficients:
  `Index`, `coefficientSmall`, `Coefficient`, `coefficientInclusion`,
  `coefficientInclusion_laws` in `WeilConjectures.AlgebraicallyClosedCoefficients`.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses:
  `integralConstantToCompletionOfUniverses` and the retained actual completed
  coefficient sheaves, with independent coefficient and site sizes.
- Mathlib.Algebra.Homology.DerivedCategory.Basic:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- Sheaf.CategoryTheory.RingedSiteModules:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- Sheaf.Paper.SfIntegralConstructible:
  `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- Sheaf.Paper.SfIntegralConstructibleTriangulated:
  `sfIntegralConstructible_isClosedUnderIsomorphisms`,
  `sfIntegralConstructible_isTriangulated` and inherited inclusion shifts.
- Sheaf.Paper.IntegralScalarExtensionUniverses:
  `integralScalarExtensionOfUniverses` and retained original constructions;
  the actual restricted functor is `sfConstructibleIntegralScalarExtension`
  from IntegralScalarExtensionConstructibleIntrinsic, used by integralTransition.
- Sheaf.Paper.SfScalarExtensionComposition:
  `sfIntegralOrdinaryComparison`, `sfIntegralScalarComp`,
  `sfRationalScalarComp` and their existsUnique specifications.
  Its publicly imported ScalarExtensionComposition provides
  `integralOrdinaryScalarComp`, `integralOrdinaryDerivedScalarComp`,
  `integralOrdinaryTensorSection`; IntegralScalarExtension provides
  `integralOrdinaryScalar`, its exactness, `integralOrdinaryDerivedScalar`.
- Sheaf.Paper.SfRationalizationKaroubi:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`.
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages:
  `integralTransition`, `integralTransitionCommShift`, `transition`,
  `scalarAssociator`, `associator`, and their normalization specifications.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  `SheafOfModules.cochainModulesMonoidal`, the retained ordinary sheaf tensor.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors` and shift comparison.
- Proof imports retain CompletedIntegralFiniteFree, ScalarLocalization,
  Localization.Predicate, Functor.FullyFaithful and Shift.CommShift, for
  the exact proof route (finite freeness, bilinearity, localization uniqueness,
  fully faithful component lifting, and normalized composite shifts).

Edge cases checked before writing: E=L, L=M and E=L=M (no strict inclusion
binders, and coefficient identity extension is not replaced by a literal identity
functor); K=0; the empty scheme Y; shifts n=0 and negative n; ell=2; arbitrary
relative sizes of Ω and Y. Each construction remains defined in these cases.
The characteristic parameter requires only l≠0, already implied by primality.
There is no mathematical counterexample, disputed statement, missing notion,
unusable dependency, or source correction found.

Searches actually run via msearch.py for NA and this item:

- leanfinder: "The intrinsic completed integral scalar associator is ordinary
  derived tensor associativity conjugated by comparison isomorphisms, and
  rationalization maps its components to the rational associator". Eight hits,
  including HomologicalComplex.associator and TensorProduct.assoc_tensor variants;
  none states the intrinsic comparison identities for the published constructions.
- loogle: `"mapDerivedCategoryComp", "commShiftIso"`. Zero hits.
- grep: `sfIntegralScalarComp|sfIntegralOrdinaryComparison|integralTransitionCommShift`.
  Zero Mathlib hits.
- leansearch: "For intrinsic integral constructible sheaves the completed scalar
  extension composition and integer shift comparisons have their normalized
  ordinary derived images and rationalization images". Eight hits: generic
  derived shifts, exact-induced shift comparisons and sheafification/pullback;
  no intrinsic component normalization formula.
- rg over lean/WeilConjectures for sfIntegralScalarComp,
  sfIntegralOrdinaryComparison and the node id: no match.
- rg over lean/Sheaf located the construction specifications in
  SfScalarExtensionComposition and GeneralAlgebraicallyClosedCoefficientStages,
  plus the ordinary derived associator definition in ScalarExtensionComposition.
  No existing declaration states the complete node; those definitions are
  reused directly. The new declarations' names were checked against those trees.

Validation: the first server compile was clean (sandbox 42.7 s, module 21.2 s).
The final file only adds explicit direct dependency imports; its final compile
and the required delivery preflight are recorded by deliver2.py below.
Independent mathematical review is performed by the maintainer as specified
in this dispatcher's brief; no independent second-reader claim is made here.

## Repair of returned head 237bd88e8de7

The sole return entry is an `--apply-fixes` filename/shape rejection. It names
`lem-pur-intrinsic-scalar-normalization-formulas.json`, which is a whole existing
DAG node and is not an accepted reviewer fix filename. The reviewer interface
`tools/merge_delivery.py`, stage-2 `cmd_merge2`, accepts the item's Lean record
under `lem-pur-intrinsic-scalar-normalization-formulas.lean-record.json`. Its
contents must be the `lean` object itself, without an outer node or `lean` key.
The rule was read in the source; no tool was edited or bypassed.

Repair applied: the retained sandbox now supplies that correctly named Lean-only
JSON export. The record below is also included verbatim in this delivered report
so the maintainer can create the accepted fix input without access to the worker
sandbox. The node's `lean.note` documents the distinction. The ordinary stage-2
delivery still supplies the full node at its required `dag/nodes/...` path; it
is not a reviewer `--apply-fixes` directory. Do not put that whole-node file,
`report.md`, or `searches.jsonl` in a reviewer fix directory.

For a reviewer fix, use an otherwise empty directory containing only
`lem-pur-intrinsic-scalar-normalization-formulas.lean-record.json` with this
content (and, only when separately needed, the other accepted module/report
fix files). The new delivery itself needs no reviewer record override.

```json
{
 "module": "Sheaf.Paper.IntrinsicScalarNormalizationFormulas",
 "declaration": "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicIntegralScalarAssociator_image",
 "declarations": [
  "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicIntegralScalarAssociator",
  "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicOrdinaryScalar_exact",
  "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicOrdinaryScalarComp_tensor",
  "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicIntegralScalarAssociator_image",
  "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicIntegralTransition_shift",
  "WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicRationalScalarAssociator_image"
 ],
 "file": "lean/Sheaf/Paper/IntrinsicScalarNormalizationFormulas.lean",
 "statement": "theorem intrinsicIntegralScalarAssociator_image\n    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)\n    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :\n    HEq\n      ((sfIntegralConstructible l (Coefficient.{u} l Ω M) Y).ι.map\n        ((intrinsicIntegralScalarAssociator l Ω Y E L M h k).hom.app K))\n      ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)\n          (coefficientInclusion l Ω L M k) Y).inv.app\n            ((integralTransition l Ω Y E L h).obj K) ≫\n        (integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)\n          (coefficientInclusion l Ω L M k) Y).map\n            ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)\n              (coefficientInclusion l Ω E L h) Y).inv.app K) ≫\n        (integralOrdinaryDerivedScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)\n          (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)\n          (coefficientInclusion l Ω L M k)).hom.app K.obj ≫\n        (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M)\n          ((coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h)) Y).hom.app\n            K)",
 "branch": "sheaf-dag",
 "by": "NA",
 "date": "2026-10-27",
 "existing": false,
 "note": "All three specified normalization formulas, ordinary exactness and local tensor-generator multiplication, using the published intrinsic categories and actual canonical coefficient transports. The real-data helper appends the inclusion-composition equality to sfIntegralScalarComp; HEq retains endpoint identifications. Scheme universe u and closure universe v are independent. Returned-head repair 237bd88e8de7: this is the lean record only; for reviewer --apply-fixes it belongs in lem-pur-intrinsic-scalar-normalization-formulas.lean-record.json, not in a whole-node <id>.json fix. The ordinary delivery retains the required DAG node path."
}
```

Comparison with current main: the module is absent and the item has no Lean
record. Parsing the full retained node and the current node found only the
expected `lean` difference. The mathematical statement, its dependencies, and
the proof are identical. The retained Lean source is the source from the
returned delivery; the return lists no compiler failure or statement defect,
so its declarations are preserved. This repair changes the delivered review
instructions and Lean metadata and supplies the accepted fix payload, rather
than merely rebasing or repeating the prior packet.

All validation is repeated through the prescribed scompile.py and deliver2.py
wrappers against current published sources. No direct repository writes or Git
commands are used.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review correction (2026-10-27, review of c91de76b)

The returned head 237bd88e was returned only because the reviewer's fix used a whole-node
JSON file name; its mathematical correction stands and is applied again here. The helper
`intrinsicIntegralScalarAssociator` duplicated, body for body, the published
`SfStrictDirectImageScalar.integralAssociator` (def-sf-strict-direct-image-integral-coherence)
and `FiniteRestrictionCoefficientCore.integralAssociator` (def-zl-finite-restriction-integral-diagram).
Neither owner is a statement dependency of this item, so the helper is removed and the same
composite (`sfIntegralScalarComp ≪≫ eqToIso (congrArg … (coefficientInclusion_laws l Ω).2 E L M h k)`)
is written inline in `intrinsicIntegralScalarAssociator_image` and
`intrinsicRationalScalarAssociator_image`. The mathematics is unchanged. `lean.declarations`,
`lean.statement` and `lean.note` are updated through
`lem-pur-intrinsic-scalar-normalization-formulas.lean-record.json`. The record in the section
"Repair of returned head 237bd88e8de7" above is superseded: it still lists the removed helper.

