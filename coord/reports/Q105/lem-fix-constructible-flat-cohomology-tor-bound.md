## Worker report

The delivery states `WeilConjectures.constructible_flat_cohomology_tor_bound` in
`Sheaf.Paper.ConstructibleFlatCohomologyTorBound`. Its only mathematical assertion has
proof `sorry`; its docstring carries all six proof steps and their dependencies.
The helper instances supply standard sheafification and derived localization on the
actual slice, without choosing a different abelian structure or adding hypotheses.

The previous worker's claim that the stage-2 item was already reviewed under Q81 was
not supported by the shared node: that node has neither `lean` nor `reviewed_lean`.
The Q81 report and ledger entry are a stage-1 split delivery, explicitly saying no Lean
was written. This delivery adds the missing stage-2 record and statement.

Every hypothesis and clause is rendered as follows:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- The valuation ring, chosen uniformizer, and quotient residue ring are the existing
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing l E 1`. The ideal at level one is the uniformizer ideal,
  hence its quotient is the residue field by the coefficient datum. Using
  `Module.Finite` over this quotient is exactly finite-dimensionality over k; no
  extra field structure is passed as an assumption.
- The affine scheme is `(V : Scheme.{t}) [IsAffine V]`. `_hV` is weak contractibility
  at `ProEt.mk (𝟙 V)` for `ProEt.topology V`, using the existing
  `GrothendieckTopology.IsWeaklyContractible`: locally surjective sheaf morphisms
  are surjective on sections. Local surjectivity and epimorphism of sheaves of sets
  are equivalent, as required by the node. The set universe contains both inputs.
- The completed coefficient ring B is the existing inverse-limit coefficient sheaf
  inside `scalarReductionSource l E V`. Thus `K : DerivedCategory
  (scalarReductionSource l E V)` is exactly a derived B-module sheaf, not a complex
  over the discrete constant ring of integers.
- `_hcomplete : IntegralOnSlice.IsComplete l E V none K` is the recorded
  quotient-tower derived completeness predicate in its global branch.
- `(scalarReductionDerivedExtension l E V 0).obj K` is K_1. The implementation's
  natural-number index zero means exponent one, and its target is exactly the
  constant `(R/(varpi))_V` coefficient ring sheaf with module universe `max u (t+1)`.
- `(a b : ℤ) (_hab : a ≤ b)` gives the ordered interval. `_hbounded` says
  `∀ q, q < a ∨ b < q → IsZero ((homologyFunctor _ q).obj K_1)`.
- `_hlocal` says for every q that this same cohomology sheaf has a pro-etale
  covering family and, on each member, an isomorphism to the sheafification of a
  constant module whose model satisfies `Module.Finite (ULift k) M`.
  The cover and models may depend on q, and M may vary over the cover.
- The conclusion quantifies over every `U : V.ProEt`, without affineness or
  weak-contractibility assumptions on U, and every
  `L : SheafOfModules.{max u (t+1)} ((integralCoefficientSheaf l E V 0).over U)`.
  Thus L is an arbitrary sheaf of modules over precisely k_V restricted to C/U.
- `ringedSiteDerivedRestrictionOfUniverses ... U K_1` restricts the canonical
  representative and localizes on C/U. `singleFunctor _ 0` places L in degree zero.
  `ringedSiteDerivedTensorOfUniverses` resolves a representative of the first
  argument by a K-flat complex, forms its actual total tensor with the second
  representative, and localizes. `IsZero ((homologyFunctor _ i).obj ...)` for
  every `i < a ∨ b < i` is exactly the required sheaf vanishing on that slice.
  There is no evaluation-on-V or evaluation-on-U substitution.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports all coefficient
  constructions of `Sheaf.NumberTheory.Padics.CoefficientExtension` and its finite quotient theorem.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` reexports the actual
  `completedIntegralCoefficientSheafUnrestricted`,
  `integralCoefficientCommRingSheaf`, and `integralCoefficientSheaf` constructions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` with its canonical abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory.standard`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose `none`
  branch is `IsDerivedCompleteUnrestricted` (the augmented quotient Roos triangle).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.SixFunctors.IntrinsicDerivedTensor`: `Scheme.proEtaleDerivedTensor`;
  generalized in the dependency module described below, preserving its K-flat model.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` (the exact Mathlib match of the cohomology node).
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`:
  `Scheme.IsLocallyConstantProEtaleModuleSheaf` and its constant module sheafification;
  generalized in the dependency module below without changing its notion.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `overFunctor`, and `Sheaf.over`; these are the exact
  recorded Mathlib matches for the localized ringed site.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, the recorded unrestricted derived reduction
  along the completed ring's actual quotient projection.

All recorded proof-dependency modules that have declarations are imported, including
exact localized restriction, tensor restriction, bounded-flat K-flatness, the K-flat
resolution, derived tensor descent, tensor exactness, truncation triangles, and the
cohomological long exact sequence. These imports retain the DAG's intended proof plan.

Edge cases checked before drafting: the empty scheme and empty local cover have only
zero sheaves, and the conclusion still quantifies over their actual slices. The zero
complex and zero-dimensional local model are allowed. The singleton interval a=b
retains a degree-a cohomology sheaf, rather than requiring a zero complex. Negative
bounds are unrestricted integers. No finiteness, flatness, boundedness or constancy is
assumed for L. The test object U is arbitrary. The coefficient ring is always the
positive-exponent quotient (index zero for exponent one), never exponent zero. Site
object universe is t+1 and morphism universe t; coefficient universe u is independent,
and all relevant coefficient modules have size max u (t+1). There is no excluded
characteristic, nonemptiness condition, or added geometric hypothesis.

Searches performed:

- `msearch.py leanfinder`: “A bounded complex with flat cohomology sheaves has Tor
  amplitude in its cohomological support on every slice site”; eight results about
  DerivedCategory.IsGE/IsLE and ordinary homology support, no slice-wise Tor theorem.
- `msearch.py loogle`: `DerivedCategory.homologyFunctor, Module.Flat`; zero hits.
- `msearch.py leansearch`: “Bounded locally constant finite dimensional cohomology
  implies Tor amplitude on every slice of the pro etale site”; eight results about
  condensed/discrete sheaves and locally constant functions, no exact match.
- `msearch.py grep`: `TorAmplitude|flat.*[Cc]ohomology` in `Algebra/Homology`;
  zero hits.
- `rg` in WeilConjectures and lean/Sheaf for Tor amplitude, flat cohomology, finite
  local models, and the node id. Read the upstream TorAmplitude and FlatModel
  signatures and the side `AdicTorFlatCohomology` statement: none is this theorem.
  The latter concerns complete integral flat cohomology and higher-Tor equivalences,
  with no arbitrary-slice residue bound. The node-id search found the stage-1 report,
  not an existing Lean declaration.
- `rg` for the proposed declaration names in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json found no collisions.
- Source read: `proetale.tex`, lemma-local-structure-constructible-complex, Tag 09C3.
  The finite residue Tor-amplitude input is justified by the node's finite
  truncation-filtration argument; 09C3 itself is not incorrectly presented as a
  direct assertion of this extra slice-wise conclusion.

No statement correction, new DAG node, or disputed statement is needed.

## Dependency modules

`def-weil-proetale-locally-constant-sheaf`: the recorded declaration uses the same
universe for coefficient ring and scheme and therefore cannot accept the existing
independent-sized quotient coefficient module category. The module
`Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses` gives the same constant module
presheaf, simultaneous ring/module sheafification, actual localized-site constant
module, and coverwise isomorphism definition with independent t,u. Its primary
predicate allows arbitrary varying module models. The helper `WithModels` merely
inserts an explicit predicate on these same models, enabling the item's finite
local-model clause. The two sheafification-unit proof obligations are named theorems
with `sorry`, source references and complete proof plans; all definition data is real.
Only this dependency node's `lean` record changes, with the required explanation.

`def-weil-derived-tensor`: its recorded construction fixes coefficient and scheme
universes and is typed only on the global pro-etale category. The module
`Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses` provides exactly the same
canonical-representative/K-flat-resolution/total-tensor/localization construction
with independent site, coefficient and localization sizes, so it applies on the
actual over-site. It uses the already recorded independent-coefficient K-flat
resolution theorem. No arbitrary tensor functor, Nonempty choice of maps, or test
sheaf flatness hypothesis replaces the canonical construction. The old interface is
publicly imported and preserved. Only the dependency node's `lean` record changes.

Validation: scompile.py compiled each of the three delivered modules separately in
dependency order, including current-server confirmation of all three. Every compile
finished within its per-file 60-second limit, with no errors or unexpected warnings.
All variables and universes are explicitly bound, and every Lean line is at most
100 characters. No direct compilation, global build, shared-source edit or Git command
was run by the worker.

Dry-run repair: preflight reads the dependency signature starting at the `def`
keyword, excluding its `noncomputable` modifier. The lean.statement record now
quotes that exact signature. This was the only initial preflight finding.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
