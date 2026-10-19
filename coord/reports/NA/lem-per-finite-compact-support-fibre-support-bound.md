## Worker report

The module `Sheaf.DeligneLaumon.FiniteCompactSupportFibreSupportBound` states
`AlgebraicGeometry.Etale.finiteCompactSupportFibreSupportBound`. Its sole theorem has
proof `sorry`; there are no new definitions or helper theorems. The docstring reproduces all
ten steps of the DAG proof, with the cited nodes, and imports all recorded statement and
proof dependency modules (Mathlib leaves through their owning modules).

The node statement is unchanged. This is the finite-coefficient sheaf estimate used by
BBD 4.2.4 and by Step 2 of the parent `lem-per-artin-gabber-affine-curve`. I read BBD 4.2.4
in the local PDF using pdftotext, and the parent's proof in the main-20261015 blueprint.
BBD 4.2.4 gives the amplitude statement; the DAG supplies the detailed fibrewise support
argument for this sheaf-level estimate. No adic category, affine hypothesis, finite-Tor
hypothesis, or choice of an arbitrary functor is used.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| Λ is a finite commutative ring | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` |
| Its additive exponent is invertible in k | `[HasInvertibleExponent Λ (Spec (.of k))]`: some positive annihilating integer is a unit on Spec k. For a finite ring this is equivalent to its additive exponent being a unit in k: the exponent divides every such integer; conversely it annihilates the ring. Global sections of Spec k are canonically k. This includes the zero coefficient ring (exponent one). |
| X and Y are k-schemes | `(X Y : Scheme.{u})` and their `Over (Spec (.of k))` instances |
| Both are separated and of finite type over k | `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on each structure morphism `X ↘ Spec (.of k)` and `Y ↘ Spec (.of k)` |
| f is a separated finite-type morphism between these k-schemes | `(f : X ⟶ Y)`, `f.IsOver (Spec (.of k))`, and `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` |
| Nonnegative integer d | `(d : ℕ)`; precisely the nonnegative integers |
| Every scheme-theoretic fibre has dimension at most d | `hf : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)` |
| F is an étale sheaf of Λ-modules | `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` |
| F is constructible | `hF : Scheme.IsConstructibleEtaleModuleSheaf F`, the finite-value constructibility predicate used by the recorded bounded-constructible definition |
| Nonnegative integer a | `(a : ℕ)` |
| Closed support Z of F has dimension at most a | `hSupp : topologicalKrullDim (sheafSupport F) ≤ (a : WithBot ℕ∞)` |
| Ordinary unbounded derived categories | Existing `DerivedCategoryModule` / `DerivedCategory (Sheaf ... (ModuleCat Λ))`; `DerivedCategory.singleFunctor _ 0` places F in degree zero |
| Rf_! | `rightDerivedLowerShriekOfCompactification (ModuleCat Λ)` applied to the existing chosen compactification. Its existence proof is `HasCompactification.of_isOver (S := Spec (.of k)) f`, supplied explicitly to `HasCompactification.compactification`. Thus no additional compactifiability assumption is needed. This is exactly the compact-support candidate of the dependency and the chosen-functor convention; the refinement comparisons give its independent notation. |
| R^qf_!F = H^q Rf_!F, for every integer q | `∀ q : ℤ` and `(_root_.DerivedCategory.homologyFunctor _ q).obj` of the preceding compact-support value |
| Closed support of R^qf_!F | The existing `AlgebraicGeometry.Etale.sheafSupport`, defined by failure to vanish on every Zariski open neighbourhood, so it is the complement of the largest vanishing open |
| Dimension at most a+d−q, empty support dimension −∞ | First conjunct: whenever this closed support is nonempty, `0 ≤ (a : ℤ) + (d : ℤ) - q` and its dimension is at most the natural value of that integer in `WithBot ℕ∞`. This is exactly the signed-integer bound: nonempty spaces have nonnegative dimension; for negative bounds only empty support can satisfy it. Empty support itself imposes no restriction, in agreement with dimension bottom. |
| In particular R^qf_!F=0 for q<0 and q>a+d | Second conjunct: `∀ q : ℤ, (q < 0 ∨ (a : ℤ) + (d : ℤ) < q) → IsZero (...)` |

Recorded dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  re-exporting `AlgebraicGeometry.Etale.DerivedCategoryModule`; its coefficient source is
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-weil-pbc-scheme-conventions`: a convention record, with no standalone declaration;
  use Mathlib `Scheme`, `Scheme.Over`, `Scheme.Hom.IsOver`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` exactly as its leaves prescribe.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, the pullback along `Y.fromSpecResidueField y`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, defined using chains in `IrreducibleCloseds` with value `WithBot ℕ∞`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, whose body is the
  derived exact extension by zero followed by total right derived proper direct image.
- `def-weil-derived-cohomology-sheaves`: its unchanged `mathlib_match`,
  `DerivedCategory.homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, used directly for ordinary
  etale module sheaves. The live N5 `lean` record and all 12 declarations remain unchanged;
  see Repair of returned delivery.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, re-exporting
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` and
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, whose sheaf predicate is
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` in
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `lemma-weil-pbc-geometric-stalk-conservative`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`,
  `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`.

Other reused interfaces are `sheafSupport` from
`WeilConjectures.SixFunctors.Etale.Perverse.Basic`, and
`HasCompactification.of_isOver` / `HasCompactification.compactification` from
`WeilConjectures.Compactification.NagataCompactification` / `WeilConjectures.Compactification.Defs`.
No local instance, notation, private definition, let binder, auto-bound variable or extra axiom
is introduced.

Edge cases checked before writing:

- F=0, zero coefficient ring, X empty and empty fibres: closed supports are empty and have
  dimension bottom; the conditional dimension clause is vacuous and the vanishing clause holds.
- Y empty forces X empty; no nonempty hypothesis has been added.
- q<0: the dimension bound follows from zero higher compact-support cohomology and the separate
  negative-vanishing clause retains this conclusion explicitly.
- q>a+d: a nonempty support would require the negative integer a+d−q to be nonnegative;
  the statement explicitly asserts zero cohomology in this case.
- q=a+d: the bound allows nonempty zero-dimensional support; it does not accidentally force zero.
- d=0, including f the identity: degree zero retains the input support bound, and positive
  cohomology vanishes; the displayed support condition does not exclude this case.
- A^d → Spec k and its constant finite sheaf, with a=d: q=2d permits support dimension zero,
  the expected sharp boundary of a+d−q. The theorem does not incorrectly impose q≤d.
- Naturals a,d cover all nonnegative integer values and q ranges over all integers. Schemes and
  field use universe u; module values and the finite coefficient carrier use u+1, matching the
  existing ordinary small-étale framework rather than an unrelated pro-étale/adíc encoding.

Searches actually run (2026-10-19):

- `msearch.py ... leanfinder` query: "Dimension of the closed support of compactly supported
  higher direct image of a constructible etale sheaf bounded by input support dimension plus
  fibre dimension minus degree". Eight hits, including `Scheme.Hom.isConstructible_image`,
  `Module.supportDim`, `Module.supportDim_le_ringKrullDim`,
  `Scheme.IdealSheafData.support_map`, and module support-dimension inequalities. No exact match.
- `msearch.py ... loogle` query: `topologicalKrullDim, AlgebraicGeometry.Scheme.Hom.fiber`.
  Zero hits.
- `msearch.py ... grep` query:
  `compact.?support.*(dimension|bound)|(dimension|bound).*compact.?support`.
  Twenty-four Mathlib hits, all about compact support of functions, distributions, or analytic
  bounds, not higher direct images of étale sheaves.
- `msearch.py ... leansearch` query: "Support dimension estimate for higher direct image with
  compact support of an etale constructible sheaf". Eight hits, including `Module.supportDim`,
  its injective/surjective inequalities, and scheme ideal-sheaf support. No exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for support dimensions, closed support,
  sheafSupport and fibre support found the existing closed-support definition and the upstream
  perverse `AffinePushforward` results. I read
  `exists_le_of_not_isZero_upperStar_homology_rightDerivedLowerShriek_singleFunctor` and
  `DerivedCategory.supportCondition_shift_rightDerivedLowerShriek`: the former is a pointwise
  nonzero-stalk estimate and the latter is a bounded-complex perverse support condition. Neither
  states this sheaf-level closed-support estimate with both vanishing ranges, so neither is
  attached as an exact existing match.
- Search for the item id and proposed declaration name in `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json` found no declaration for this item and no collision.

Node faults: no dependency-record repair is needed.
The item's source.external cites Stacks 0F0V, an affine ordinary-cohomology bound rather than
this compact-support estimate; this source-field issue was already flagged in its stage-1
review. The stage-2 delivery preserves that maintainer-owned field and follows the stated
BBD source and the full reviewed DAG proof. No mathematical statement correction or dispute.

Validation: scompile.py compiled the sandbox form and actual module form successfully,
each in 5.8 seconds, with no errors or warnings. The initial compile detected the absence
of an inferred HasCompactification instance; the final statement supplies the already proved
Nagata existence argument explicitly instead of adding an assumption.

## Repair of returned delivery

The maintainer returned immutable head `7f05558f81b2` for H13/H4: rebinding
`def-weil-derived-cohomology-sheaves` to an existing Mathlib declaration would orphan
`Sheaf.Paper.SfCommonStageWeilCohomology` and its 12 landed N5 declarations, including
landed proofs used by `WeilOpenImageDelta` and `DlConstantFieldCharts`.

Removed the dependency node file from this delivery. Its live N5 `lean` record, module,
and all 12 declarations remain unchanged. The item directly uses the dependency's already
recorded `mathlib_match`, `DerivedCategory.homologyFunctor`, specialized to ordinary etale
module sheaves. `DerivedCategory.homologyFunctorFactors` identifies this functor with the
cohomology of a representing cochain complex. No replacement construction is introduced.
The item's `lean.note` records this choice. The theorem module and signature are unchanged
from the mathematically accepted returned delivery.

The retained packet's initial dry run passed (`ed7c33d0c2`), but still contained the rejected
dependency record. This repair removes that change despite the automated pass. The maintainer's
independent reading already accepted every hypothesis, conclusion, edge case, source and
proof-plan step of the unchanged item; this repair addresses its sole returned defect.

Repair validation: scompile.py compiled the sandbox and actual module forms against the live
server library in 5.8 seconds each, with no errors or warnings. Self-check confirmed the item
differs from current main only in `lean`, the recorded signature is verbatim, the packet has
only the item node, and the module retains exactly its single expected `sorry`.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
