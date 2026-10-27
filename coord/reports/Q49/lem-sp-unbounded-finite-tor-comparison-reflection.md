## Worker report

The new module `Sheaf.Paper.UnboundedFiniteTorComparisonReflection` states
`AlgebraicGeometry.unbounded_finiteTor_comparison_reflection`. Its sole theorem has proof
`sorry`; it introduces no definition, choice of comparison, or tensor construction.
The theorem signature and proof plan are unchanged. The item's statement gains the
existing categorical Tor predicate's owner citation and its statement dependency, as
requested in the independent review return; the citation-only change is recorded below.
The source was read in `literature/stacks-project/proetale.tex`,
`lemma-fully-faithful` (Tag 099T), lines 3827ff., and
`lemma-compare-constructible` (Tag 09AK), lines 5238ff., together with the Noetherian Tor
comparison in the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/`.
As the node explicitly says, the unbounded reflection assertion is a consequence, not a
verbatim claim of Tag 09AK. The complete five-step argument is in the theorem docstring.

Hypotheses and conclusions, clause by clause:

- The scheme is `T : Scheme.{u}`. Quasi-compactness is `[CompactSpace T]` and
  quasi-separatedness is `[QuasiSeparatedSpace T]`, the standard scheme-space conventions.
- The arbitrary finite discrete commutative coefficient ring is
  `R : Type (u + 1)` with `[CommRing R] [Finite R] [TopologicalSpace R]
  `[DiscreteTopology R]`. There is no nontriviality, field, prime, characteristic,
  invertibility or geometric finite-type assumption. The successor coefficient universe
  is the existing small-site convention: sites have objects in `Type (u+1)` and morphisms
  in `Type u`; it does not equate their two universes.
- `C : Etale.DerivedCategoryModule R T` is in the ordinary unbounded localization of
  fixed-R module sheaves. There is no boundedness, bounded-below or constructibility
  hypothesis on C. The pro-etale side uses `DerivedCategory (Sheaf (ProEt.topology T)
  (ModuleCat R))`, the equivalent fixed-coefficient presentation of constant-ring modules.
  It imposes no classical-origin condition on the pro-etale test module sheaves.
- The canonical `N_T C` is written explicitly as
  `(ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj C`.
  This is the existing exact inverse image, derived termwise. No arbitrary functor,
  isomorphism or map is supplied as a hypothesis. It is the fixed-module presentation
  used in `Scheme.proEtaleSiteComparisonModules` and `ProEtale.finiteCoefficientComparison`;
  the latter composes it with the existing canonical ring-sheaf realization equivalence.
- `(c d a b : ℤ) (_hcd : c ≤ d) (_hab : a ≤ b)` gives the two ordered intervals.
- `_hVanishing` quantifies every integer q and requires `IsZero` of H^q(N_T C) for
  `q < c ∨ d < q`, exactly the complement of the closed interval [c,d].
- `_hConstructible` quantifies every integer q and applies the dependency's recorded
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf T R` to H^q(N_T C). This is intrinsic:
  a positive finite constructible locally closed stratification, locally constant
  module sheaves on its strata and finite geometric stalks. It does not assert etale
  origin or assume bounded constructibility as input.
- `_hTor` is the existing
  `ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat R) T a b (N_T C)`.
  Its definition is the canonical K-flat derived tensor tested against every
  degree-zero pro-etale R-module sheaf, with cohomology concentrated in [a,b].
  The landed node `def-sf-categorical-proetale-tor-amplitude` owns this presentation
  and is now cited explicitly by the statement and `stmt_deps`.
- The first conclusion is `∀ q, q < c ∨ d < q → IsZero (H^q(C))`, with the very same
  c and d. The second is `∀ q, Scheme.IsConstructibleEtaleModuleSheaf (H^q(C))`.
  The existing `Scheme.Stratification` includes constructibility of the strata through
  `Topology.Stratification.isConstructible_stratum`; this clause is not omitted.
- The third conclusion is `Etale.DerivedCategory.hasTorAmplitudeIn R T a b C` with the
  very same a and b, testing all degree-zero etale module sheaves.
- The fourth is the precise recorded
  `Etale.DerivedCategory.isBoundedConstructible R T C`, and the final conclusion is
  `DerivedCategory.TStructure.t.plus C`, membership in the bounded-below subcategory.
  These are explicit conclusions of the node, not additional input conditions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  The scheme-conventions dependency is expressly a convention record, not a declaration.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.homologyFunctor` and
  `Etale.DerivedCategory.hasTorAmplitudeIn`. The unrelated torsion-cohomology predicate
  in that multi-declaration node is not imposed here.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientEtaleDerivedCategory`, `finiteCoefficientComparison`,
  `finiteCoefficientDerivedComparison`, `finiteCoefficientRealization` and its exactness
  and equivalence results. The statement uses the fixed-module presentation, already
  used on the etale side, rather than duplicating these constructions.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`; its left adjoint is the canonical
  `ProEtale.comparisonUpperStar` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
  Its ordinary derived functor is `Functor.mapDerivedCategory`, described also in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`:
  `ProEtale.DerivedCategory.torAmplitudeIn`. It specializes
  `DerivedCategory.torAmplitudeIn`, whose degree-zero tests use the canonical
  derived monoidal tensor. The former ringed-site dependency interface and the
  independent-coefficient-model interface were read as well, before choosing this
  existing fixed-module interface.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`; its finite constructible stratifications
  and finite locally constant values are the node's definition.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`:
  the recorded bounded predicate is the existing `Etale.DerivedCategory.hasTorAmplitudeIn`.
  The lower-only `hasTorAmplitudeGE` is not the assertion here.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure` and
  `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`:
  `DerivedCategory.Plus`, `DerivedCategory.Bounded`, `TStructure.plus`,
  `TStructure.bounded`, `DerivedCategory.isGE_iff` and `DerivedCategory.isLE_iff`.
  The bounded-subcategories node is a Mathlib leaf; it requires no lean repair.

All available proof dependencies are plain imports:
`ProEtale.proEtaleClassicalSheavesModules`, `comparisonPullbackExact`,
`ProEtale.constructibleComparison`, `ProEtale.finiteTorComparisonNoetherian`,
and the already publicly imported bounded-subcategory/constructible-complex definitions.
The latter two comparison theorems use equivalent coefficient-sized ringed site models;
transport to their interfaces belongs to the postponed proof, not an extra hypothesis.

Edge cases checked before and after writing: zero C; the zero coefficient ring
(no Nontrivial assumption); the empty scheme (a one-piece empty stratification is allowed);
singleton intervals c=d or a=b; negative integers; and intervals [c,d] and [a,b]
with no inclusion relation imposed. No nonempty geometric points or nonempty strata are
assumed. H^q vanishing is a categorical `IsZero`, not a bare-type IsZero predicate.
The input remains genuinely unbounded in its type and hypotheses; only its image is
assumed cohomologically bounded. The proof starts with exactness on cochain complexes
and full faithfulness on SHEAVES, not an unproved unbounded derived full-faithfulness claim.
No mathematical statement fault or STATEMENT-DISPUTED issue was found. The explicit
citation-only correction is recorded under "Statement corrected".

Actual searches performed:

- `msearch.py ... leanfinder "Exact etale to proetale comparison reflects bounded
  constructible cohomology and Tor amplitude of an arbitrary unbounded derived complex"`:
  eight hits, including DerivedCategory.isGE_Q_obj_iff / isLE_Q_obj_iff and generic
  acyclicity/etale algebra facts. None is the comparison-reflection assertion.
- `msearch.py ... loogle "DerivedCategory, CategoryTheory.Functor.Faithful"`:
  two generic faithful-functor instances (whiskering by Qh and the single functor);
  no constructibility/Tor comparison theorem.
- `msearch.py ... grep "HasTorAmplitude|[Pp]ro[Ee]tale|reflect.*[Cc]onstructib"
  AlgebraicGeometry`: ten hits on Mathlib's proetale site and ell-adic cohomology,
  no exact theorem.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  unbounded reflection and constructibility reflection: no exact match. The relevant
  `BoundedBelowCtfReflection` / `BoundedBelowConstructibleReflection` theorems require
  a bounded-below input and special finite-field/p-adic quotient data; they do not
  state this node. `FiniteCoefficientInputModels` confirms the existing fixed-module
  intrinsic constructibility and `ProEtale.DerivedCategory.torAmplitudeIn` interfaces.
- `rg` for `unbounded_finiteTor_comparison_reflection` in Mathlib, both project roots,
  and `dag/lean_names_upstream.json`: no pre-existing declaration with this name.

Validation: `scompile.py Q49 lem-sp-unbounded-finite-tor-comparison-reflection` compiled
this module in the sandbox and library module modes on the server, within the standard
60-second limit and with no errors or non-sorry warnings. The final dry-run result and
push are reported by the delivery wrapper.

## Repair of returned delivery

The independent immutable-head review of `1c232a4adb7e` returned two points.

- H13: restored the live Q28 superset attachment of
  `def-weil-proetale-tor-amplitude` unchanged by removing the proposed replacement
  node file from this packet. Its module remains
  `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`, and all seven
  recorded declarations remain owned by that dependency. This delivery edits no
  dependency record and supplies no dependency module.
- H4: retained `_hTor` exactly and cited its existing owner,
  `def-sf-categorical-proetale-tor-amplitude`, in both `statement` and `stmt_deps`.
  I opened that node's live record and the full upstream `torAmplitudeIn` declaration
  and docstring. It takes arbitrary pro-etale sheaves as degree-zero tests for the
  canonical derived tensor. The already present public import of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`
  is the recorded module of this owner; no duplicate declaration is introduced.

The saved packet's initial dry run passed as `b503ba17a50`, but still carried the
returned record replacement. The actual repair above is made on top of current
live records; that initial pass is not treated as resolving the return.

## Statement corrected

This is a citation-only ownership correction, recorded in `statement_change` for
transparency and the field checker. The old statement cited only
`[def-weil-proetale-tor-amplitude]` after the universal degree-zero pro-etale module
Tor test; the new text additionally cites
`[def-sf-categorical-proetale-tor-amplitude]` at that exact place. No mathematical
word, quantifier, hypothesis, conclusion, source or proof changes. The latter node's
landed `torAmplitudeIn` declaration is precisely the predicate used by `_hTor`.
The former node's live seven-declaration record is preserved unchanged. The source
remains Stacks `proetale.tex`, Tag 09AK, with the exact fully faithful comparison and
`det-pe-finite-tor-comparison-noetherian`, as recorded in the item.

The sole citing node is `lem-sp-finite-compact-support-domains`: holds true. Its
proof Steps 4 and 5 use the same reflection for arbitrary derived inputs; the extra
owner citation alters no premise or conclusion. It is not edited.

## Second reading by Q49

This is the same worker's separate rereading, not an independent agent review: the
assignment prohibits starting other agents and reserves independent review to the maintainer.
I reopened the written module and compared its complete signature with the node. Both
bounds are explicit and are preserved verbatim in the conclusions. The comparison is
exactly the canonical termwise functor, constructibility is intrinsic on the pro-etale
side, every degree-zero module is tested for Tor, and bounded-below membership occurs
only after the implication. I checked the potentially easy-to-miss constructible-strata
clause by opening `Scheme.Stratification` and `Topology.Stratification`; it is already
part of the dependency definition. I also read the Tor predicate's generic body and its
pro-etale specialization, ensuring this is ordinary uncompleted derived tensor.
The returned ownership mismatch is repaired by citing the existing categorical node,
without changing the ringed-site dependency record. I compared the signature against
`lean.statement` verbatim and verified that all five conclusions and every hypothesis
are retained. No mathematical clause, source statement or proof plan was changed.
