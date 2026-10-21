## Worker report

The module `Sheaf.Paper.IntegralGeneralLfpHomInversion` states
`AlgebraicGeometry.ProEtale.IntegralHomInversion.integralGeneralLfpHomInversion`.
It leaves exactly that theorem as `sorry`. All other declarations are real constructions
or transparent aliases to the recorded canonical objects. No statement correction or
new independent notion is needed.

Hypothesis and clause audit, with `I` denoting the namespace `IntegralHomInversion`:

- Prime ell: `l : ℕ` and `[Fact l.Prime]`.
- The specified embedded finite extension: `E : PadicAlgCl.FiniteIntermediateField l`.
  This is an actual intermediate field of the fixed algebraic closure, finite over Q_l.
- Noetherian scheme: `X : Scheme.{u}`, `[CompactSpace X]`,
  `[IsLocallyNoetherian X]`. There is no dimension, separatedness, base-field,
  characteristic, or invertibility-on-X assumption.
- B is the genuine condensed valuation-ring coefficient pulled back along p_X:
  `I.integral l E X` is `condensedRingObj (Profinite.padicIntegersRingObj l E.1) X`.
  `I.ring` is its existing reconstructed commutative section-ring sheaf.
- S is the corresponding rational coefficient ring. `I.coefficientMap` is the existing
  `sectionScalarMap` applied to `padicIntegersToPadicSubfield`, the actual pulled-back
  inclusion O_E -> E. Its codomain is the section ring of
  `condensedRingObj (Profinite.continuousMapRingObj E.1) X`, with the induced valuation
  topology supplied by the existing finite intermediate field construction.
- `I.D` is the ordinary unbounded module-sheaf derived category. `I.internal` is the
  derived inverse of the exact `sectionModuleEquivalence`; it tests the original
  internal-module predicate on precisely the same objects. In particular `_hK` is the
  original `boundedConstructible` predicate, not its discrete-coefficient specialization,
  not finite constant matrices, site-perfectness, or derived completeness. Its definition
  is bounded cohomology intersected with `IsConstructibleModuleObject` in every degree.
  The latter uses `Scheme.Stratification` and `IsLocallyFinitelyPresented`, whose free
  presentation morphisms allow arbitrary local entries and arbitrary finite ranks.
- `_hL : ∃ c : ℤ, L.IsGE c` is exactly cohomology vanishing in sufficiently negative
  degrees, with neither constructibility nor completeness.
- `M : ScalarHomModels`, `μ : ∀ b, ScalarHomTensorComparison M b`, and
  `α : ScalarInternalHomAdjunction M μ` specify the existing universal ambient operations
  together with their pure-tensor and evaluation normalizations. These are presentation
  data for operations already present, available by `scalarInternalHomAdjunction_exists`;
  they impose no condition on K, L, E, or X. The statement holds for every such presentation.
  No arbitrary map, tensor, or Nonempty isomorphism is substituted for a canonical operation.
- `I.extension` is `(M.scalar I.coefficientMap).derived`, i.e. S tensor_B^L -. `I.hom`
  is `derivedInternalHomOfUniverses` on the same ring sheaf. The existing evaluation-
  preserving internal/ringed comparison identifies this with recorded `derivedHom`.
- The first `IsIso` is the existing `localizationHomComparison`, built by scalar-extending
  evaluation, applying the inverse strong tensor comparison, and transposing over S.
- The second `IsIso` uses `localizationHomRestrictedComparison`, including exactly the
  evaluation-normalized scalar-Hom adjunction identifying its target with Hom_B(K,U(L_E)).
- The next universally quantified square is naturality in both inputs, contravariant in
  K and covariant in L. It allows arbitrary arrows; in particular it covers the required
  arrows between bounded constructible/bounded-below inputs.
- The existential `h` proves invertibility of ell^n on every extended object. It is a
  conclusion, used only to type the inverse in the actual formula `I.leg`; it adds no
  hypothesis. `I.leg` is unit followed by restricted inverse multiplication by ell^n.
- For every complex representative A of Hom_B(K,L), every representative P of L, and
  every identifying isomorphism eA/eP, the two beta isomorphisms identify the actual
  termwise colimits `colimit (I.tower A)` and `colimit (I.tower P)` with restricted
  scalar extension. `I.tower` has literally constant object and transition `l • 𝟙`.
  Colimits of complexes are termwise module-sheaf colimits. The two equations for every
  n pin their legs to eA/eP followed by `I.leg`.
- Gamma identifies the first termwise telescope with Hom_B(K,the second telescope).
  Its beta square identifies it with the actual restricted canonical comparison; its
  equation for every n says exactly that it is induced by Hom of the target cocone leg.
  Quantifying over every A/P and eA/eP retains representative independence; no bound
  is imposed on a complex representing Hom or even on the chosen P.
- The last equation uncurries the nth-stage composite. It equals evaluation followed
  by the nth localization leg of L: `(h,k) -> ell^(-n)(1 tensor h(k))`.
  This is the morphism-level version of the node's specified pairing, rather than an
  unrelated sectionwise formula on a chosen resolution.
- No completion functor or completed category occurs anywhere.

The small site retains object universe u+1 and arrow universe u, with modules in u+1.
The two public instance wrappers reuse existing sheafification transport and
`HasDerivedCategory.ofIsGrothendieckAbelian`; they construct canonical data with no sorry.
They avoid the false extra assumption of an arbitrary, incompatible localization instance.
The generic API required explicit universes for the concrete morphism carriers as well
as categories. Canonical instances also resolve the original comparison elaboration timeout.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, public continuous
  and adic coefficient constructors; its actual ring-object input type is retained.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, their monoid and commutativity structures.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`: the publicly
  retained general `boundedConstructible`, `BoundedConstructible`,
  `mem_boundedConstructible_iff`. The discrete specialization is deliberately not used.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `derivedHom` and
  `derivedTensorHomAdjunction`; used through the recorded evaluation-preserving
  `ModuleObjectRingedComparison` presentation (`ring`, `equivalence`, `forward`, `hom`).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the recorded finite p-adic
  coefficient-extension framework and its spectral valuation-ring construction.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; `CompactSpace` is
  the Mathlib quasi-compactness predicate on the underlying space.
- `Sheaf.Paper.CompletedCondensedCoefficients`: `completedCondensedRational`,
  its actual coefficient inclusion and repeated-ell universal-property description.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, `IsColimit`;
  the displayed comparison is specified by the actual colimit legs.
- `Sheaf.Algebra.Homology.InternalHomLocalizationComparison`:
  `localizationHomComparison`, `localizationHomRestrictedComparison`,
  `internalHom_localization_comparison`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: `sectionScalarMap` and the
  normalized internal/sectionwise scalar-transport interface.
- All available proof dependencies are imported: general-lfp constant-model bridge,
  constructible internal continuity, ringed-site Grothendieck abelianness, localization
  reflection, scalar complex colimits, K-injective scalar telescope, and scalar internal
  Hom adjunction. The minimal-closed-subsets dependency is a Mathlib match from
  `Noetherian.lean`, not a missing Lean node. Abstract derived categories, the small
  pro-etale site, scalar adjunction, and ordinary colimits are already public imports.

Source check: read the local Bhatt--Scholze PDF pp. 61--62, Lemma 6.8.12 and
Proposition 6.8.14(2). The former is global Hom/direct sums; the node explicitly calls
its internal-sheaf result an extraction and supplies the continuity/localization bridge.
No claim that the paper verbatim states the internal theorem is made.

Edge cases: empty X, zero K or L, torsion and zero/rank-zero presentation matrices,
ramified finite extensions, E=Q_l, cohomology in arbitrary integer degrees, arbitrarily
negative lower bounds, unbounded positive cohomology of L, n=0 and every n>0, arbitrary
complex representatives (not necessarily strictly bounded below). No nonzero, perfect,
torsion-free or completedness condition has slipped into a hypothesis. No mathematical
counterexample to this node was established in this statement-only task.

Searches: prescribed `msearch.py` LeanFinder query "Derived internal sheaf Hom from
bounded constructible integral pro-etale coefficients commutes with inverting ell"
returned 8 hits (LightCondensed internal Hom/points and underived sheafification maps),
none the assertion. Loogle `"internalHom", "localization"` returned 0 hits. Prescribed
Mathlib grep `(internalHom|derivedHom).*(localiz|invert)|(localiz|invert).*(internalHom|derivedHom)`
returned 0 hits. Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the node
id and integral-Hom-inversion names found no exact declaration, only related integral
model/descent and formal localization statements. The formal conditional theorem is
used, not restated. Existing bounded-constructible and coefficient notions were inspected
through their full source signatures and docstrings before writing.

## Second reading by NX

Single-worker clause audit (the dispatcher explicitly prohibits subagents; independent
maintainer review follows this delivery). Reopened the node and the complete module.
Checked every clause against the list above. Replaced initially implicit universe choices
with the exact u+1/u small-site parameters. Removed arbitrary localization-instance
binders after diagnosing their incompatibility with the recorded derived equivalence.
The final statement universally quantifies representatives and every telescope stage;
it does not silently discard the normalization or independence clauses. All helper data
are defined, and the one theorem remains sorry as required for stage 2.

## Validation

The final module passed scompile.py in both sandbox and library naming modes, with only the expected theorem `sorry` warning. The delivery dry run passed preflight and per-file compilation (commit 29b74fd582c); an additional transparency-setting experiment failed and was reverted to that validated source before delivery.
