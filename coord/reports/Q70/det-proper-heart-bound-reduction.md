## Worker report

The module `Sheaf.Paper.ProperHeartBoundReduction` states
`AlgebraicGeometry.ProEtale.properHeartBoundReduction`, with `sorry` as its only theorem
proof. Three auxiliary definitions spell out this same node's assertion: the higher
direct-image bound, ordinary integral rationalization, and the reduction implication.
They use existing constructions and contain no postponed data or new independent notion.
The natural statement, dependencies and seven-step proof plan of the node are unchanged.

Hypothesis and clause correspondence, checked with the node and module open:

- The fixed prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is
  `PadicAlgCl ℓ`. The finite subextension E is `E : PadicAlgCl.FiniteIntermediateField ℓ`:
  its underlying intermediate field is embedded in that closure, and its second component
  is precisely finite dimensionality over `ℚ_[ℓ]`.
- Positive characteristic different from ell is `(k : Type u) [Field k] (r : ℕ)
  [Fact r.Prime] [CharP k r] (_hrℓ : r ≠ ℓ)`. A prime r is positive, so characteristic
  zero is excluded exactly as in the standing setting.
- X and Y are `Scheme.{u}` with `.Over (Spec (.of k))`, and each structure map carries
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`. These are precisely separated
  finite-type k-schemes. The morphism `(p : X ⟶ Y)` has `[p.IsOver (Spec (.of k))]`
  and `[IsProper p]`. The bound is the unrestricted integer `(c : ℤ)`.
- The only Noetherian instance used to type the locally closed extension is constructed
  in the theorem's conclusion from `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`. It is not an additional assumption.
- Every coefficient sheaf uses the existing `condensedRingObj` through
  `pulledBackModuleObjects`. Finite fields and integer rings use the continuous
  condensed rings `Profinite.continuousMapRingObj F` and
  `Profinite.padicIntegersRingObj ℓ F`. The algebraic closure uses
  `Profinite.padicAlgClRingObj ℓ`, whose sections are finite-subextension-valued
  continuous functions. It is not replaced by all continuous functions into the closure.
- `ProperHeartHigherVanishing Λ p c M` is
  `∀ q : ℕ, c < (q : ℤ) → IsZero (((CondensedRing.lowerStar Λ p).rightDerived q).obj M)`.
  Mathlib's `rightDerived` uses injective resolutions of the actual additive left exact
  module pushforward. The source declares negative degrees zero; consequently checking
  all natural degrees is equivalent to checking all integer degrees, for every integer c.
- The premise of `ProperHeartBoundReductionAssertions` quantifies over every finite
  subextension F with `E ≤ F`. This includes F = E, not just strict extensions.
  It quantifies over every `S : Scheme.{u}`, `a : S ⟶ X`, and `ha : IsImmersion a`.
  The extension is the recorded `coefficientHeartLocallyClosedExtension` applied to a,
  namely open extension into its scheme-theoretic image followed by closed pushforward.
- Its L0 is a module over the pulled-back `Profinite.padicIntegersRingObj ℓ F` on S.
  `IsLisseCoefficientModule ... L₀` means a pro-etale cover on each member of which it
  is isomorphic to `Mod.finiteFree` of some finite rank. The existential rank occurs
  separately on each cover member, so ranks may vary, and rank zero is included.
- The first conjunct gives the integral bound for `a_! L₀`. The second applies
  `properHeartRationalization ℓ F X` to that already extended module. Its definition is
  `Mod.extendScalars` along `coefficientMap` of the actual condensed inclusion O_F → F,
  so this is exactly `(a_! L₀)[1/ell]` on X, using ordinary scalar extension.
- The third conjunct applies `Mod.extendScalars` along
  `coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) X` to the same localized
  module. It is exactly `((a_! L₀)[1/ell])_Qbar`, again ordinary scalar extension.
- The conclusion quantifies over a condensed ring sheaf Λ with its commutative ring
  object structure and the disjunction
  `Λ = Profinite.padicSubfieldCondensedRing ℓ E ∨ Λ = Profinite.padicAlgClCondensedRing ℓ`.
  Thus it covers exactly E and Qbar_l. For every
  `M : ConstantModelConstructible (coefficientHeartRingObj Λ) X` it asserts
  `ProperHeartHigherVanishing ... p c M.obj`. This is the recorded finite constant
  local-model constructibility, not a replacement by arbitrary finite presentations.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` exports the recorded
  `Padic.finite_coefficientExtensionRing` and the coefficient constructions of
  `CoefficientExtension`. For subfields of the fixed algebraic closure the existing
  `PadicAlgCl.FiniteIntermediateField`, `PadicAlgCl.integers` and corresponding condensed
  rings provide the specialized field and integer-ring data.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` supplies
  the recorded standing-setting interface `CondensedRing.compactificationOverField`;
  the setting itself is expressed by the explicit geometric binders above. No
  compactification is used or assumed by this particular reduction statement.
- Mathlib `AlgebraicGeometry.IsProper`, `IsSeparated`, and `IsClosedImmersion` are the
  recorded geometric notions. `IsImmersion` is Mathlib's locally closed immersion.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`; `Sheaf.Paper.ModuleObjects`:
  `pulledBackModuleObjects`; `...UpperLowerStar.Defs`: `CondensedRing.lowerStar`,
  its additive and finite-limit-preservation instances.
- `Sheaf.Paper.CoefficientHeart` and its public imports:
  `coefficientHeartLocallyClosedExtension`, `IsLisseCoefficientModule`,
  `coefficientHeartRingObj`. The theorem `coefficientHeart` supplies the proof plan's
  filtration criterion; these definitions already make sense for integral coefficients.
- `...ModuleObject.ChangeOfCoefficients`: `coefficientMap`;
  `...ModuleObjects.ExtendScalars`: `Mod.extendScalars`. Their actual coefficient
  maps are used; no arbitrary scalar map or arbitrary extension functor is introduced.
- `Sheaf.Paper.CondensedConstantConstructibility`: `ConstantModelConstructible` and
  its predicate `IsConstantModelConstructible`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and its public imports provide
  the recorded universe-general continuous-ring interface. The fixed finite subfields
  of `PadicAlgCl ℓ` have the existing Type-0 specialized construction in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `padicIntegersRingObj`, `padicSubfieldCondensedRing`, `padicAlgClRingObj`, and
  `padicAlgClCondensedRing`. `...Condensed.FiniteSubextension` supplies the canonical
  inclusion `padicSubfieldRingObjToPadicAlgCl`.
- Mathlib `CategoryTheory.Functor.rightDerived` is used for the higher images.
  Proof-only imports include the recorded ringed-site resolution, full long exact
  sequence, completed coefficients, scalar flatness, exact left derivation, finite
  coefficient descent, stratified lattice and open/closed ring-sheaf sequence modules.
  The recorded common-stratification and filtration modules are public dependencies
  of `CoefficientHeart`. `det-prop-scalar-six-pullback` has no recorded declaration,
  so there is no proof import for that node yet.

Edge cases checked before writing: empty X, empty S, the zero lattice and rank zero;
variable ranks on disconnected strata; F = E; arbitrary negative c (degree zero is
still required to vanish); c = 0; and either coefficient choice, including the identity
finite-field case. No nonempty, connected, reduced, constant-rank, positive-dimension,
or strict-extension restriction occurs. Integral and rational higher images live in
their respective coefficient module categories rather than being silently identified.
All schemes and covers use the existing framework's universe u; the sheaf values are
in u+1, retaining the small pro-etale site's object/morphism universe convention.

Searches for an existing statement:

- `msearch.py ... leansearch "higher direct images constructible sheaves vanishing
  reduction to locally closed lisse lattices"`: eight unrelated results concerning
  constructible subsets, locally constant condensed functors and ideal sheaves; no match.
- `msearch.py ... leanfinder "Vanishing of higher direct images of constructible
  pro-etale sheaves reduces to locally closed extensions of integral l-adic lattices"`:
  eight results on affine limits and condensed functor constructions; none states this
  reduction.
- `msearch.py ... loogle "Functor.rightDerived, IsZero"`: unknown identifier reported
  by that index; not evidence of absence. The actual Mathlib RightDerived source was
  opened and its full definition, ambient assumptions and docstring read directly.
- `msearch.py ... grep "properHeart|heart.*bound|constructible.*lattice" CategoryTheory`:
  no Mathlib hits. Direct rg in the project's `lean/Sheaf`, the exact side framework,
  and upstream `WeilConjectures` found only unrelated amplitude/continuity bounds and
  references to lattices. Direct grep for this blueprint id in upstream found no match.
- Exact-name rg across Mathlib, both project source trees and
  `dag/lean_names_upstream.json` found no existing declaration with any delivered name.

The resolved stage-1 repair note was read; it concerns splitting the proof plan, not a
stage-2 interface defect. This delivery preserves the reviewed seven-step plan and
includes it in the theorem docstring. No statement correction or disputed statement.

## Second reading by Q70

Author self-check for direct delivery; the maintainer supplies the independent review.
I reopened the DAG statement, blueprint reduction and proof, and the delivered module.
Each clause was compared with the correspondence above. In particular the premise
contains all three vanishings with the same extension a_!L0; localization occurs on X
after a_!, not on an unrelated sheaf; finite F must contain the fixed E; the conclusion
uses the recorded constructibility predicate; and c remains an integer with degree zero
included when c is negative. The scheme-theoretic-image extension is the existing
dependency construction, and the theorem constructs its Noetherian instance from the
standing hypotheses. The helper predicates only expand this assertion and introduce
no extra mathematical assumption. No natural-statement mismatch was found.
