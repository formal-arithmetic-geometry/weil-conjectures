## Worker report

The module `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact` states
`AlgebraicGeometry.ProEtale.CondensedRing.module_pullback_additive_exact`, with one
`sorry` as its entire proof. It introduces no construction, helper, or additional
node, and changes only the item's `lean` record. The natural statement is unchanged.

The source read was the main-20261015 blueprint's
`sec-proetale-coefficients/sk-prop-sfb-module-pullback-exact/` detail statement and
proof `det-prop-sfb-module-pullback-exact-main`. Its Setting, Transport, Extension
of scalars and Conclusion paragraphs agree with the reviewed DAG's six proof
steps. The declaration docstring includes all six steps and the dependency names.

Hypothesis and clause correspondence:

- A commutative condensed ring is the arbitrary
  `Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}` with
  `[MonObj Λ] [IsCommMonObj Λ]`. This is the internal-ring encoding used by the
  recorded module-object framework; no topological-ring presentation is assumed.
- Arbitrary schemes and their arbitrary morphism are `{X Y : Scheme.{u}}`
  and `(f : X ⟶ Y)`. No weakly-etale, finite, proper, nonempty or characteristic
  hypothesis is introduced. The small pro-etale site retains its canonical
  object/morphism universe sizes, with abelian coefficients in `u + 1`.
- The node's `f^* = Ext_{alpha_f} o mapMod(f^*_Ab)` is the recorded
  `CondensedRing.upperStar Λ f`, whose real definition is literally
  `(ProEtale.upperStar AddCommGrpCat f).mapMod (condensedRingObj Λ Y) ⋙
  Mod.extendScalars (condensedPullbackHom Λ f)`. Its source and target are
  module objects over `Λ_Y` and `Λ_X`, respectively. No replacement by restriction
  along an arbitrary inverse is made in the statement.
- Additivity is `(upperStar Λ f).Additive` (first conjunct).
- Preservation of finite limits is `PreservesFiniteLimits (upperStar Λ f)`
  (second conjunct), and preservation of finite colimits is
  `PreservesFiniteColimits (upperStar Λ f)` (third conjunct).
- Exactness of the first factor is the fourth and fifth conjuncts:
  `PreservesFiniteLimits` and `PreservesFiniteColimits` of
  `(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1} f).mapMod
  (condensedRingObj Λ Y)`.
- Exactness of the second factor is the sixth and seventh conjuncts:
  `PreservesFiniteLimits` and `PreservesFiniteColimits` of
  `Mod.extendScalars (condensedPullbackHom Λ f)`.
  These two preservation classes are exactly `def-galois-exact-functor`, as
  confirmed by Mathlib's `CategoryTheory.exactFunctor_iff`. All three module
  categories have the existing abelian and hence finite (co)limit instances.

Dependency interfaces read and used (the source and docstring, not just the name):

- `sk-def-sfb-module-pushforward-pullback`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`; its full section binds
  exactly the general commutative condensed ring and arbitrary scheme morphism.
  The same source was confirmed using `scompile.py --source`.
- `sk-def-sfb-pulled-back-coefficients` and `def-sfb-alpha`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, `isCommMonObj_condensedRingObj`, and
  `condensedPullbackHom`. The underlying sheaf is `(upperStarFromPoint X).obj Λ`;
  the ring structure is transported along that strong monoidal functor, and
  `condensedPullbackHom` is the specified component of `upperStarFromPointComp`.
- `def-sfb-modobj-transport`: the closed upstream audit records
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Functor.mapMod`, `modObjObj`, `act_mapMod_obj`.
  The attached legacy `lean` record omits module and primary declaration, but
  its closed audit supplies them exactly, so no repair or duplicate is needed.
- `def-sfb-modobj-extension`: the closed upstream audit records
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.extendScalars`. This is the actual relative tensor
  coequalizer construction, with action on its first factor.
- `sk-def-sfb-module-objects`: the closed upstream audit records
  `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.ModObj`, `Mod`,
  `Mod.forget`, `Mod.regular`. They give the internal action and the exact module
  category used here. No `lean` record is required on a closed-audit dependency.
- `def-weil-pbc-additive-functor`: Mathlib
  `CategoryTheory.Preadditive.AdditiveFunctor`, `CategoryTheory.Functor.Additive`.
  Its `map_add` field is the node's Hom-additivity requirement.
- `def-galois-exact-functor`: Mathlib
  `CategoryTheory.Limits.Preserves.Finite`, `PreservesFiniteLimits` and
  `PreservesFiniteColimits`; `CategoryTheory.Limits.ExactFunctor`,
  `CategoryTheory.exactFunctor_iff`. Finite shapes include the empty shape and,
  by the existing size-change instance, finite shapes in higher universes.
- `sk-def-sfb-condensed-ring`: the recorded continuous-coefficient declaration
  in `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`,
  `Profinite.isCommMonObj_continuousCoefficientRingObj`, was read. It supplies
  examples, while the general condensed ring here is the same arbitrary internal
  ring of the recorded Basic/upperStar interface. It is not necessary to import
  a module constructing continuous-function examples to quantify over all rings.

The public import supplies these actual statement constructions and their
instances. The proof-only imports are `Sheaf.CategoryTheory.SheafTensorClosed`
(`CategoryTheory.sfbSheafTensorClosed`),
`Sheaf.CategoryTheory.ModuleObjects.LiftExact`
(`CategoryTheory.Mod.lift_additive_exact`), and Mathlib's Grothendieck-category
`EnoughInjectives`. Remaining stated proof dependencies are exported transitively
by the public framework import: finite-coefficient inverse image exactness and
its monoidal structure, module-object braidedness, the abelian module instance,
`Mod.comap`, `Mod.comapEquivalenceOfIsIso`, `Mod.extendScalarsIsoComapInv`, and
`isIso_condensedPullbackHom` / `isMonHom_condensedPullbackHom`. The canonical
`FiniteCoefficient.UpperLowerStar.Defs` is used through this import closure rather
than loading an older duplicate implementation.

Searches before writing:

- `msearch.py` leanfinder: "Pullback of module objects over a commutative condensed
  coefficient ring on pro-etale sheaves is additive and preserves finite limits
  and finite colimits, as do transport and extension of scalars". Eight hits,
  concerning AB4*, (co)limits and abelian instances on condensed modules;
  none states the geometric pullback and its two factors.
- `msearch.py` loogle: `CategoryTheory.Limits.PreservesFiniteLimits, CategoryTheory.Mod`.
  Zero hits.
- `msearch.py` grep: `extendScalars|mapMod|pullback.*[Ee]xact` in `CategoryTheory`.
  Nine hits, including Mathlib's TODO for mapMod and unrelated pullback exactness.
- `rg` in the upstream `WeilConjectures`, the published framework and `lean/Sheaf`
  for extension/mapMod/pullback exactness and the item ID: no complete matching
  declaration. The published framework already states the three composite
  properties and two generic mapMod preservation properties separately. The
  scalar-extension natural isomorphism is construction data, not a declaration
  asserting finite-limit preservation. No existing declaration states the full
  seven-clause result. This module uses all existing functor definitions.
- `rg` in the same trees and `dag/lean_names_upstream.json` for the proposed full
  theorem name: no collision. The only generic lifting result is the recorded
  `CategoryTheory.Mod.lift_additive_exact` and is imported for the proof.

Edge cases checked before writing: identity `f`; empty `X` or empty `Y` wherever
such a morphism exists; the zero coefficient ring; nonreduced coefficients such
as Z/4; and empty finite diagrams (zero objects). None is excluded by a binder.
No flatness assumption on arbitrary coefficients is justified or needed: the
specific `alpha_f` is an isomorphism. Extension along Z -> Z/2 would fail left
exactness, which is why the statement names precisely `condensedPullbackHom`
rather than quantifying over arbitrary coefficient maps. No statement dispute,
correction, missing notion, or dependency module is needed.

Validation: the prescribed `scompile.py Q49 det-prop-sfb-module-pullback-exact-main`
passed for the delivered file in both sandbox and library modes, with no compiler
errors or warnings. Every source line is at most 100 characters. The node copy
was compared with the shared base: `lean` is its only changed field. All binders,
including the sole universe `u`, are explicitly declared.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
