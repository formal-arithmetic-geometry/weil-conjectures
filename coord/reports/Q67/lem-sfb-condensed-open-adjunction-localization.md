## Worker report

This stage-2 delivery states `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_adjunction_localization`
in `Sheaf.AlgebraicGeometry.CondensedOpenAdjunctionLocalization`. There is one named theorem,
with proof `sorry`, and no new definitions, dependency repairs or statement corrections.
The accepted Q88 stage-1 split is preserved. The inherited BLOCKED message concerned a
stage-1 re-split, not this stage-2 delivery; coord/brief-stage2.md §0 explicitly resolves
that handoff. The shared node has no Lean attachment and no released repair note.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field and its positive characteristic
  different from ell are `(k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
  (hpℓ : p ≠ ℓ)`. No perfection or algebraic-closedness assumption is imposed.
- `Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}` with `MonObj Λ`
  and `IsCommMonObj Λ` is exactly a commutative condensed ring. The binder
  `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` uses the recorded admissible-coefficient
  definition, including its finite-subextension-valued `Profinite.padicAlgClRingObj ℓ`
  case. It does not replace this ring by the all-continuous-function algebraic closure.
- `V X : Scheme.{u}`, their `Over (Spec (.of k))` structures, and `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` on each structure morphism say separated finite
  type over k. `h.IsOver (Spec (.of k))` says h is a k-morphism. The final two instances
  `IsOpenImmersion h` and `QuasiCompact h` are precisely the stated immersion hypotheses.
- The sites and categories are the recorded `Scheme.ProEt.topology T` and
  `Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) (condensedRingObj Λ T)`.
  Here `condensedRingObj Λ T` is the actual strong-monoidal inverse image of Λ from
  the point. No constant-discrete coefficient sheaf, section-ring substitute, or second
  category of modules is introduced. The site retains object universe u+1 and morphism
  universe u, with abelian coefficients in u+1, exactly the published framework.
- The actual functors are `openImmersionLowerShriek Λ h` and `upperStar Λ h`; their
  specified adjunction is `openImmersionLowerShriekUpperStarAdjunction Λ h`.
  The first six conjuncts assert additivity and preservation of finite limits and finite
  colimits of both functors, exactly additive exactness between abelian categories.
  The seventh conjunct is `IsIso` of the actual underived adjunction unit.
- `∃ adj : (openImmersionLowerShriek Λ h).mapDerivedCategory ⊣
  (upperStar Λ h).mapDerivedCategory` supplies the asserted descended adjunction on
  the ordinary unbounded derived categories. It is not an assumption of the theorem.
  An adjunction object includes both natural transformations and both triangle laws.
  Its normalization equations determine the descent from the specified adjunction;
  no unrelated arbitrary adjunction is substituted for the specified descent.
- The first universal conjunct, for every unbounded cochain complex K over V, is the
  node's displayed equation in Lean composition order: `adj.unit.app (Q.obj K)` followed
  by `D(h^*).map (a_h!.hom.app K)` followed by `a_h*.hom.app (C(h!).obj K)` equals
  `Q.map` of the termwise unit. The termwise unit is obtained directly from the recorded
  `Adjunction.mapHomologicalComplex (.up ℤ)`, whose degree-r component is the actual
  module unit at `K.X r`.
- The second universal conjunct gives the counit normalization explicitly, for every
  unbounded complex M over X: `adj.counit.app (Q.obj M)` equals `D(h!).map (a_h*.hom.app M)`
  followed by `a_h!.hom.app (C(h^*).obj M)` and `Q.map` of the termwise counit. The
  comparisons have the same orientation `D(F) Q ≅ Q C(F)` as in the node.
- `IsIso adj.unit` is invertibility on the entire derived category, not merely on some
  complexes or constructible objects. `NatTrans.CommShift adj.unit ℤ` and the same
  predicate for `adj.counit` express their squares against the canonical integer-shift
  structures of these exact functors, including the functor-composition shift structures.
- The final universal equality is the simultaneous-shift Hom square. It takes arbitrary
  derived objects A, B, arbitrary `f : D(h!).obj A ⟶ B`, and `n : ℤ`. The left route
  precomposes the shifted f with the left functor's canonical shift isomorphism and
  applies the shifted Hom bijection. The right route shifts the original adjunct and
  postcomposes with the inverse right-functor shift comparison. Because the Hom maps
  and the shift identifications are bijections, this equality also asserts compatibility
  of the inverse Hom bijections. No boundedness or constructibility binder appears.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its setting
  docstring. The present result needs only that setting; it does not choose a compactification.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `sk-def-sfb-qlbar-condensed`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and its topology.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj` and its commutativity instance.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `upperStar`.
- `sk-def-sfb-module-lower-shriek` and `def-sfb-module-open-lower-shriek-adjunction`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `openImmersionLowerShriek` and `openImmersionLowerShriekUpperStarAdjunction`.
- `sk-def-sfb-derived-categories`: the recorded convention module
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` is imported publicly;
  the actual unbounded categories and Q used here are Mathlib `DerivedCategory` and
  `DerivedCategory.Q`, as its aggregate record specifies. No resolution data is needed
  for exact-functor descent.
- `lem-weil-pbc-exact-functor-derived-factorization` is a Mathlib leaf with no lean record:
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors`, and the canonical `CommShift ℤ` instance.
- All stated proof-dependency modules are imported. In particular the termwise
  adjunction is `CategoryTheory.Adjunction.mapHomologicalComplex` in
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`; localization is the
  recorded `Mathlib.CategoryTheory.Localization.Adjunction` API; localization uniqueness
  is in `Mathlib.CategoryTheory.Localization.Predicate`; composite adjunction is
  Mathlib `Adjunction.comp`, exposed by the imported adjunction modules. The module
  `WeilConjectures.CategoryTheory.ModuleObjects.Abelian` supplies `Mod.instAbelian`, whose
  node record lists the declaration but omits a module. Sheaf tensor, Grothendieck
  abelianness, ordinary fully faithfulness, module linearization and scalar change use
  exactly the modules recorded in the accepted proof dependencies.

Edge cases checked before writing: h the identity, V empty (also X empty), a zero ring
coefficient, ell=2 and any positive characteristic different from ell, the finite and
finite-subextension-valued algebraic-closure coefficient cases, complexes unbounded in
both directions, and shifts n=0, n=1, n=-1. There is no Nonempty on schemes or nontriviality
of coefficients, no finite-amplitude condition, and no sign restriction on n. At n=0,
the canonical zero-shift comparisons implement the usual unshifted Hom bijection.
The counit is not claimed invertible: only the two units are, exactly as in the node.
No statement dispute or node fault was found.

Searches for reuse (actual launcher msearch calls, logged in searches.jsonl):

- LeanFinder: “Exact extension by zero for condensed module objects has a normalized
  derived adjunction with invertible unit and shift compatible Hom bijections”. Eight
  hits concerned Condensed module AB4/AB4*, locally constant-module adjunctions, solid
  modules, and free/forgetful adjunctions. None is the geometric normalized derived result.
- Loogle: `CategoryTheory.Adjunction.localization, CategoryTheory.Adjunction.CommShift`:
  zero hits.
- Mathlib grep: `mapDerivedCategoryAdjunction|localization_unit_app|homEquiv.*[Ss]hift`
  in CategoryTheory: two hits, `Adjunction.localization_unit_app` and the unrelated
  `ShiftedHom.homEquiv`. The former supplies generic descent, not this open-unit theorem.
- Direct rg of the project's WeilConjectures and Sheaf roots for the item id gave no
  owning declaration. Direct searches for open-unit/derived adjunction declarations
  found the existing upstream `Adjunction.mapDerivedCategoryAdjunction`, its homotopy
  unit normalization, the module derived open adjunction, and
  `CondensedSupportDerivedLocalization`. Those cover parts of the result, but not both
  complex-level normalization equations and simultaneous integer-shift compatibility
  for the specified module open adjunction as a single declaration. Reuse their
  underlying functors and category structures, rather than define them again.

Validation: scompile.py compiled the statement in both sandbox and library mode cleanly
on 2026-10-22. An initial parser issue from the imported scoped notation `)⟦` was repaired
by spelling the shift of the Hom adjunct as `(shiftFunctor _ n).map (...)`. All variables
and universes are explicit, with `set_option autoImplicit false`. The only proof is sorry.

## Second reading by Q67

This is a second pass by the same dispatched worker; the dispatcher explicitly forbids
starting another agent. It is not represented as an independent worker's review. The
maintainer's independent delivery review remains necessary.

I reopened the node and final module and checked every hypothesis and conclusion against
the mapping above. The field, characteristic, admissible commutative condensed ring,
separated finite-type schemes, k-linearity, quasi-compactness and open immersion are all
present. Neither exactness nor unit invertibility was moved into the hypotheses. The
module categories use pulled-back ring objects, and both derived variables range over
the full localization. The equation ordering is correct: the unit first maps into
D(h*)D(h!)QK and then through D(h*)(a_h!) and a_h*, whereas the counit starts at
D(h!)D(h*)QM and proceeds through D(h!)(a_h*), a_h! and the localized ordinary counit.
The termwise adjunction really is the specified one, not a choice of unrelated unit.
Both shift squares use the canonical functor structures, and the Hom equation uses
left hom versus right inv, giving arrows A[n]→D(h*)B[n] on both sides.

The second pass added direct public imports for recorded statement-dependency modules
which had initially been only transitive, made the termwise-adjunction import public
because its declaration occurs in the signature, and removed the unused Shift.Adjunction
import in favor of the CommShift definition actually used. No mathematical statement,
accepted split, or dependency record changed. There are no new nodes or dependency modules.
The final module is recompiled and the prescribed deliver2.py checks follow.
