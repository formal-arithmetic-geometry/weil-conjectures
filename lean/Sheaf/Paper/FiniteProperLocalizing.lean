/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude
import Sheaf.AlgebraicGeometry.ProperHeartContinuitySections
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.SixFunctors.UnboundedClassicalTruncation
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.Algebra.Ring.Shrink

/-!
# Finite-coefficient proper direct image on the localizing categories

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.md
(blueprint: det-ctf-finite-proper-localizing).

The finite ring is represented canonically by its finite discrete condensed ring.
All subcategories in the statements are the recorded constant-model constructible
finite-Tor predicate and `localizingClosureProEtale`; the functors are the published
module-object six functors, and the base-change map is the recorded ambient exchange
`CondensedRing.condensedAmbientExchange`. Thus the statements retain the specified
coefficient identification while using the recorded condensed objects.

## Main definitions

* `finiteDiscreteCondensedCoefficient`: the condensed ring of a finite discrete ring.
* `finiteCoefficientLocalizingProperties`: the Dctf, localizing-restriction, exactness
  and sum clauses for a module-object derived functor.

## Main statements

* `finiteProperLocalizing`: clause (1).
* `finiteProperLocalizing_baseChange`: clause (2).
* `finiteOpenLocalizing`: the extension-by-zero part of clause (3).
* `finiteCompactificationLocalizing`: the compactification part of clause (3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

/-- The condensed ring of a finite discrete commutative ring: the continuous-map
condensed ring `S ↦ C(S, A)` for the discrete topology on `A`.
Source: blueprint det-ctf-finite-proper-localizing, statement, coefficient
identification of lem-weil-pbc-finite-discrete-condensed-ring-constant
(blueprint: det-ctf-finite-proper-localizing). -/
noncomputable def finiteDiscreteCondensedCoefficient (A : Type u) [CommRing A] [Finite A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact Profinite.continuousMapRingObjOfUniverse.{u, u} A

/-- The canonical monoid structure on the finite discrete condensed coefficient, the
published pointwise ring-object structure of the continuous-map condensed ring.
Source: blueprint det-ctf-finite-proper-localizing, statement, coefficient
identification (blueprint: det-ctf-finite-proper-localizing). -/
noncomputable instance finiteDiscreteCondensedCoefficient_monObj
    (A : Type u) [CommRing A] [Finite A] :
    MonObj (finiteDiscreteCondensedCoefficient A) := by
  unfold finiteDiscreteCondensedCoefficient
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A

/-- Commutativity of the canonical finite discrete condensed coefficient.
Source: blueprint det-ctf-finite-proper-localizing, statement, coefficient
identification (blueprint: det-ctf-finite-proper-localizing). -/
noncomputable instance finiteDiscreteCondensedCoefficient_isCommMonObj
    (A : Type u) [CommRing A] [Finite A] :
    IsCommMonObj (finiteDiscreteCondensedCoefficient A) := by
  unfold finiteDiscreteCondensedCoefficient
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  exact Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A

/-- The Dctf and localizing-restriction clauses for a module-object derived functor `F`:
`F` maps `Dctf(X)` into `Dctf(Y)` (the recorded `constantModelBoundedConstructible` and
finite Tor amplitude), maps `Loc(Dctf(X))` into `Loc(Dctf(Y))` (the recorded
`localizingClosureProEtale`), sends distinguished triangles of the source closure to
distinguished triangles (exactness of the restriction), and preserves every small
coproduct of objects of the source closure (the empty one included).
Source: blueprint det-ctf-finite-proper-localizing, statement, clauses (1) and (3)
(blueprint: det-ctf-finite-proper-localizing). -/
def finiteCoefficientLocalizingProperties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}}
    (F : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)))
    [F.CommShift ℤ] : Prop :=
  (∀ K, (constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K) →
    (constantModelBoundedConstructible Λ Y (F.obj K) ∧
      DerivedCategory.finiteTorAmplitude _ (F.obj K))) ∧
  (∀ K, localizingClosureProEtale Λ X K →
    localizingClosureProEtale Λ Y (F.obj K)) ∧
  (∀ T : Triangle
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
    T ∈ distTriang _ →
    localizingClosureProEtale Λ X T.obj₁ →
    localizingClosureProEtale Λ X T.obj₂ →
    localizingClosureProEtale Λ X T.obj₃ →
      F.mapTriangle.obj T ∈ distTriang _) ∧
  (∀ (I : Type (u + 2))
    (D : Discrete I ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
    (∀ i : I, localizingClosureProEtale Λ X (D.obj ⟨i⟩)) →
      PreservesColimit D F)

open scoped CategoryTheory.MonoidalClosed in
/-- Finite rings in any universe have a small discrete model. Postcomposition with the
ring equivalence induces an isomorphism of continuous-map ring sheaves, hence of their
ring objects. The annihilating power of `ℓ` transports along this same equivalence.
Source: blueprint det-ctf-finite-proper-localizing, proof steps 1 and 16, and
sk-def-localizing-closure, finite-coefficient convention
(blueprint: det-ctf-finite-proper-localizing). -/
private theorem finiteDiscreteCoefficient_admissible
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0) :
    IsLocalizingAdmissibleCoefficient ℓ (finiteDiscreteCondensedCoefficient A) := by
  classical
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  let B := Shrink.{0} A
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : IsTopologicalRing B := by infer_instance
  let e : A ≃+* B := (Shrink.ringEquiv.{0} A).symm
  let h : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ⟶
      Profinite.continuousMapRingSheaf.{u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheaf.{u} B ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let E : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let E' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso E
  letI : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  let eh := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := Ab.{u + 1})
  letI : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasEnrichedHom Ab.{u + 1} F G := eh.1
  letI : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom Ab.{u + 1} F G := eh.2
  letI : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  have hmon : IsMonHom E'.hom := Sheaf.isMonHom_sheafCompose_map _ E.hom
  refine Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨Mon.mkIso' E'⟩⟩
  obtain ⟨n, _, hn⟩ := hA
  refine ⟨n, fun b ↦ ?_⟩
  have hn' : (ℓ ^ n : ℕ) • (1 : B) = 0 := by
    simpa only [map_nsmul, map_one, map_zero] using congrArg e hn
  simpa only [nsmul_eq_mul, mul_one, zero_mul] using congrArg (fun x : B ↦ x * b) hn'

section Setting

variable (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : 0 < p) (hpℓ : p ≠ ℓ)
  (k : Type u) [Field k] [CharP k p]
  (A : Type u) [CommRing A] [Finite A]
  (hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]

include hℓ hp hpℓ hA k

/-- Clause (1): proper pushforward preserves the recorded finite-coefficient Dctf and
restricts to an exact sum-preserving functor of the localizing closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (1)
(blueprint: det-ctf-finite-proper-localizing).

Proof (steps 1--13 of the node):
1. Every standing scheme is Noetherian (lem-weil-pbc-finite-type-over-noetherian) and
   quasi-separated (lem-weil-pbc-locally-noetherian-quasi-separated); proper maps are qcqs
   (lem-pc-separated-quasi-separated). The finite condensed ring is the constant ring
   (lem-weil-pbc-finite-discrete-condensed-ring-constant,
   lem-weil-pbc-finite-discrete-scheme-ring-constant), and `ν^*` identifies the étale and
   pro-étale Dctf with the same Tor intervals (det-pe-finite-tor-comparison-noetherian).
2. A uniform fibre-dimension bound `e` (lem-fin-finite-type-fibre-dimension-bound,
   lem-sc-fibre-dimension-after-base-change,
   lem-weil-pbc-dimension-supremum-local-dimensions, lem-pc-proper-base-change,
   lem-kun-03qu-sep-closed, thm-sc-finite-type-torsion-cd) gives `d = 2e`, so
   det-ctf-finite-proper-tor maps étale Dctf into Dctf with interval `[a, b + 2e]`.
3. The bounded-below comparison sk-thm-pe-direct-image-comparison transfers this to
   `Rp_* K ≃ ν_Y^* Rp_{ét,*} C`, which lies in `Dctf(Y, A)`.
4. Complexes with classical cohomology form a replete triangulated subcategory closed
   under ambient coproducts (det-pe-classical-sheaves-modules,
   det-pe-classical-derived-weak-serre, lem-pur-ringed-site-grothendieck-abelian,
   lem-kun-grothendieck-derived-coproducts); it contains `Loc(Dctf)` by
   sk-def-localizing-closure, and is stable under scheme pullback.
5. For affine weakly contractible `V → Y` and `h : Z = X ×_Y V → V`, every classical
   `H` has `R^q h_* H = 0` for `q > 2e` (lem-kun-proper-torsion-cd-bound,
   lem-weil-pbc-exchange-forget-coefficients, sk-thm-pe-direct-image-comparison).
6. Hence `H^q(Z, H) = 0` for `q > 2e` (lem-weil-proetale-weakly-etale-localization,
   lem-weil-pbc-localized-sheaves-over-representable, sk-def-pe-weak-contractible,
   det-proper-heart-continuity-sections,
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
7. With a K-injective representative (lem-pur-kinjective-restrict-localized,
   det-pe-topos-functoriality-inverse-image), `(H^m Rp_* K)(V) = H^m RΓ(Z, K|_Z)`.
8. The restriction to `Z` is the scheme inverse image
   (def-weil-pbc-ringed-derived-restriction) and commutes with truncation.
9. For `N < m - 2e - 1`, det-pe-unbounded-classical-truncation (2) and
   det-pe-sections-conservative give `H^m Rp_* K ≅ H^m Rp_* τ_{≥N} K`.
10. The same holds after any base change `p'` (used for clause (2)).
11. For families with a common lower bound, det-pe-bounded-continuity-direct-image and
    lem-pc-right-derived-functor-triangulated give the coproduct comparison.
12. Steps 9 and 11 with `N = m - 2e - 2` give preservation of all ambient sums of
    families in the classical subcategory, the empty family included.
13. `Rp_*` is triangulated; the objects of the classical subcategory sent into
    `Loc(Dctf(Y))` form a localizing subcategory containing `Dctf(X)`, so by
    sk-def-localizing-closure and lem-weil-pbc-triangulated-functor-restriction the
    restriction is exact and preserves sums. -/
theorem finiteProperLocalizing (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (f)_*⟦finiteDiscreteCondensedCoefficient A⟧.rightDerivedFunctor := by
  sorry

/-- Clause (2): the canonical base-change map, the recorded ambient exchange
`condensedAmbientExchange` (the adjunction mate of the square comparison under the
derived adjunctions), is invertible on the localizing closure, for arbitrary `g`.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (2)
(blueprint: det-ctf-finite-proper-localizing).

Proof (steps 1--10, 14 and 15 of the node):
1. Steps 1--10 of `finiteProperLocalizing` give the fibre bound `e`, the classical
   subcategory containing `Loc(Dctf(X))`, and the truncation isomorphisms
   `H^m Rp_* K ≅ H^m Rp_* τ_{≥N} K` and `H^m Rp'_* J ≅ H^m Rp'_* τ_{≥N} J` for
   `N < m - 2e - 1`.
2. (Step 14.) For bounded-below `B` with classical cohomology,
   det-pe-classical-derived-equivalence (its unit hypothesis by sk-prop-sf-comparison)
   gives `B ≃ ν_X^* L`; thm-weil-pbc-bounded-below,
   lem-weil-pbc-exchange-forget-coefficients (3) and
   lem-weil-pbc-transport-identifies-exchange identify the ambient mate
   (def-weil-pbc-ambient-ringed-exchange) with the invertible étale exchange.
3. (Step 15.) For `K` in the closure and `N = m - 2e - 2`, naturality of the mate gives a
   square with top `β_K`, bottom `β_{τ_{≥N} K}` and invertible vertical maps in degree
   `m` (steps 9, 10, exactness of `g^*` and `g'^*`); hence `H^m β_K` is invertible for
   every `m`, with no flatness hypothesis on `g`. -/
theorem finiteProperLocalizing_baseChange
    {X' Y' : Scheme.{u}} [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (finiteDiscreteCondensedCoefficient A) X)))
    (hK : localizingClosureProEtale (finiteDiscreteCondensedCoefficient A) X K) :
    IsIso ((condensedAmbientExchange (finiteDiscreteCondensedCoefficient A) sq).app K) := by
  sorry

/-- Clause (3), open part: extension by zero preserves the recorded Dctf and all small
sums, and restricts to an exact sum-preserving functor of the localizing closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (3)
(blueprint: det-ctf-finite-proper-localizing).

Proof (steps 1 and 16 of the node): by step 1 the constant-`A` categories are the
module-object categories over the finite discrete condensed ring, which is an admissible
coefficient. Apply det-proper-image-localizing-open with `Λ = A` discrete: its scheme
hypotheses are the standing ones, and it gives preservation of Dctf, of all small ambient
sums, and the exact sum-preserving restriction to the two localizing closures. -/
theorem finiteOpenLocalizing (j : X ⟶ Y) [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory ∧
    (∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
      (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory) :=
  sorry

/-- Clause (3), compactification part: for `j` open and `f` proper, `Rf_* ∘ j_!` maps
Dctf into Dctf and restricts to an exact sum-preserving functor of the closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (3)
(blueprint: det-ctf-finite-proper-localizing).

Proof (step 17 of the node): apply `finiteOpenLocalizing` (step 16) to `j` and
`finiteProperLocalizing` (step 13) to `f`. Each maps Dctf into Dctf and restricts to an
exact functor of the closures, so the composite does. For a family in the source closure
the two canonical coproduct comparisons compose to
`Rf_* j_! (⨁ K_s) ≅ Rf_* (⨁ j_! K_s) ≅ ⨁ Rf_* j_! K_s`, compatibly with coprojections,
including the empty family. -/
theorem finiteCompactificationLocalizing
    {U : Scheme.{u}} [U.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      ((j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory ⋙
        (f)_*⟦finiteDiscreteCondensedCoefficient A⟧.rightDerivedFunctor) := by
  obtain ⟨hj, _⟩ := finiteOpenLocalizing ℓ p hℓ hp hpℓ k A hA j
  have hf := finiteProperLocalizing ℓ p hℓ hp hpℓ k A hA f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact hf.1 _ (hj.1 K hK)
  · intro K hK
    exact hf.2.1 _ (hj.2.1 K hK)
  · intro T hT h₁ h₂ h₃
    have hT' := hj.2.2.1 T hT h₁ h₂ h₃
    have hT'' := hf.2.2.1 _ hT' (hj.2.1 _ h₁) (hj.2.1 _ h₂) (hj.2.1 _ h₃)
    exact isomorphic_distinguished _ hT'' _
      ((Functor.mapTriangleCompIso _ _).app T)
  · intro I D hD
    have h₁ := hj.2.2.2 I D hD
    have h₂ := hf.2.2.2 I
      (D ⋙ (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory)
      (fun i ↦ hj.2.1 _ (hD i))
    infer_instance

end Setting

end AlgebraicGeometry.ProEtale
