/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.FormalClosedSupport
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Constructibility of sections with closed support

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-closed-adjoint-constructible/sk-prop-closed-adjoint-constructible-support.md
(blueprint: det-prop-closed-adjoint-constructible-support).

The support functor, exact closed direct image, and exact inverse image are the existing
module-object constructions. The adjunction is specified by its kernel-inclusion counit,
so the first arrow cannot be replaced by an arbitrarily rescaled counit.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

-- Avoid unfolding the internal-Hom and coefficient-pullback constructions.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.rightDerivedFunctor Sheaf.monoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The closed-support localization assertion for a given coefficient ring.
The existential adjunction is normalized by the existing support-kernel inclusion, exactly
as in `FormalClosedSupportAssertions`. Its derived counit and the canonical open unit are
the first two arrows. The only unspecified triangle arrow is the connecting morphism.
The middle vertex is bounded constructible by its type; the other three displayed terms
and the closed-support object are explicitly required to be bounded constructible.

Source: blueprint main-20261015, closed-adjoint-constructible, support detail statement
(blueprint: det-prop-closed-adjoint-constructible-support). -/
def ClosedSupportConstructibleAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] : Prop :=
  ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
    (∀ M : FormalSupportModules Λ X,
      (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
        (formalSupportKernelInclusion Λ j).app M) ∧
    ∀ K : BoundedConstructible (condensedRingObj Λ X),
      ∃ δ : (lowerStar Λ j).rightDerivedFunctor.obj
          ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj) ⟶
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧,
        Triangle.mk
            (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj)
            ((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
              K.obj) δ ∈ distTriang _ ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ j).rightDerivedFunctor.obj
            ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          (((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧) ∧
        boundedConstructible (condensedRingObj Λ Z)
          ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)

private theorem boundedTriangulated_of_serre
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (hker : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧ IsConstructibleModuleObject R (cokernel f))
    (hext : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated := by
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    IsConstructibleModuleObject R
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ IsConstructibleModuleObject.of_iso e h⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro Z ⟨f, k, hk, h⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (hker _ _ f h.1 h.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro Z ⟨f, k, hk, h⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (hker _ _ f h.1 h.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ hext _ h h₁ h₃⟩
  exact isTriangulated_boundedConstructible_of_serre R

private theorem supportPullback_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (FormalSupportModules Λ Y))
    (hK : boundedConstructible (condensedRingObj Λ Y) K) :
    boundedConstructible (condensedRingObj Λ X)
      ((formalSupportPullback Λ f).mapDerivedCategory.obj K) := by
  refine ⟨(formalSupportPullback Λ f).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  apply constructible_of_iso
    (((formalSupportPullback Λ f).mapDerivedCategoryHomologyFunctorIso n).app K)
  apply constructible_of_iso
    ((Functor.isoWhiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).app
        ((DerivedCategory.homologyFunctor _ n).obj K))
  exact isConstructibleModuleObject_upperStar Λ f _ (hK.2 n)

private theorem support_constructible_of_localization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated]
    (hpush : ∀ K, boundedConstructible (condensedRingObj Λ U) K →
      boundedConstructible (condensedRingObj Λ X)
        ((lowerStar Λ j).rightDerivedFunctor.obj K)) :
    ClosedSupportConstructibleAssertions Λ i j := by
  have hji : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  obtain ⟨_, _, a, hn, _, _, _, _, hc, b, c, δ, hb, hj, htri, hfiber⟩ :=
    formal_closed_support_adjunction.{u, u + 1} Λ i j hji
  subst b c
  refine ⟨a, hn, fun K ↦ ?_⟩
  let F := (lowerStar Λ i).mapDerivedCategory.obj
    ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)
  have hB := hpush _ (supportPullback_constructible Λ j K.obj K.property)
  have hF : boundedConstructible (condensedRingObj Λ X) F :=
    (boundedConstructible (condensedRingObj Λ X)).ext_of_isTriangulatedClosed₁
      _ (htri K.obj) K.property hB
  obtain ⟨e⟩ := hfiber K.obj F
    (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj) (δ.app K.obj) (htri K.obj)
  refine ⟨δ.app K.obj, htri K.obj, hF, hB, ?_, ?_⟩
  · exact (boundedConstructible (condensedRingObj Λ X)).le_shift (1 : ℤ) _ hF
  · exact (boundedConstructible (condensedRingObj Λ Z)).prop_of_iso e.symm
      (supportPullback_constructible Λ i F hF)

private theorem support_constructible_over_field
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsFinitenessCoefficient ℓ Λ]
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [j.IsOver (Spec (.of k))]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ClosedSupportConstructibleAssertions Λ i j := by
  let : LocallyOfFiniteType (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (U ↘ Spec (.of k)))
  let : QuasiCompact (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (U ↘ Spec (.of k)))
  let : IsSeparated (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (U ↘ Spec (.of k)))
  let : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  let : QuasiCompact (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  let : IsSeparated (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  exact support_constructible_of_localization Λ i j hij
    (fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj
      Λ ℓ (k := k) (j.asOver (Spec (.of k))) K hK)

/-- Sections with closed support preserve bounded constructibility for both field
coefficients, and the counit-unit localization triangle has bounded constructible terms.
Finite intermediate fields use their induced norm topology. The algebraic-closure ring
uses finite-subextension-valued continuous functions, not all continuous functions.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-closed-adjoint-constructible-support.md and its proof
(blueprint: det-prop-closed-adjoint-constructible-support).

Proof plan (the seven steps of the DAG node):
1. Finite type over the Noetherian field makes X and Z Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. By
   lem-weil-pbc-noetherian-open-subscheme-noetherian, U is Noetherian and quasi-compact.
   lem-weil-pbc-locally-noetherian-quasi-separated and
   lem-weil-pbc-qcqs-morphism-permanence make j quasi-compact.
2. sk-def-sfb-coefficient-morphisms gives the coefficient isomorphisms. The module
   pullback of sk-def-sfb-module-pushforward-pullback is exact by
   lem-weil-pbc-proetale-immersion-limit-preservation; sk-def-sfb-derived-categories
   therefore identifies the derived inverse images with their termwise functors.
3. det-lem-formal-closed-support-derived gives the normalized support adjunction,
   the localization triangle with open unit, and its closed-pullback fiber formula.
4. lem-weil-pbc-proetale-ringed-open-closed gives exact i_* and j^*i_* = 0.
   lem-weil-pbc-proetale-ringed-closed-counit and
   lem-sc-derived-adjunction-from-underived make the actual derived counit invertible;
   lem-weil-pbc-adjunction-counit-iso-right-fully-faithful gives fully faithful i_*.
   Adjunction kills Hom(i_*A,B) and Hom(i_*A,B[-1]) for B = Rj_*j^*K. Apply
   lem-sfb-orthogonal-triangle-counit-normalization: the first arrow is the actual
   support counit and the second stays the open unit.
5. lem-sfb-dc-upper-star-preserves gives constructible j^*K, and
   lem-sfb-dc-lower-star-preserves gives constructible Rj_*j^*K, for either coefficient.
6. det-cor-coefficient-heart-ii-triangulated gives the remaining vertex and its shift
   from K and Rj_*j^*K by two-out-of-three and shift closure.
7. Apply lem-sfb-dc-upper-star-preserves to i and this vertex. The fiber formula of
   det-lem-formal-closed-support-derived identifies its pullback with RΓ_Z K.
   Isomorphism closure from det-cor-coefficient-heart-ii-triangulated on the Noetherian
   Z completes the assertion. All constructions are for the pulled-back ring objects.
-/
theorem closedSupport_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ClosedSupportConstructibleAssertions (Profinite.continuousMapRingObj.{u} E) i j) ∧
    ClosedSupportConstructibleAssertions (Profinite.padicAlgClRingObj.{u} ℓ) i j := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have : QuasiCompact j := by infer_instance
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rwa [ringChar.eq k p]⟩
  constructor
  · intro E
    let : IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj.{u} E) := .continuous E
    obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicSubfield X ℓ E
    have : (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated :=
      boundedTriangulated_of_serre _ hk he
    exact support_constructible_over_field (Profinite.continuousMapRingObj.{u} E) ℓ k i j hij
  · let : IsFinitenessCoefficient ℓ (Profinite.padicAlgClRingObj.{u} ℓ) := .algebraicClosure
    obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
    have : (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated :=
      boundedTriangulated_of_serre _ hk he
    exact support_constructible_over_field (Profinite.padicAlgClRingObj.{u} ℓ) ℓ k i j hij

end AlgebraicGeometry.ProEtale.CondensedRing
