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

private lemma constructible_iso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (hM : IsConstructibleModuleObject R M) :
    IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hS a
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h𝒰 i
  exact ⟨n, m, f, ⟨(((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R ⋙
    (ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod _).mapIso e).symm ≪≫ e'⟩⟩

private lemma bounded_iso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (e : K ≅ L) (hK : boundedConstructible R K) : boundedConstructible R L := by
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ constructible_iso R ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

private lemma bounded_replete {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (boundedConstructible R).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ bounded_iso R e h⟩

private lemma bounded_triangulated {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hk : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
        IsConstructibleModuleObject R (kernel f) ∧
        IsConstructibleModuleObject R (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
        IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e h ↦ constructible_iso R e h⟩
  have : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) := ⟨by
    rintro Y ⟨f, k, hk', hf⟩
    exact constructible_iso R (limit.isoLimitCone ⟨k, hk'⟩) (hk _ _ f hf.1 hf.2).1⟩
  have : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) := ⟨by
    rintro Y ⟨f, k, hk', hf⟩
    exact constructible_iso R (colimit.isoColimitCocone ⟨k, hk'⟩) (hk _ _ f hf.1 hf.2).2⟩
  have : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) :=
    ⟨fun hS h₁ h₃ ↦ he _ hS h₁ h₃⟩
  infer_instance

private noncomputable def pullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : upperStar Λ f ≅ formalSupportPullback Λ f :=
  Adjunction.leftAdjointUniq (upperStarLowerStarAdjunction Λ f)
    (formalSupportPullbackAdjunction Λ f)

private lemma support_of_triangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsFinitenessCoefficient ℓ Λ]
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated] :
    ClosedSupportConstructibleAssertions Λ i j := by
  have : (boundedConstructible (condensedRingObj Λ X)).IsClosedUnderIsomorphisms :=
    bounded_replete _
  have hpull {T S : Scheme.{u}} [T.Over (Spec (.of k))] [S.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
      [IsSeparated (S ↘ Spec (.of k))]
      (f : T ⟶ S) [f.IsOver (Spec (.of k))]
      (K : DerivedCategory (FormalSupportModules Λ S))
      (hK : boundedConstructible (condensedRingObj Λ S) K) :
      boundedConstructible (condensedRingObj Λ T)
        ((formalSupportPullback Λ f).mapDerivedCategory.obj K) := by
    have : LocallyOfFiniteType (OverClass.asOver T (Spec (.of k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (T ↘ Spec (.of k)))
    have : QuasiCompact (OverClass.asOver T (Spec (.of k))).hom :=
      inferInstanceAs (QuasiCompact (T ↘ Spec (.of k)))
    have : IsSeparated (OverClass.asOver T (Spec (.of k))).hom :=
      inferInstanceAs (IsSeparated (T ↘ Spec (.of k)))
    have : LocallyOfFiniteType (OverClass.asOver S (Spec (.of k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (S ↘ Spec (.of k)))
    have : QuasiCompact (OverClass.asOver S (Spec (.of k))).hom :=
      inferInstanceAs (QuasiCompact (S ↘ Spec (.of k)))
    have : IsSeparated (OverClass.asOver S (Spec (.of k))).hom :=
      inferInstanceAs (IsSeparated (S ↘ Spec (.of k)))
    exact bounded_iso _
      (((leftDerivedUpperStarIsoMapDerivedCategory Λ f) ≪≫
        Functor.mapDerivedCategoryNatIso (pullbackComparison Λ f)).app K)
      (boundedConstructible_leftDerivedUpperStar_obj Λ ℓ (f.asOver (Spec (.of k))) K hK)
  have hji : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  obtain ⟨_, _, a, ha, _, _, _, _, hex, b, c, δ, hb, hc, ht, hf⟩ :=
    formal_closed_support_adjunction.{u, u + 1} Λ i j hji
  refine ⟨a, ha, fun K ↦ ?_⟩
  let d := δ.app K.obj
  have hd : Triangle.mk (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj)
      ((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
        K.obj) d ∈ distTriang _ := by
    simpa only [hb, hc] using ht K.obj
  have : LocallyOfFiniteType (OverClass.asOver U (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (U ↘ Spec (.of k)))
  have : QuasiCompact (OverClass.asOver U (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (U ↘ Spec (.of k)))
  have : IsSeparated (OverClass.asOver U (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (U ↘ Spec (.of k)))
  have : LocallyOfFiniteType (OverClass.asOver X (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact (OverClass.asOver X (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated (OverClass.asOver X (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have hB : boundedConstructible (condensedRingObj Λ X)
      ((lowerStar Λ j).rightDerivedFunctor.obj
        ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj)) :=
    boundedConstructible_rightDerivedLowerStar_obj Λ ℓ (j.asOver (Spec (.of k))) _
      (hpull j K.obj K.property)
  have hF := (boundedConstructible (condensedRingObj Λ X)).ext_of_isTriangulatedClosed₁
    _ hd K.property hB
  refine ⟨d, hd, hF, hB,
    (boundedConstructible (condensedRingObj Λ X)).le_shift 1 _ hF, ?_⟩
  obtain ⟨e⟩ := hf K.obj _ _ d (by simpa only [hc] using hd)
  exact bounded_iso _ e.symm (hpull i _ hF)

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
  have hchar : ringChar k = p := ringChar.eq k p
  have : Fact (ringChar k).Prime := ⟨hchar ▸ Fact.out⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨hchar ▸ hpℓ⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  have : QuasiCompact j := inferInstance
  constructor
  · intro E
    have hserre := isConstructibleModuleObject_serre_padicSubfield X ℓ E
    have : (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated :=
      bounded_triangulated _ hserre.1 hserre.2
    exact support_of_triangulated _ ℓ k i j hij
  · have hserre := isConstructibleModuleObject_serre_padicAlgCl X ℓ
    have : (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated :=
      bounded_triangulated _ hserre.1 hserre.2
    exact support_of_triangulated _ ℓ k i j hij

end AlgebraicGeometry.ProEtale.CondensedRing
