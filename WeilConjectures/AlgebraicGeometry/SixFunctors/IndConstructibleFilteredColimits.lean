/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Filtered colimits and sums of ind-constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart,
`sk-prop-ind-heart-filtered-colimits.md` and its proof
(blueprint: det-ind-heart-filtered-colimits).

The standing geometric hypotheses are those of `sk-def-sfb-dc-setting`.
`ObjectProperty.ind.{u + 1}` of `IsConstantModelConstructible` is precisely IndCons:
small filtered presentations in the actual internal-module category, closed under isomorphism.
The two statements cover respectively a finite coefficient subextension and the condensed
algebraic closure. Coproducts are stated using arbitrary colimit cofans, including the empty one.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

private theorem ind_finite_coproduct
    {C : Type*} [Category.{u + 1} C] [HasColimitsOfSize.{u + 1, u + 1} C]
    (P : ObjectProperty C)
    (hfin : ∀ (S : Type (u + 1)) [Finite S] (B : S → C),
      (∀ s, P (B s)) → P (∐ B))
    (S : Type (u + 1)) [Finite S] (B : S → C)
    (hB : ∀ s, P.ind.{u + 1} (B s)) : P.ind.{u + 1} (∐ B) := by
  classical
  choose J _ _ pres hpres using hB
  let F : (∀ s, J s) ⥤ (S → C) := Functor.pi (fun s ↦ (pres s).diag)
  let c : Cocone F := pi.coconeOfCoconeCompEval
    (fun s ↦ (pres s).cocone.whisker (Pi.eval J s))
  have hc : IsColimit c := pi.coconeOfCoconeEvalIsColimit
    (fun s ↦ (Functor.Final.isColimitWhiskerEquiv (Pi.eval J s)
      (pres s).cocone).symm (pres s).isColimit)
  let : PreservesColimitsOfShape (∀ s, J s) (Sigma.functor S : (S → C) ⥤ C) := by
    rw [← piEquivalenceFunctorDiscrete_functor_comp_colim]
    infer_instance
  exact ⟨∀ s, J s, inferInstance, inferInstance,
    { diag := F ⋙ Sigma.functor S
      ι := (Sigma.functor S).mapCocone c |>.ι
      isColimit := isColimitOfPreserves (Sigma.functor S) hc },
    fun j ↦ hfin S (fun s ↦ (pres s).diag.obj (j s)) (fun s ↦ hpres s (j s))⟩

private theorem ind_coproduct
    {C : Type*} [Category.{u + 1} C] [LocallySmall.{u + 1} C]
    [HasColimitsOfSize.{u + 1, u + 1} C]
    (P : ObjectProperty C) (hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} C)
    (hfin : ∀ (S : Type (u + 1)) [Finite S] (B : S → C),
      (∀ s, P (B s)) → P (∐ B))
    (S : Type (u + 1)) (B : S → C) (c : Cofan B) (hc : IsColimit c)
    (hB : ∀ s, P.ind.{u + 1} (B s)) : P.ind.{u + 1} c.pt := by
  classical
  apply (P.ind).prop_of_iso ((colimit.isColimit _).coconePointUniqueUpToIso hc)
  rw [← ObjectProperty.ind_ind hfp]
  exact ⟨Finset (Discrete S), inferInstance, inferInstance,
    { diag := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor B)
      ι := (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone B).ι
      isColimit := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone B },
    fun T ↦ ind_finite_coproduct P hfin T (fun t ↦ B t.val.as) (fun t ↦ hB t.val.as)⟩

namespace AlgebraicGeometry.ProEtale

private theorem constructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) := by
  have hloc (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨U, hU⟩ := h
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hU i
    exact ⟨Q, hQ, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eQ⟩⟩
  have hstrat (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hloc _ _ _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  constructor
  intro M N e h
  unfold IsConstantModelConstructible at h ⊢
  split_ifs at h ⊢ with hX
  · exact hstrat _ _ _ e h
  · intro U hU
    exact hstrat _ _ _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (h U hU)

private theorem constructible_finite_coproduct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [HasFiniteColimits (ConstantModelConstructible Λ X)]
    [PreservesFiniteColimits (ObjectProperty.ι (IsConstantModelConstructible Λ X))]
    (S : Type (u + 1)) [Finite S]
    (B : S → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hB : ∀ s, IsConstantModelConstructible Λ X (B s)) :
    IsConstantModelConstructible Λ X (∐ B) := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) :=
    constructible_iso Λ X
  let : ObjectProperty.IsClosedUnderColimitsOfShape
      (IsConstantModelConstructible Λ X) (Discrete S) :=
    ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _ _
  exact ObjectProperty.prop_colimit (IsConstantModelConstructible Λ X)
    (Discrete.functor B) (fun s ↦ hB s.as)

end AlgebraicGeometry.ProEtale
