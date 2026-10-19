/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import all Sheaf.AlgebraicGeometry.EllAdicFiniteIndHeartWeakSerre
import Sheaf.AlgebraicGeometry.EllAdicIntegralConstructibleHeartBound
import all Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
import Sheaf.Paper.ProperHeartBound
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.LocallyFreeConstantModelComparison
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Proper upper bound on the ind-constructible heart

This isolates the class-relative upper-amplitude argument from the truncation-window
corollary. Source: blueprint `sk-lem-proper-unbounded-window` and
`det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: new-lem-sfb-adic-proper-heart-upper-bound)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
private theorem proper_heart_bound_ind
    (P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))) (c : ℕ)
    (hc : ∀ M, P M → ∀ j : ℤ, (c : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((R((f)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : P.ind.{u + 1} M) (j : ℤ) (hj : (c : ℤ) < j) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((R((f)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  obtain ⟨J, _, _, pres, hp⟩ := hM
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let T := DerivedCategory.singleFunctor A 0 ⋙ R((f)_*⟦Λ⟧) ⋙
    DerivedCategory.homologyFunctor _ j
  let S := CochainComplex.singleFunctor A 0
  have : PreservesColimit pres.diag S := by
    change PreservesColimit pres.diag (HomologicalComplex.single A (.up ℤ) 0)
    infer_instance
  have : PreservesColimit (pres.diag ⋙ S)
      (DerivedCategory.Q ⋙ R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor _ j) :=
    continuity_preserves_strictlyGE Λ f (pres.diag ⋙ S) 0 j (fun i ↦ by
      change ((CochainComplex.singleFunctor A 0).obj (pres.diag.obj i)).IsStrictlyGE 0
      infer_instance)
  have : PreservesColimit pres.diag
      (S ⋙ DerivedCategory.Q ⋙ R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor _ j) :=
    inferInstance
  have : PreservesColimit pres.diag T :=
    preservesColimit_of_natIso pres.diag
      ((Functor.associator S DerivedCategory.Q _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0).symm _)
  exact (isColimitOfPreserves T pres.isColimit).isZero_pt
    ((pres.diag ⋙ T).isZero_iff.mpr (fun a ↦ hc _ (hp a) j hj))
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k

private theorem padicAlgCl_proper_heart_upper_bound :
    ∃ c : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left),
      ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)) M →
      ∀ j : ℤ, (c : ℤ) < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj
          ((R((g.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : Z.left.Over (Spec (.of k)) := ⟨Z.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)
  have : IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  have : g.left.IsOver (Spec (.of k)) := ⟨g.w⟩
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := {}
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le Z.hom
  have hdim (y : Y.left) (n : ℕ)
      (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback g.left (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y)))) ≫
            Y.left.fromSpecResidueField y) : Scheme.{u})) : (n : ℤ) ≤ d := by
    have h := hn.trans ((topologicalKrullDim_pullback_le g.left _).trans hd)
    exact_mod_cast h
  have heq := constructible_eq_constantModels_of_lfp_locally_free
    (Profinite.padicAlgClRingObj ℓ) (algcl_lf ℓ) Z.left
  have h := (properHeartBound_padicAlgCl ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ)
    Z.left Y.left g.left d hdim).1
  refine ⟨2 * d + 1, fun M hM j hj ↦ ?_⟩
  rw [heq] at hM
  exact (h M hM).1 j (by exact_mod_cast hj)
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

/-- Proper pushforward has uniformly bounded cohomology on ind-constructible heart objects.

Source: blueprint `sk-lem-proper-heart-bound` and
`det-prop-int-compactness-direct-sums`, proof (1)-(2).
(blueprint: new-lem-sfb-adic-proper-heart-upper-bound)

Proof: choose a uniform bound d on the dimensions of geometric fibres of g.
For finite field coefficients, proper finiteness and the finite cohomological
bound give vanishing above 2d for constructible sheaves. The algebraic closure
case descends every finite presentation and finite diagram to a finite coefficient
extension. In the integral case, the local torsion charts and finite locally free
resolutions put derived torsion reductions in degrees [-1,0]. Their proper images
vanish above 2d. The Milnor exact sequence of the countable adic tower loses at most
one degree, so 2d+1 works. Finally write an ind-constructible heart object as its
filtered colimit of constructibles. Bounded-below filtered continuity of proper
pushforward gives the same vanishing for this colimit in the ordinary module-sheaf
category. Set c=2d+1 in all cases; zero sheaves and empty fibres satisfy the same bound.
-/
theorem ellAdic_proper_heart_upper_bound :
    ∃ c : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj Λ Z.left),
      ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject (condensedRingObj Λ Z.left)) M →
      ∀ j : ℤ, (c : ℤ) < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj
          ((R((g.left)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  cases hΛ with
  | continuous E => exact continuous_proper_heart_upper_bound ℓ g E
  | algebraicClosure => exact padicAlgCl_proper_heart_upper_bound ℓ g
  | integral E =>
    obtain ⟨c, hc⟩ := ellAdic_integral_constructible_heart_upper_bound ℓ g E
    exact ⟨c, fun M hM j hj ↦ proper_heart_bound_ind _ g.left _ c hc M hM j hj⟩

end AlgebraicGeometry.ProEtale.CondensedRing
