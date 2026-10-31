/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Local returns for both condensed coefficient fields

Source: latest blueprint, def-weil-local-frobenius-trace, local return convention;
Deligne, Weil II (1.1.7)--(1.1.10) (blueprint: def-weil-local-frobenius-trace).

## Main definitions

- `Modules`, `scalars`, `scalarsOp`, `sections`, `fibre`: the actual point-fibre functor.
- `moduleIterate`, `moduleReturn`: positive module returns with their compositors.
- `derivedIterate`, `returnComparison`, `derivedReturn`: their exact derived counterparts.
- `cohomology`, `cohomologyReturn`, `alternatingTrace`: ordinary cohomology and traces.

The previous interfaces are reexported. Here scalars are the global sections of the
condensed coefficient ring itself, canonically its underlying field in both field cases.
Every comparison is the published module pullback comparison or its exact localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedLocalReturn

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing module category for the pulled-back condensed coefficients.
Source: blueprint coefficient convention (blueprint: def-weil-local-frobenius-trace). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Pullback of constant scalars, acting by multiplication on the regular module.
Source: blueprint pulled-back coefficient convention
(blueprint: def-weil-local-frobenius-trace). -/
def scalars (X : Scheme.{u}) : Γ Λ →+* End (Mod.regular (condensedRingObj Λ X)) :=
  Mod.regularEndRingHom.comp (Γ.mapFunctor (upperStarFromPoint X))

/-- The opposite-ring scalar map used by the existing additive coyoneda functor.
Source: blueprint sections of coefficient modules
(blueprint: def-weil-local-frobenius-trace). -/
def scalarsOp (X : Scheme.{u}) :
    Γ Λ →+* (End (Mod.regular (condensedRingObj Λ X)))ᵐᵒᵖ :=
  (scalars Λ X).toOpposite (fun a b ↦ (map_mul (scalars Λ X) a b).symm.trans
    ((congrArg (scalars Λ X) (mul_comm a b)).trans (map_mul (scalars Λ X) b a)))

/-- Actual point sections, represented by Hom from the regular coefficient module.
Source: blueprint vector-space fibre convention
(blueprint: def-weil-local-frobenius-trace). -/
def sections (k : Type u) [Field k] : Modules Λ (Spec (.of k)) ⥤ ModuleCat.{u + 1} (Γ Λ) :=
  preadditiveCoyonedaObj (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ⋙
    ModuleCat.restrictScalars.{u + 1} (scalarsOp Λ (Spec (.of k)))

/-- Additivity is inherited from additive coyoneda and restriction of scalars.
Source: blueprint point sections (blueprint: def-weil-local-frobenius-trace). -/
instance sections_additive (k : Type u) [Field k] : (sections Λ k).Additive := by
  unfold sections
  infer_instance

/-- Point sections preserve finite limits.
Source: blueprint point sections (blueprint: def-weil-local-frobenius-trace). -/
instance sections_preservesFiniteLimits (k : Type u) [Field k] :
    PreservesFiniteLimits (sections Λ k) := by
  let R := (End (Mod.regular (condensedRingObj Λ (Spec (.of k)))))ᵐᵒᵖ
  let F := ModuleCat.restrictScalars.{u + 1} (scalarsOp Λ (Spec (.of k)))
  have hExact : ∀ S : ShortComplex (ModuleCat.{u + 1} R),
      S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact hS
  have h := ((Functor.exact_tfae F).out 1 3).mp hExact
  have : PreservesFiniteLimits F := h.1
  exact comp_preservesFiniteLimits _ F

/-- Split pro-etale covers make the regular point module projective, hence sections exact.
Source: blueprint point sections and the published separably closed projectivity theorem
(blueprint: def-weil-local-frobenius-trace). -/
instance sections_preservesFiniteColimits (k : Type u) [Field k] [IsSepClosed k] :
    PreservesFiniteColimits (sections Λ k) := by
  let R := (End (Mod.regular (condensedRingObj Λ (Spec (.of k)))))ᵐᵒᵖ
  let F := ModuleCat.restrictScalars.{u + 1} (scalarsOp Λ (Spec (.of k)))
  have hExact : ∀ S : ShortComplex (ModuleCat.{u + 1} R),
      S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact hS
  have h := ((Functor.exact_tfae F).out 1 3).mp hExact
  have : PreservesFiniteColimits F := h.2
  exact comp_preservesFiniteColimits _ F

/-- The actual geometric fibre functor: module inverse image, then point sections.
Source: blueprint derived geometric stalk (blueprint: def-weil-local-frobenius-trace). -/
abbrev fibre (k : Type u) [Field k] {X : Scheme.{u}} (z : Spec (.of k) ⟶ X) :
    Modules Λ X ⥤ ModuleCat.{u + 1} (Γ Λ) :=
  CondensedRing.upperStar Λ z ⋙ sections Λ k

/-- The positive Weil word with the canonical inverse-image compositors.
Index n denotes exponent n+1, including the one-step return at n=0.
Source: blueprint iterated Weil map (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def moduleIterate {X : Scheme.{u}} (a : X ⟶ X) (M : Modules Λ X)
    (θ : (CondensedRing.upperStar Λ a).obj M ≅ M) :
    (n : ℕ) → (CondensedRing.upperStar Λ (localPositivePower a n)).obj M ≅ M
  := CondensedModule.isoChain
    (fun n ↦ (CondensedRing.upperStar Λ (localPositivePower a n)).obj M) M
    (CondensedModule.evaluateInitial
      (CondensedRing.upperStar Λ (localPositivePower a 0)) (CondensedRing.upperStar Λ a)
      (CondensedRing.upperStarCongr Λ (show localPositivePower a 0 = a from rfl)) M θ)
    (fun n ↦ CondensedModule.evaluateStep
      (CondensedRing.upperStar Λ (localPositivePower a n)) (CondensedRing.upperStar Λ a)
      (CondensedRing.upperStar Λ (localPositivePower a (n + 1)))
      (CondensedRing.upperStarComp Λ (localPositivePower a n) a) M θ)

/-- The actual module return, including the semilinear source reparametrization.
Source: blueprint local-return formula (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def moduleReturn (D : FiniteFieldDatum.{u}) {X : Scheme.{u}} (a : X ⟶ X)
    (M : Modules Λ X) (θ : (CondensedRing.upperStar Λ a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) : End ((fibre Λ D.k z).obj M) :=
  ((sections Λ D.k).mapIso
    ((CondensedRing.pointComparison Λ
      (CondensedRing.upperStarIsoIdOfIsSepClosed Λ
        (localPositivePower (frobeniusPointIso D).hom n))
      (localPositivePower a n) h).app M ≪≫
      (CondensedRing.upperStar Λ z).mapIso (moduleIterate Λ a M θ n))).hom

/-- The exact derived positive Weil word, with the localized canonical compositor.
Source: blueprint iterated Weil map (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def derivedIterate {X : Scheme.{u}} (a : X ⟶ X) (K : DerivedCategory (Modules Λ X))
    (φ : (CondensedRing.upperStar Λ a).mapDerivedCategory.obj K ≅ K) :
    (n : ℕ) → (CondensedRing.upperStar Λ (localPositivePower a n)).mapDerivedCategory.obj K ≅ K
  := CondensedModule.isoChain
    (fun n ↦ (CondensedRing.upperStar Λ (localPositivePower a n)).mapDerivedCategory.obj K)
    K ((Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarCongr Λ (show localPositivePower a 0 = a from rfl))).app K ≪≫ φ)
    (fun n ↦
      (Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarComp Λ (localPositivePower a n) a)).app K ≪≫
      (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ a)
        (CondensedRing.upperStar Λ (localPositivePower a n))).app K ≪≫
      (CondensedRing.upperStar Λ (localPositivePower a n)).mapDerivedCategory.mapIso φ)

/-- The normalized comparison of the returned fibre with the fibre of iterated pullback.
Source: blueprint semilinear return (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def returnComparison (D : FiniteFieldDatum.{u}) {X : Scheme.{u}} (a : X ⟶ X)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    fibre Λ D.k z ≅ CondensedRing.upperStar Λ (localPositivePower a n) ⋙ fibre Λ D.k z :=
  Functor.isoWhiskerRight
    ((Functor.rightUnitor (CondensedRing.upperStar Λ z)).symm ≪≫
      CondensedRing.pointComparison Λ
        (CondensedRing.upperStarIsoIdOfIsSepClosed Λ
          (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h)
    (sections Λ D.k) ≪≫ Functor.associator _ _ _

/-- The derived local return on the actual condensed fibre complex.
Source: blueprint local-return formula (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def derivedReturn (D : FiniteFieldDatum.{u}) {X : Scheme.{u}} (a : X ⟶ X)
    (K : DerivedCategory (Modules Λ X))
    (φ : (CondensedRing.upperStar Λ a).mapDerivedCategory.obj K ≅ K)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    End ((fibre Λ D.k z).mapDerivedCategory.obj K) :=
  ((Functor.mapDerivedCategoryNatIso (returnComparison Λ D a z n h)).app K ≪≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar Λ (localPositivePower a n)) (fibre Λ D.k z)).app K ≪≫
    (fibre Λ D.k z).mapDerivedCategory.mapIso (derivedIterate Λ a K φ n)).hom

/-- The actual local cohomology vector space, without a finite-stage model.
Source: blueprint fibre/cohomology convention (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def cohomology (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (K : DerivedCategory (Modules Λ X)) (z : Spec (.of k) ⟶ X) (j : ℤ) :
    ModuleCat.{u + 1} (Γ Λ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) j).obj
    ((fibre Λ k z).mapDerivedCategory.obj K)

/-- The ordinary local cohomology operator in degree j.
Source: blueprint local trace (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def cohomologyReturn (D : FiniteFieldDatum.{u}) {X : Scheme.{u}} (a : X ⟶ X)
    (K : DerivedCategory (Modules Λ X))
    (φ : (CondensedRing.upperStar Λ a).mapDerivedCategory.obj K ≅ K)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (j : ℤ) :
    End (cohomology Λ D.k K z j) := by
  unfold cohomology
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) j).map
    (derivedReturn Λ D a K φ z n h)

/-- The finite alternating trace, written as finsum to avoid choosing a support interval.
Source: blueprint alternating local trace (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def alternatingTrace (D : FiniteFieldDatum.{u}) {X : Scheme.{u}} (a : X ⟶ X)
    (K : DerivedCategory (Modules Λ X))
    (φ : (CondensedRing.upperStar Λ a).mapDerivedCategory.obj K ≅ K)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) : Γ Λ :=
  ∑ᶠ j : ℤ, (if Even j then 1 else -1 : Γ Λ) *
    LinearMap.trace (Γ Λ) (cohomology Λ D.k K z j)
      (cohomologyReturn Λ D a K φ z n h j).hom

end WeilConjectures.CondensedLocalReturn
