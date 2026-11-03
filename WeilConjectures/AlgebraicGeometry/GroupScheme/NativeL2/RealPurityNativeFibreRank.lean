/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The actual native fibre and its additive rank

Source: sk-p-real-purity, finite composition filtration
(blueprint: lem-rp-native-fibre-rank).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

private instance native_sections_additive (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] :
    (pointSections l k).Additive := by
  unfold pointSections
  infer_instance

private instance native_sections_limits (l : ℕ) [Fact l.Prime] (k : Type u)
    [Field k] [IsSepClosed k] : PreservesFiniteLimits (pointSections l k) := by
  let F := pointSections l k
  refine ⟨fun J _ _ ↦ ?_⟩
  have : PreservesLimitsOfShape J (F ⋙
      forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) Ab.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape J
      (preadditiveCoyonedaObj (Mod.regular
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of k)))) ⋙
          forget₂ _ Ab.{u + 1}))
  exact preservesLimitsOfShape_of_reflects_of_preserves F
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) Ab.{u + 1})

private instance native_sections_colimits (l : ℕ) [Fact l.Prime] (k : Type u)
    [Field k] [IsSepClosed k] : PreservesFiniteColimits (pointSections l k) := by
  let F := pointSections l k
  have : F.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    apply (ModuleCat.epi_iff_surjective (F.map f)).2
    intro x
    obtain ⟨y, hy⟩ := Projective.factors
      (show Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Spec (.of k))) ⟶ N from x) f
    exact ⟨y, hy⟩⟩
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  exact Functor.preservesFiniteColimits_of_preservesHomology F

/-- Pullback of a lisse actual module to a geometric point is finite free.
Source: sk-p-real-purity, exact fibre and composition-filtration step
(blueprint: lem-rp-native-fibre-rank).

Proof: lift the geometric point through one member of a lisse trivializing cover.
Pull back its finite-free coordinates and use the pullback-composition isomorphism.
Point sections preserve finite biproducts, and the coefficient-unit sections are the
one-dimensional scalar field. Thus this actual native fibre is finite-dimensional. -/
theorem native_fibre_finite_of_lisse
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (M : Modules l X)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M)
    (z : Spec (.of D.k) ⟶ X) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M z) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨U, hU⟩ := hM
  obtain ⟨i, a, ha⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale z
  have hfree := (hU i).map
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
    (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l) a)
  have hfree' := hfree.of_iso
    (((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) a (U.f i)).app M).symm ≪≫
      eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar
        (Profinite.padicAlgClRingObj l) f).obj M) ha))
  obtain ⟨r, ⟨e⟩⟩ := hfree'
  let F := pointSections l D.k
  let e' := F.mapIso e ≪≫ F.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ : Fin r ↦ (pointSectionsUnitIso l D.k).symm) ≪≫
    ModuleCat.biproductIsoPi _
  exact Module.Finite.equiv e'.toLinearEquiv.symm

/-- The dimension of the actual native fibre is additive on a monomorphism of lisse
Weil modules. Source: sk-p-real-purity, composition-filtration rank induction
(blueprint: lem-rp-native-fibre-rank).

Proof: forgetting the Weil map, inverse image and point sections are exact. Apply them
to the canonical short exact sequence of a monomorphism and its cokernel. The outer
fibres are finite-dimensional, so dimension additivity gives the displayed equality. -/
theorem native_fibre_rank_add
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    {M N : WeilModule D l X₀} (f : M ⟶ N) [Mono f]
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hQ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (cokernel f).carrier) :
    Module.finrank (ULift.{u + 1} (PadicAlgCl l)) (fibre l D N.carrier z) =
      Module.finrank (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M.carrier z) +
      Module.finrank (ULift.{u + 1} (PadicAlgCl l))
        (fibre l D (cokernel f).carrier z) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let F := Endofunctor.IsoAlgebra.forget
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom) ⋙
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
      inferInstance inferInstance
  have : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (F.obj M) :=
    native_fibre_finite_of_lisse D l M.carrier hM z
  have : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (F.obj (cokernel f)) :=
    native_fibre_finite_of_lisse D l (cokernel f).carrier hQ z
  let S := (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map F
  have : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) S.X₁ :=
    native_fibre_finite_of_lisse D l M.carrier hM z
  have : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) S.X₃ :=
    native_fibre_finite_of_lisse D l (cokernel f).carrier hQ z
  exact ModuleCat.free_shortExact_finrank_add (S := S) (hS.map_of_exact F) rfl rfl

end WeilConjectures.NativeL2
