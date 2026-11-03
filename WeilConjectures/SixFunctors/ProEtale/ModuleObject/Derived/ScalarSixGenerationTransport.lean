/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Transport of finite scalar generation along coefficient isomorphisms

Source: blueprint latest, scalar-six-ctf proof (1), coefficient presentations.
(blueprint: lem-sfb-scalar-six-generation-coefficient-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem finiteGeneration_map
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (G : ObjectProperty C) (H : ObjectProperty D)
    (hg : ∀ K, G K → H (F.obj K)) (n : ℕ) (K : C)
    (hK : ((G.shiftClosure ℤ).extensionProductIter n).retractClosure K) :
    ((H.shiftClosure ℤ).extensionProductIter n).retractClosure (F.obj K) := by
  have hiso (m : ℕ) :
      ((H.shiftClosure ℤ).extensionProductIter m).IsClosedUnderIsomorphisms := by
    induction m with
    | zero => exact inferInstanceAs (H.shiftClosure ℤ).IsClosedUnderIsomorphisms
    | succ m ih => rw [ObjectProperty.extensionProductIter_succ]; infer_instance
  have hiter (m : ℕ) : ∀ K, (G.shiftClosure ℤ).extensionProductIter m K →
      (H.shiftClosure ℤ).extensionProductIter m (F.obj K) := by
    induction m with
    | zero =>
      rintro K ⟨L, a, e, hL⟩
      exact ⟨F.obj L, a, F.mapIso e ≪≫ (F.commShiftIso a).app L, hg L hL⟩
    | succ m ih =>
      rw [ObjectProperty.extensionProductIter_succ,
        ObjectProperty.extensionProductIter_succ]
      rintro K ⟨A, B, f, g, h, ht, hA, hB⟩
      have hA' : H.shiftClosure ℤ (F.obj A) := by
        obtain ⟨L, a, e, hL⟩ := hA
        exact ⟨F.obj L, a, F.mapIso e ≪≫ (F.commShiftIso a).app L, hg L hL⟩
      exact ⟨_, _, _, _, _, F.map_distinguished _ ht, hA', ih B hB⟩
  obtain ⟨L, hL, ⟨r⟩⟩ := hK
  exact ⟨F.obj L, hiter n L hL, ⟨r.map F⟩⟩

private theorem change_locallyPerfect {Λ Γ : ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    (S : Scheme.{u})
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hP : IsLocallyPerfectScalarModel Λ.X S P) :
    IsLocallyPerfectScalarModel Γ.X S ((scalarSixChange a S).obj P) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hP
  choose C l h hl hh hp e using h𝒰
  have hc := sfbPerfectScalarChangeModel (Λ := Λ.X) (Λ' := Γ.X)
    a.hom.hom S P 𝒰 C
    (fun j ↦ ⟨l j, h j, hl j, hh j⟩) hp (fun j ↦ (e j).some)
  refine ⟨𝒰, fun j ↦ ?_⟩
  have hb := sfbPerfectScalarChangeModels (Λ := Λ.X) (Λ' := Γ.X)
    a.hom.hom (𝒰.X j) (C j) (l j) (h j) (hl j) (hh j) (hp j)
  exact ⟨sfbScalarChangedComplex (Λ := Λ.X) (Λ' := Γ.X) a.hom.hom (C j),
    l j, h j, hb.1, hb.2.1, hb.2.2.1,
    ⟨(hc j).1.some ≪≫ (hc j).2.some⟩⟩

/-- A native coefficient generation theorem transports through any ring-object
isomorphism. The extension length is preserved.

Source: blueprint latest, scalar-six-ctf proof (1), coefficient presentations.
(blueprint: lem-sfb-scalar-six-generation-coefficient-transport).

Proof: restrict along the inverse isomorphism to obtain a constructible finite-Tor
object over the native ring. Derived extension back is left adjoint to this exact
restriction equivalence, so its counit is invertible. Scalar change preserves locally
perfect models and commutes with the canonical locally closed extension. It therefore
sends each native generator to a generator. Apply it to the finite witness: its shift
comparison handles shifted generators, distinguished triangles handle extensions,
and functoriality handles retracts. Finally use the counit to recover the original
object. This argument preserves the finite number of extensions. -/
theorem sfbGeneration_coefficientIso (ell : ℕ) [Fact ell.Prime]
    {Λ Γ : ScalarSixRing.{u}} (e : Mon.mk Λ.X ≅ Mon.mk Γ.X)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (hΓ : ∀ K : ConstantModelConstructibleFiniteTor Γ.X X.left,
      ∃ n : ℕ, (((sfbPerfectScalarGenerator Γ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K.obj)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by
  classical
  let a : Γ ⟶ Λ := ⟨e.inv⟩
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso (coefficientMap e.inv.hom X.left) := by
    dsimp [coefficientMap]
    infer_instance
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (coefficientMap e.inv.hom X.left)
  have : U.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap e.inv.hom X.left)
      ).functor.IsEquivalence
  let K' : ConstantModelConstructibleFiniteTor Γ.X X.left :=
    ⟨U.mapDerivedCategory.obj K.obj, constantModelCtf_coefficientIso e X.left K⟩
  let F := scalarSixChange a X.left
  let adj : F ⊣ U.mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap e.inv.hom X.left)
  let : F.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := adj.isTriangulated_leftAdjoint
  have : U.mapDerivedCategory.IsEquivalence := inferInstance
  have hg : ∀ L, sfbPerfectScalarGenerator Γ X L →
      sfbPerfectScalarGenerator Λ X (F.obj L) := by
    rintro L ⟨S, i, hi, P, hP, ⟨q⟩⟩
    obtain ⟨c⟩ := sfbCanonicalExtensionScalarComparison a ell k X S i hi P
    exact ⟨S, i, hi, (scalarSixChange a S).obj P,
      change_locallyPerfect a S P hP, ⟨F.mapIso q ≪≫ c⟩⟩
  obtain ⟨n, hn⟩ := hΓ K'
  refine ⟨n, ?_⟩
  have hm := finiteGeneration_map F (sfbPerfectScalarGenerator Γ X)
    (sfbPerfectScalarGenerator Λ X) hg n K'.obj hn
  have hi : (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure.IsClosedUnderIsomorphisms := inferInstance
  exact ObjectProperty.prop_of_iso _ (asIso (adj.counit.app K.obj)) hm

end AlgebraicGeometry.ProEtale.CondensedRing
