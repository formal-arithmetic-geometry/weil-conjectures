/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-! # Finite-free carriers and scalar matrices at the condensed point

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7.
This is the carrier sub-step preceding the dimension-zero Jordan filtration.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

-- Split-cover argument as in CondensedFinite.point_finitelyPresented.
-- This proves the underived part of the point classification used below.
private theorem point_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstantModelConstructible Λ X M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ X) :
    Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of Ω)))
      ((CondensedRing.upperStar Λ a).obj M) := by
  classical
  obtain ⟨S, hS⟩ : IsFiniteConstantStratified Λ X M := by
    simpa only [IsConstantModelConstructible, if_pos (show CompactSpace X ∧
      QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)] using hM
  let z : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (a z))
  rw [← S.range_immersion i] at hi
  obtain ⟨b, hb⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField
    (S.immersion i) (Field.toIsField Ω) a z hi
  obtain ⟨U, hU⟩ := hS i
  obtain ⟨j, c, hc⟩ := U.exists_comp_eq_of_isField
    (Field.toIsField Ω) IsField.isSepClosed_toField b
  obtain ⟨P, hP, ⟨e⟩⟩ := hU j
  let F := (upperStarFromPoint (U.X j)).mapMod Λ
  have : PreservesColimits (upperStarFromPoint (U.X j)) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (U.X j)))).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint (U.X j)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint (U.X j)).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : F.Additive :=
    ⟨Mod.hom_ext _ _ (Functor.map_add (upperStarFromPoint (U.X j)))⟩
  have hF : Mod.IsFinitelyPresented (condensedRingObj Λ (U.X j)) (F.obj P) :=
    hP.map F (Mod.isoMk (Iso.refl _) (by simp))
  have h₁ := CondensedRing.IsFinitelyPresented.upperStar Λ c (hF.of_iso e.symm)
  exact h₁.of_iso
    ((CondensedRing.upperStar Λ c).mapIso
        ((CondensedRing.upperStarComp Λ (U.f j) (S.immersion i)).app M).symm ≪≫
      ((CondensedRing.upperStarComp Λ c (U.f j ≫ S.immersion i)).app M).symm ≪≫
      eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
        (by rw [reassoc_of% hc, hb])))

private theorem point_entry_bijective (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] [IsAlgClosed D.k] :
    Function.Bijective (fun f : End (Mod.regular
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k)))) ↦
      ((NativeCondensedModule.pointSectionsUnitIso l D.k).inv.hom
        ((NativeCondensedModule.pointSections l D.k).map f
          (NativeCondensedModule.pointSectionsUnit l D.k))).down) := by
  let e := NativeCondensedModule.pointSectionsUnitIso l D.k
  have h : Function.Bijective (fun f : End (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k)))) ↦
      (e.inv.hom f).down) := by
    exact ULift.down_bijective.comp e.toLinearEquiv.symm.bijective
  change Function.Bijective (fun f : End (Mod.regular
    (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k)))) ↦
      (e.inv.hom (𝟙 _ ≫ f)).down)
  simpa only [Category.id_comp] using h

private theorem point_matrix_bijective (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (a b : ℕ) :
    Function.Bijective (matrix D l (a := a) (b := b)) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : IsIso (pointLift D) := by unfold pointLift; infer_instance
  let F := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (pointLift D)
  have hr : Function.Bijective (CondensedRing.restrictEnd
      (Profinite.padicAlgClRingObj l) (pointLift D)) := by
    unfold CondensedRing.restrictEnd
    exact (CondensedRing.upperStarObjRegularIso _ _).conjRingEquiv.bijective.comp
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective _ _)
  have he := (point_entry_bijective D l).comp hr
  constructor
  · intro f g h
    apply (biproduct.matrixEquiv (f := fun _ : Fin a ↦ Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj l) (pointSpace D)))
      (g := fun _ : Fin b ↦ Mod.regular
        (condensedRingObj (Profinite.padicAlgClRingObj l) (pointSpace D)))).injective
    funext j i
    exact he.1 (congrFun (congrFun h i) j)
  · intro A
    classical
    choose t ht using fun i j ↦ he.2 (A i j)
    refine ⟨biproduct.matrix (fun j i ↦ t i j), ?_⟩
    ext i j
    change ((NativeCondensedModule.pointSectionsUnitIso l D.k).inv.hom
      ((NativeCondensedModule.pointSections l D.k).map
        (CondensedRing.restrictEnd _ _
          (biproduct.components (biproduct.matrix (fun j i ↦ t i j)) j i))
        (NativeCondensedModule.pointSectionsUnit l D.k))).down = A i j
    rw [biproduct.matrix_components]
    exact ht i j

/-- The carrier and matrix identifications needed before constructing a Weil flag.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-condensed-point-weil-carrier-data).

Proof: A constructible module has a finite constant stratification. A geometric point
lands in one stratum, and the covering over that stratum splits over the separably
closed field. Pull back its constant finite presentation. Gaussian elimination over
the coefficient field identifies its cokernel with a finite sum of regular modules.
The point lift is an isomorphism, so fully faithful pullback transports this basis
back to the given carrier. On regular endomorphisms, normalized unit sections are
a scalar isomorphism; applying this entrywise to biproducts gives the matrix bijection.
Empty biproducts and zero-dimensional cokernels are included.
-/
theorem point_carrier_data (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (M : NativeL2.WeilModule D l (pointModel D))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (pointSpace D)
      M.carrier) :
    (∀ a b : ℕ, Function.Bijective (matrix D l (a := a) (b := b))) ∧
      ∃ d : ℕ, Nonempty (M.carrier ≅ free D l d) := by
  classical
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hpoint : IsIso (pointLift D) := by unfold pointLift; infer_instance
  have : IsAffine (pointSpace D) := IsAffine.of_isIso (asIso (pointLift D)).inv
  let F := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (pointLift D)
  obtain ⟨n, m, f, ⟨e⟩⟩ := point_finitelyPresented _ hM (pointLift D)
  obtain ⟨d, ⟨e'⟩⟩ := Limits.exists_iso_biproduct_cokernel
    (CondensedRing.isIso_of_ne_zero_end_tensorUnit l
      (Field.toIsField D.k) IsField.isSepClosed_toField) (Iso.refl _) (Iso.refl _) f
  let e₀ : M.carrier ≅ free D l d :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
      (e ≪≫ e' ≪≫ (CondensedRing.upperStarFiniteFreeIso _ (pointLift D) d).symm)
  exact ⟨point_matrix_bijective D l, d, ⟨e₀⟩⟩

end WeilConjectures.CondensedWeilPointFlags
