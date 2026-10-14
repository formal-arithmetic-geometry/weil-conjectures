/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import Sheaf.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Cancelling the restricted homotopy counit comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem cancel_restricted_counit {C : Type*} [Category C]
    {A B D E F G H J : C}
    (a : A ≅ B) (s : A ⟶ D) (e : D ⟶ E) (b : E ≅ F) (t : F ≅ G)
    (d : B ⟶ G) (v : F ⟶ H) (w : E ⟶ J) (b' : J ≅ H)
    (h : s ≫ e ≫ b.hom ≫ t.hom = a.hom ≫ d)
    (hn : w ≫ b'.hom = b.hom ≫ v) :
    a.inv ≫ s ≫ e ≫ w ≫ b'.hom = d ≫ t.inv ≫ v := by
  have h' := congrArg (fun k => a.inv ≫ k ≫ t.inv ≫ v) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] at h'
  rw [hn]
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
-- Preserve the original signature's unused F₀ and a let bindings.
set_option maxHeartbeats 600000 in
-- Comparing the pinned localization factors needs this elaboration budget.
/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).

Proof: Put P = F_h(I), let v be the homotopy tensor adjunction counit at I,
 and write t for the homotopy tensor restriction isomorphism. Apply
 open_pinned_counit_homotopy_restriction to P and the restricted square. Its identity
 input contributes only an identity map, so its left side is S(Qh(P)) followed by
 rX(epsilon_f(P)), the target restriction factorization at the homotopy pullback of
 P, and Qh(t.hom(P)). Its right side is Lf0 of the source restriction factorization
 followed by epsilon_f0(rY_h(P)). Precompose both sides with Lf0 of the inverse
 source restriction factorization, and postcompose both sides with Qh(t.inv(P)).
 Functoriality and the inverse identities cancel the source factorization and the
 pair t.hom, t.inv. Next postcompose with Qh(rX_h(v)). Naturality of the target
 restriction factorization at v identifies its composite with this arrow with
 rX(Qh(v)) followed by the restriction factorization at I. Finally combine the two
 Qh images on the right by functoriality. This gives precisely the asserted
 equality. No derived unit or derived-adjunction counit occurs. All cancellations
 are of isomorphisms, so empty opens and zero complexes require no exceptions. -/
theorem singleComplexOpen_restricted_counit_cancellation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I)) := by
  classical
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition
  let P := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
    (.up ℤ)).obj I
  let v := ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)).counit.app I
  let rY := schemeOpenRestriction Y V
  let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  let t := openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
    (morphismRestrict_ι f V)
  have h := open_pinned_counit_homotopy_restriction.{u, w} f V (f ⁻¹ᵁ V) (f ∣_ V)
    (morphismRestrict_ι f V) P
  have hn := rX.mapDerivedCategoryFactorsh.hom.naturality v
  have h' := cancel_restricted_counit
    ((derivedPullback (f ∣_ V)).mapIso (rY.mapDerivedCategoryFactorsh.app P))
    (singleComplexRestrictedCoefficient f (DerivedCategory.Qh.obj P)
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P)) (𝟙 _) V (f ⁻¹ᵁ V)
      (f ∣_ V) (morphismRestrict_ι f V))
    (rX.mapDerivedCategory.map ((pinnedPullbackCounit.{u, w} f).app P))
    (rX.mapDerivedCategoryFactorsh.app
      (((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P))
    (DerivedCategory.Qh.mapIso (t.app P))
    ((pinnedPullbackCounit.{u, w} (f ∣_ V)).app
      ((rY.mapHomotopyCategory (.up ℤ)).obj P))
    (DerivedCategory.Qh.map ((rX.mapHomotopyCategory (.up ℤ)).map v))
    (rX.mapDerivedCategory.map (DerivedCategory.Qh.map v))
    (rX.mapDerivedCategoryFactorsh.app I) h hn
  simpa only [singleComplexRestrictedCoefficient, singleComplexOpenPinnedComposition,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
    Iso.symm_hom, eqToIso.hom, pinnedPullbackCounit, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc, CategoryTheory.Functor.map_comp] using h'

end AlgebraicGeometry
