/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapLocal
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.Topology.PresheafModuleStalkFunctor
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Degreewise local representatives before taking a finite common intersection. -/
theorem exists_local_degreewise_of_stalk_local
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y)
    (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n) :
    ∀ n : ℤ, ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n := by
  intro n
  rcases hPfree n with hP | ⟨r, ⟨eP⟩⟩
  · refine ⟨⊤, trivial, 0, ?_⟩
    have ht : t n = 0 := ((Modules.pullback (Y.fromSpecStalk y)).map_isZero hP).eq_of_src _ _
    simp [ht]
  · rcases hQfree n with hQ | ⟨s, ⟨eQ⟩⟩
    · refine ⟨⊤, trivial, 0, ?_⟩
      have ht : t n = 0 := ((Modules.pullback (Y.fromSpecStalk y)).map_isZero hQ).eq_of_tgt _ _
      simp [ht]
    · let F := Modules.pullback (Y.fromSpecStalk y)
      obtain ⟨U, hyU, g, hg⟩ := exists_local_free_stalk_map r s y
        (F.map eP.inv ≫ t n ≫ F.map eQ.hom)
      let R := restrictFunctor U.ι
      let G := Modules.pullback (U.fromSpecStalkOfMem y hyU)
      let E := Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) G ≪≫
        pullbackComp (U.fromSpecStalkOfMem y hyU) U.ι ≪≫
        pullbackCongr (U.fromSpecStalkOfMem_ι y hyU)
      refine ⟨U, hyU, R.map eP.hom ≫ g ≫ R.map eQ.inv, ?_⟩
      change G.map (R.map eP.hom ≫ g ≫ R.map eQ.inv) =
        E.hom.app (P.X n) ≫ t n ≫ E.inv.app (Q.X n)
      change G.map g = E.hom.app _ ≫ (F.map eP.inv ≫ t n ≫ F.map eQ.hom) ≫
        E.inv.app _ at hg
      simp only [Functor.map_comp, hg, Category.assoc]
      erw [E.hom.naturality_assoc eP.hom]
      erw [← E.inv.naturality eQ.inv]
      simp [F, ← Functor.map_comp]

end AlgebraicGeometry.Scheme.Modules
