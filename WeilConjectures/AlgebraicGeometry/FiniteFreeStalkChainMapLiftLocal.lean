/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkDegreewiseLift
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkDegreewiseShrink

/-! # Finite matrix extension to one neighbourhood
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite matrix extension to one neighbourhood. -/
theorem exists_chainMap_of_stalk_local
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y)
    (f : ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P ⟶
      ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (fU :
      ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q),
      let S := (Modules.pullback (U.fromSpecStalkOfMem y ‹y ∈ U›)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let eP := (stalkRestrictionComplexIso U y ‹y ∈ U›).app P
      let eQ := (stalkRestrictionComplexIso U y ‹y ∈ U›).app Q
      S.map fU = eP.hom ≫ f ≫ eQ.inv := by
  obtain ⟨U, hyU, g, hg⟩ := exists_degreewise_of_stalk_local
    P Q a b c e hPa hPb hQc hQe hPfree hQfree y f.f
  let SU := (Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let RU := (restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)
  let eP := (stalkRestrictionComplexIso U y hyU).app P
  let eQ := (stalkRestrictionComplexIso U y hyU).app Q
  have hcomm (n : ℤ) :
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g n) ≫
        (SU.obj (RU.obj Q)).d n (n + 1) =
      (SU.obj (RU.obj P)).d n (n + 1) ≫
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g (n + 1)) := by
    rw [hg n, hg (n + 1)]
    change (eP.hom ≫ f ≫ eQ.inv).f n ≫ (SU.obj (RU.obj Q)).d n (n + 1) =
      (SU.obj (RU.obj P)).d n (n + 1) ≫ (eP.hom ≫ f ≫ eQ.inv).f (n + 1)
    exact (eP.hom ≫ f ≫ eQ.inv).comm n (n + 1)
  obtain ⟨V, hyV, _, k, hk, hkg⟩ := exists_shrink_degreewise_comm_of_stalk
    P Q a b c e hPa hPb hQc hQe hPfree hQfree y U hyU g hcomm
  let fV := CochainComplex.ofHom k hk
  refine ⟨V, hyV, fV, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  change (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (k n) = _
  rw [hkg n, hg n]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have hP : eP.inv.f n ≫ eP.hom.f n = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun t ↦ t.f n) eP.inv_hom_id
  have hQ : eQ.inv.f n ≫ eQ.hom.f n = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun t ↦ t.f n) eQ.inv_hom_id
  change ((stalkRestrictionComplexIso U y hyU).app P).inv.f n ≫
    ((stalkRestrictionComplexIso U y hyU).app P).hom.f n = 𝟙 _ at hP
  change ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n ≫
    ((stalkRestrictionComplexIso U y hyU).app Q).hom.f n = 𝟙 _ at hQ
  simp only [← Category.assoc, hP, hQ, Category.id_comp]
end AlgebraicGeometry.Scheme.Modules
