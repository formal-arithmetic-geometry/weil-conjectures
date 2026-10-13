/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-!
# Filtered colimits and ordinary module stalks

Source: Stacks Project, Sheaves, Section 009E, item (5), and Modules, Lemma 01AH (2)
(blueprint: lem-weil-pbc-module-stalk-filtered-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

-- Transfer a colimit through a reflective adjunction after applying a functor
-- which inverts the unit at the presheaf colimit object.
private theorem stalk_colimit_of_reflection
    {A B E : Type*} [Category A] [Category B] [Category E]
    {J : Type*} [Category J] {L : A ⥤ B} {U : B ⥤ A}
    (adj : L ⊣ U) [IsIso adj.counit]
    (S : A ⥤ E) (D : J ⥤ B) (c : Cocone D) (hc : IsColimit c)
    (P : Cocone (D ⋙ U)) (hP : IsColimit P)
    [PreservesColimit (D ⋙ U) L]
    (hPS : IsColimit (S.mapCocone P))
    [IsIso (S.map (adj.unit.app P.pt))] :
    Nonempty (IsColimit ((U ⋙ S).mapCocone c)) := by
  let hQ := isColimitOfPreserves L hP
  let e : (D ⋙ U) ⋙ L ≅ D := Functor.isoWhiskerLeft D (asIso adj.counit)
  let hcE := (IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : J) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (D.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (D.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have : IsIso (S.map k) := by
    dsimp only [k]
    rw [S.map_comp]
    infer_instance
  let m : S.mapCocone P ⟶ (U ⋙ S).mapCocone c :=
    { hom := S.map k
      w := fun i ↦ by
        change S.map (P.ι.app i) ≫ S.map k = S.map (U.map (c.ι.app i))
        rw [← S.map_comp, hk] }
  have : IsIso m := Cocone.cocone_iso_of_hom_iso m
  exact ⟨hPS.ofIsoColimit (asIso m)⟩

/-- The stalk maps of a colimit cocone of sheaves of modules exhibit the stalk of the colimit
as the colimit, in modules over the local ring `𝒪_{X,x}`, of the stalks of the diagram. The
stalks and the induced linear stalk maps are those of the module stalk functor
`RingedSpace.moduleStalkFunctor` (`def-weil-pbc-module-stalk`, `def-pc-module-stalk-functor`);
the index category lives in the universe of the modules.
Source: Stacks Project, Sheaves, Section 009E (5), and Modules, Lemma 01AH (2)
(blueprint: lem-weil-pbc-module-stalk-filtered-colimit).

Proof outline:
1. Form a colimit P of the underlying presheaves of modules. Its underlying abelian
   presheaf is a colimit by `lem-weil-pbc-presheaf-modules-colimits-sectionwise`.
   Abelian presheaf stalks preserve colimits: their functor is precomposition followed
   by the colimit functor, both of which preserve colimits.
2. Module sheafification is left adjoint to inclusion, with invertible counit
   (`def-weil-presheaf-modules-sheafification` and
   `lem-weil-pbc-module-presheaf-sheafification-exact`). Thus its image of P is
   isomorphic to the given colimit, compatibly with the coprojections.
3. Compose the unit at P with the inclusion of this isomorphism. Unit naturality
   and the adjunction triangle identity show that this comparison carries each
   presheaf coprojection to the corresponding given sheaf coprojection.
4. The comparison is an isomorphism on abelian stalks because the unit is
   (`lem-weil-pbc-stalk-sheafification-space`). Transport the abelian stalk colimit
   property along the resulting cocone isomorphism.
5. The underlying abelian cocone is definitionally the forgotten module stalk
   cocone (`def-pc-module-stalk-functor`). The forgetful functor from modules to
   abelian groups reflects colimits, so the module stalk cocone is a colimit. -/
theorem module_stalk_filtered_colimit
    (X : Scheme.{u}) (x : X) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ X.Modules) (c : Cocone D) (hc : IsColimit c) :
    Nonempty (IsColimit ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapCocone c)) := by
  classical
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).obj X.sheaf
  let U := SheafOfModules.forget R
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P := colimit.cocone (D ⋙ U)
  let hP := colimit.isColimit (D ⋙ U)
  let S := PresheafOfModules.toPresheaf R.obj ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : PreservesColimit (D ⋙ U) S := by
    dsimp [S, TopCat.Presheaf.stalkFunctor]
    infer_instance
  have hPS : IsColimit (S.mapCocone P) := isColimitOfPreserves S hP
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  have : IsIso (S.map (adj.unit.app P.pt)) := by
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf R.obj).map (adj.unit.app P.pt)))
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.pt.presheaf))
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.pt.presheaf
  obtain ⟨h⟩ := stalk_colimit_of_reflection adj S D c hc P hP hPS
  let V := forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have h' : IsColimit (V.mapCocone
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapCocone c)) := by
    exact h
  exact ⟨isColimitOfReflects V h'⟩

end AlgebraicGeometry.Scheme.Modules
