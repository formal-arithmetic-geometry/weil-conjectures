/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison
import WeilConjectures.AlgebraicGeometry.OpenStalkRestrictionTransport
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkRetractHomEquality
import Mathlib.Data.Int.Interval
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Killing the differential defects of a degreewise family

Source: Stacks Project, Tags 09RE and 01CP.
(blueprint: lem-sc-perfect-open-stalk-degreewise-shrink).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private def restriction_comp_iso (X : Scheme.{u}) (V Z W : X.Opens)
    (hZV : Z ≤ V) (hWZ : W ≤ Z) :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hZV)) ⋙
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWZ)) ≅
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hWZ.trans hZV)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private theorem restrict_eq_of_le (X : Scheme.{u}) {Z W T : X.Opens}
    (hWZ : W ≤ Z) (hTW : T ≤ W)
    {M N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Z)}
    (a b : M ⟶ N)
    (heq : (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map a =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map b) :
    (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (hTW.trans hWZ))).map a =
    (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (hTW.trans hWZ))).map b := by
  let e := restriction_comp_iso X Z W T hWZ hTW
  apply (cancel_mono (e.inv.app N)).1
  rw [e.inv.naturality a, e.inv.naturality b]
  exact congrArg (fun k ↦ e.inv.app M ≫
    (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hTW)).map k) heq

private theorem conjugate_map
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    (R : C₀ ⥤ C₁) (S : C₁ ⥤ C₂) (T : C₀ ⥤ C₂) (c : R ⋙ S ≅ T)
    {M N : C₀} {M' N' : C₁} (i : M' ≅ R.obj M) (j : N' ≅ R.obj N)
    (f : M ⟶ N) {M'' N'' : C₂} (p : T.obj M ≅ M'') (q : T.obj N ≅ N'') :
    S.map (i.hom ≫ R.map f ≫ j.inv) =
      (S.map i.hom ≫ c.hom.app M ≫ p.hom) ≫ p.inv ≫ T.map f ≫ q.hom ≫
        (q.inv ≫ c.inv.app N ≫ S.map j.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← c.hom.naturality_assoc,
    ← Category.assoc (c.hom.app N) (c.inv.app N), c.hom_inv_id_app, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option profiler true in
/-- A degreewise family already defined near x becomes a chain map after shrinking
if its stalk commutes with the differentials. The second conclusion records the
stalks of the restricted components in the original comparison coordinates.

Source: Stacks Project, Tag 09RE, finite-presentation shrinking calculation, and
Tag 01CP, injectivity of the internal-Hom stalk comparison.
(blueprint: lem-sc-perfect-open-stalk-degreewise-shrink).

Proof: For each adjacent degree form the difference of g n followed by d_Q and
of d_P followed by g (n+1). The hypothesis says its stalk is zero. Finite
presentation of P.X n and injectivity of the internal-Hom stalk comparison say
that this is a zero germ of a local morphism. The germ equality criterion gives
a neighbourhood on which that morphism vanishes. Only degrees n in the bounded
support interval of P need checking; outside it the source P.X n is zero.
Intersect these finitely many neighbourhoods inside W and choose an affine V
containing x. Restrict the family to V, using transitivity of overMap to regard
its components as maps between the direct restrictions from U. This gives k
and all adjacent chain equations. A comparison between the V stalk and the W stalk
after restriction, transported by `exists_openStalk_restriction_transport`, composes
with e to the canonical comparison eV. Naturality and
restriction transitivity give the displayed conjugation formula for k. The
comparison is natural for every complex, not just P and Q. With an empty support
interval or rank zero the corresponding equations and maps are unique. This
lemma extends no prescribed map: it starts with a family already defined on W.
No perfectness hypothesis on Q is needed. -/
theorem exists_affine_perfect_open_stalk_degreewise_shrink
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U)
    (g : ∀ n : ℤ,
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q).X n)
    (hcomm : ∀ n : ℤ,
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
        (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
          (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q)).d n (n + 1) =
      (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)).d n (n + 1) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g (n + 1))) :
    let e : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ) ⋙
        (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ) ≅
        (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ) :=
      Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) (.up ℤ)
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (_hVW : V ≤ W) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      let eV : R ⋙ S ≅ T := Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      ∃ k : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n,
        (∀ n : ℤ, k n ≫ (R.obj Q).d n (n + 1) =
          (R.obj P).d n (n + 1) ≫ k (n + 1)) ∧
        (∀ n : ℤ, (openModuleStalkFunctor X V ⟨x, hxV⟩).map (k n) =
          (eV.app P).hom.f n ≫ (e.app P).inv.f n ≫
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
              (e.app Q).hom.f n ≫ (eV.app Q).inv.f n) := by
  classical
  intro e
  let A := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU)
  let R := A.mapHomologicalComplex (.up ℤ)
  let f := fun n : ℤ ↦ g n ≫ (R.obj Q).d n (n + 1)
  let t := fun n : ℤ ↦ (R.obj P).d n (n + 1) ≫ g (n + 1)
  have hn (n : ℤ) : ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map (f n) =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map (t n) := by
    apply exists_open_stalk_retract_hom_eq X U W hWU (P.X n) (hP.2 n)
      (A.obj (Q.X (n + 1))) x hxW (f n) (t n)
    simpa only [f, t, R, A, Functor.map_comp, Functor.mapHomologicalComplex_obj_d]
      using hcomm n
  have hs (s : Finset ℤ) : ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
      ∀ n ∈ s,
        (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map (f n) =
        (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map (t n) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨W, le_rfl, hxW, by simp⟩
    | @insert n s hns ih =>
      obtain ⟨V, hVW, hxV, hV⟩ := ih
      obtain ⟨Z, hZW, hxZ, hZ⟩ := hn n
      refine ⟨V ⊓ Z, inf_le_left.trans hVW, ⟨hxV, hxZ⟩, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact restrict_eq_of_le X hZW inf_le_right (f i) (t i) hZ
      · exact restrict_eq_of_le X hVW inf_le_left (f i) (t i) (hV i hi)
  obtain ⟨a, b, hsupport⟩ := hP.1
  obtain ⟨Z, hZW, hxZ, hZ⟩ := hs (Finset.Icc a b)
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset hxZ
  let hVW := hVZ.trans hZW
  let hVU := hVW.trans hWU
  let B := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVW)
  -- Restriction is strictly compatible with composition, degree by degree.
  let k := fun n : ℤ ↦ B.map (g n)
  refine ⟨V, hxV, hV, hVW, hVU, k, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ Finset.Icc a b
    · have heq := restrict_eq_of_le X hZW hVZ (f n) (t n) (hZ n hn)
      change B.map (g n) ≫ B.map (A.map (Q.d n (n + 1))) =
        B.map (A.map (P.d n (n + 1))) ≫ B.map (g (n + 1))
      exact (B.map_comp _ _).symm.trans (heq.trans (B.map_comp _ _))
    · have hz : IsZero (P.X n) := hsupport n (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        exact hn)
      exact ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hVU)).map_isZero hz).eq_of_src _ _
  · intro n
    obtain ⟨c₀, c, hc₀, hc⟩ := exists_openStalk_restriction_transport X U x hxU W hxW hWU
      (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) V hxV hVW hVU
    let eW := openModuleStalkRestrictionComparison X U W hWU x hxU hxW
    let eV := openModuleStalkRestrictionComparison X U V hVU x hxU hxV
    have he (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
        eV.hom.app M = c.hom.app (A.obj M) ≫ eW.hom.app M := by
      have h := hc M
      rw [hc₀] at h
      simpa only [Functor.map_id, Category.id_comp] using h
    change (openModuleStalkFunctor X V ⟨x, hxV⟩).map (B.map (g n)) =
      eV.hom.app (P.X n) ≫ eW.inv.app (P.X n) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
          eW.hom.app (Q.X n) ≫ eV.inv.app (Q.X n)
    apply (cancel_mono (eV.hom.app (Q.X n))).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [he (P.X n), he (Q.X n)]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    exact (c.hom.naturality_assoc (g n) (eW.hom.app (Q.X n)))

end
end AlgebraicGeometry.Scheme
