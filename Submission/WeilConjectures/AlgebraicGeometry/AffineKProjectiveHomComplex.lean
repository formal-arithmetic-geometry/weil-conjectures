/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Submission.WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Submission.WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import Submission.WeilConjectures.Algebra.Homology.ModuleHomComplexQuotient
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Linear.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Affine K-projective Hom-complex representatives

Source: Stacks Project, Tag 06Z0; Mathlib's K-projectivity and Hom-complex quotient.
(blueprint: lem-sc-affine-kprojective-hom-complex).
-/

@[expose] public section

universe u w v
open CategoryTheory
namespace AlgebraicGeometry

private theorem affineTilde_map_bijective (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    ∃ F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)),
      F.Full ∧ F.Faithful ∧ F.Additive ∧
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (koszulOpenTilde A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  obtain ⟨e, ⟨h⟩, _, ⟨hs, ht⟩⟩ := exists_affineQCohDerivedEquivalence_core A
  let := hs
  let := ht
  refine ⟨e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι,
    inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨h⟩

set_option maxHeartbeats 1500000 in
-- Elaborating the three additive equivalences crosses two derived-category universes.
set_option backward.isDefEq.respectTransparency false in
/-- For any module target complex, affine derived arrows out of a K-projective module
complex are its linear Hom-complex cohomology, with chain representatives and naturality.
Source: Stacks Project, Tag 06Z0; Mathlib HomComplexCohomology and KProjective.
(blueprint: lem-sc-affine-kprojective-hom-complex)

Proof: The core affine derived equivalence identifies the derived tilde Hom group
with the corresponding module derived Hom group, through its termwise tilde comparison.
For a K-projective source localization identifies this with homotopy classes of chain
maps. Degree-zero Hom cycles are chain maps and boundaries are null-homotopic maps,
so the quotient is degree-zero homology of the module-valued Hom complex. All three
identifications are additive. Precomposition by a chain map is precomposition on cycles,
and the stated formula for t gives exactly that map on the quotient. Every quotient
class has a cycle representative, which is a chain map g; this gives z and both displayed
identities. There is no boundedness hypothesis on the target M. The zero source, zero
ring and zero target give the same quotient and unique zero representative. -/
theorem affineKProjective_homComplex (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    let T := (koszulOpenTilde A).mapHomologicalComplex (.up ℤ)
    ∃ a : ∀ (L : CochainComplex (ModuleCat.{u} A) ℤ) (_hL : L.IsKProjective),
        (DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M)) ≃+
          (CochainComplex.moduleHomComplex L M).homology 0,
      (∀ (L L' : CochainComplex (ModuleCat.{u} A) ℤ)
        (hL : L.IsKProjective) (hL' : L'.IsKProjective) (g : L' ⟶ L)
        (t : CochainComplex.moduleHomComplex L M ⟶ CochainComplex.moduleHomComplex L' M),
        (∀ (n : ℤ) (z : CochainComplex.HomComplex.Cochain L M n),
          (t.f n) z = (CochainComplex.HomComplex.Cochain.ofHom g).comp z (zero_add n)) →
        ∀ φ : DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M),
          a L' hL' (DerivedCategory.Q.map (T.map g) ≫ φ) =
            HomologicalComplex.homologyMap t 0 (a L hL φ)) ∧
      ∀ (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.IsKProjective)
        (φ : DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M)),
        ∃ (g : L ⟶ M) (z : (CochainComplex.moduleHomComplex L M).cycles 0),
          DerivedCategory.Q.map (T.map g) = φ ∧
          (CochainComplex.moduleHomComplex L M).iCycles 0 z =
            CochainComplex.HomComplex.Cochain.ofHom g ∧
          a L hL φ = (CochainComplex.moduleHomComplex L M).homologyπ 0 z := by
  classical
  dsimp only
  let T := (koszulOpenTilde A).mapHomologicalComplex (.up ℤ)
  obtain ⟨F, hfull, hfaith, hadd, ⟨η⟩⟩ := affineTilde_map_bijective A
  let := hfull
  let := hfaith
  let := hadd
  let H := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let c (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.IsKProjective) :
      (H.obj L ⟶ H.obj M) ≃+
        (DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M)) :=
    let := hL
    (AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (CochainComplex.IsKProjective.Qh_map_bijective L (H.obj M))).trans
      (((Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso _).app L)
        ((DerivedCategory.quotientCompQhIso _).app M)).toAddEquiv).trans
      ((AddEquiv.ofBijective (F.mapAddHom) ⟨F.map_injective, F.map_surjective⟩).trans
        (Linear.homCongr ℤ (η.app L) (η.app M)).toAddEquiv))
  have hc (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.IsKProjective)
      (f : L ⟶ M) : c L hL (H.map f) = DerivedCategory.Q.map (T.map f) := by
    change ((η.app L).inv ≫ F.map
      (((DerivedCategory.quotientCompQhIso _).inv.app L ≫
        DerivedCategory.Qh.map (H.map f)) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app M)) ≫ (η.app M).hom = _
    simp only [Category.assoc]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality,
      Iso.inv_hom_id_app_assoc]
    have hn := η.hom.naturality f
    change F.map (DerivedCategory.Q.map f) ≫ (η.app M).hom =
      (η.app L).hom ≫ DerivedCategory.Q.map (T.map f) at hn
    rw [hn, Iso.inv_hom_id_assoc]
  obtain ⟨b, hb⟩ := CochainComplex.moduleHomComplex_quotient A
  let a (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.IsKProjective) :=
    (c L hL).symm.trans (b L M)
  have hrep (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.IsKProjective)
      (φ : DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M)) :
      ∃ (f : L ⟶ M) (z : (CochainComplex.moduleHomComplex L M).cycles 0),
        DerivedCategory.Q.map (T.map f) = φ ∧
        (CochainComplex.moduleHomComplex L M).iCycles 0 z =
          CochainComplex.HomComplex.Cochain.ofHom f ∧
        a L hL φ = (CochainComplex.moduleHomComplex L M).homologyπ 0 z := by
    obtain ⟨f, hf⟩ := H.map_surjective ((c L hL).symm φ)
    obtain ⟨z, hz, hbz⟩ := hb L M f
    refine ⟨f, z, ?_, hz, ?_⟩
    · rw [← hc L hL f, hf, AddEquiv.apply_symm_apply]
    · change b L M ((c L hL).symm φ) = _
      rw [← hf, hbz]
  refine ⟨a, ?_, hrep⟩
  intro L L' hL hL' g t ht φ
  obtain ⟨f, z, rfl, hz, haz⟩ := hrep L hL φ
  obtain ⟨z', hz', hbz'⟩ := hb L' M (g ≫ f)
  have ha' : a L' hL' (DerivedCategory.Q.map (T.map (g ≫ f))) =
      (CochainComplex.moduleHomComplex L' M).homologyπ 0 z' := by
    change b L' M ((c L' hL').symm _) = _
    rw [← hc L' hL' (g ≫ f), AddEquiv.symm_apply_apply, hbz']
  have hcycles : HomologicalComplex.cyclesMap t 0 z = z' := by
    apply (ModuleCat.mono_iff_injective
      ((CochainComplex.moduleHomComplex L' M).iCycles 0)).mp inferInstance
    have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t 0) z
    dsimp at hi
    rw [hi, ht, hz, ← CochainComplex.HomComplex.Cochain.ofHom_comp, hz']
  rw [← Functor.map_comp, ← Functor.map_comp, ha', haz]
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t 0) z
  dsimp at hπ
  rw [hπ, hcycles]

end AlgebraicGeometry
