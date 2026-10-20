/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology
import WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproduct
import Sheaf.Paper.HigherDirectImagePresheaf
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian

/-! # Direct images of an external tensor product with an acyclic first factor

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, acyclic base case.
(blueprint: lem-sc-picard-external-coefficients-direct-images).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private theorem isZero_higherDirectImage_of_affine_local
    {X Y : Scheme.{w}} (f : X ⟶ Y) (F : X.Modules) (q : ℕ)
    (h : ∀ V : Y.Opens, IsAffineOpen V →
      IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace q (f ⁻¹ᵁ V)).obj F)) :
    IsZero (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).Additive :=
    RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  let I := injectiveResolution F
  let K : CochainComplex Y.Modules ℕ :=
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  have hP (V : Y.Opens) (hV : IsAffineOpen V) :
      IsZero (P.presheaf.obj (Opposite.op V)) := by
    let L := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op V)
    let : (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive :=
      RingedSpace.openModuleSections_additive _ _
    let e := I.isoRightDerivedObj
      (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) q
    exact (h V hV).of_iso (((L.sc q).mapHomologyIso E).symm ≪≫ e.symm)
  have hstalk (x : Y) :
      IsZero ((PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj x).obj P) := by
    suffices hs : Subsingleton
        ((PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj x).obj P) from
      @ModuleCat.isZero_of_subsingleton _ _ _ hs
    refine ⟨fun a b ↦ ?_⟩
    have hz (a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{w})
        (X := Y.toTopCat) P.presheaf x) : a = 0 := by
      obtain ⟨V, hxV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := Y.toTopCat) P.presheaf a
      obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
      have : Subsingleton (P.presheaf.obj (Opposite.op W)) :=
        AddCommGrpCat.subsingleton_of_isZero (hP W hW)
      rw [← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE hWV) x hxW a]
      have ha : P.presheaf.map (homOfLE hWV).op a = 0 := Subsingleton.elim _ _
      exact (congrArg (TopCat.Presheaf.germ P.presheaf W x hxW) ha).trans (map_zero _)
    exact (hz a).trans (hz b).symm
  let D := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F
  let A := SheafOfModules.toSheaf Y.ringCatSheaf
  suffices hA : IsZero (A.obj D) from
    (IsZero.iff_id_eq_zero D).mpr (A.map_injective (hA.eq_of_src _ _))
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (A.obj D)).mpr
  intro x
  have hi := (higherDirectImagePresheaf f F I q).2.2.1 x
  let τ := (PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj x).map
    (sectionCohomologyTheta K q ≫
      (SheafOfModules.forget Y.ringCatSheaf).map
        (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) q).inv)
  have : IsIso τ := hi
  have hs := ModuleCat.subsingleton_of_isZero ((hstalk x).of_iso (asIso τ).symm)
  exact @AddCommGrpCat.isZero_of_subsingleton _ hs

/-- The positive direct images of the external coefficients vanish, and the zeroth
is a coproduct of copies of the second coefficient. No acyclicity of G is assumed.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the paragraph beginning
"Let V be an affine open" and the displayed derived-direct-image formula.
(blueprint: lem-sc-picard-external-coefficients-direct-images).

Proof: Choose a finite affine cover U of the quasi-compact X. Affine diagonal ensures
that every nonempty finite intersection of its members is affine. On each affine open
V of Y, cover X times V by the products U_i times V. The affine fibre-product formula,
pullback-section comparison and tensor-section comparison identify its Cech complex
with Cech(U,F) tensor_k G(V), naturally under restriction of V. Finite products commute
with field tensor. Affine Cech comparison identifies its cohomology with H^p(X,F)
tensor_k G(V), since tensor over a field is exact. Hence its positive cohomology is
zero, while degree zero is Gamma(X,F) tensor_k G(V). The higher-direct-image presheaf
comparison sheafifies these compatible calculations to identify R^q pr2_* E with zero
for q>0, and R^0 pr2_* E with Gamma(X,F) tensor_k G. Choose a vector-space basis of
Gamma(X,F), indexed by a type I in universe w. The vector-space direct-sum decomposition,
tensored with G and sheafified, gives maps from G into R^0 pr2_* E which exhibit it as
the coproduct indexed by I. This is a universal property, not equality of presheaf
sections with an infinite direct sum: sheafification is needed. If Gamma(X,F) is zero,
I is empty and the coproduct is the zero sheaf. Empty schemes and G=0 are included.
The existential witnesses are used only in propositions, never to define an object. -/
theorem picardExternalCupCoefficients_directImages
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)) :
    (∀ q : ℕ, 0 < q →
      IsZero (((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerived q).obj
          (externalCupCoefficients f g F G))) ∧
    ∃ (I : Type w)
      (ι : ∀ _ : I, G ⟶ ((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerived 0).obj
          (externalCupCoefficients f g F G)),
      Nonempty (IsColimit (Cofan.mk _ ι)) := by
  constructor
  · intro q hq
    apply isZero_higherDirectImage_of_affine_local
    intro V hV
    obtain ⟨e⟩ := picardExternalCupCoefficients_affine_local_cohomology k X Y f g F G V hV q
    let : Subsingleton (scalarCohomology f F q) := by
      change Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
      exact ModuleCat.subsingleton_of_isZero (hF q hq)
    have hz (t : scalarCohomology f F q ⊗[k]
        scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤)) : t = 0 := by
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b =>
        have ha : a = 0 := Subsingleton.elim _ _
        simp only [ha, TensorProduct.zero_tmul]
      | add a b ha hb => simp only [ha, hb, add_zero]
    let : Subsingleton (scalarCohomology f F q ⊗[k]
        scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤)) :=
      ⟨fun a b ↦ (hz a).trans (hz b).symm⟩
    exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso e
  · obtain ⟨I, ι, ⟨hc⟩⟩ :=
      picardExternalCupCoefficients_pushforward_coproduct k X Y f g F G
    let P := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
    let E := externalCupCoefficients f g F G
    let : EnoughInjectives (Limits.pullback f g).Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives
        (Limits.pullback f g).toRingedSpace).2
    have : IsIso (P.toRightDerivedZero.app E) :=
      (higherDirectImagePresheaf (pullback.snd f g) E (injectiveResolution E) 0).2.2.2.2
    let e := asIso (P.toRightDerivedZero.app E)
    refine ⟨I, fun i ↦ ι i ≫ e.hom, ⟨?_⟩⟩
    exact hc.ofIsoColimit (Cofan.ext e (fun i ↦ rfl))


end AlgebraicGeometry.Scheme.Modules
