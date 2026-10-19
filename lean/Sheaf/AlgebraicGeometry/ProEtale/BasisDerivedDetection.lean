/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Derived sections on the affine ind-etale basis detect isomorphisms

Source: Weil conjectures blueprint, `lem-weil-pbc-basis-derived-detection`, order 1288
(blueprint: lem-weil-pbc-basis-derived-detection).

Second reading by NI: the statement and constructions match the node exactly.

The small model `AsSmall` changes neither the objects nor the covering families:
its equivalence transports the given small pro-etale topology. Constant rings,
module sheaves and derived categories below use the recorded Mathlib definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The recorded constant ring sheaf transported to this small presentation along
Mathlib's canonical site equivalence; this reuses `Scheme.proEtaleConstantRing`.
Source: blueprint, order 1288, coefficient convention
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable abbrev smallConstantRing (X : Scheme.{u}) (R : Type u) [CommRing R] :
    Sheaf (proEtaleModelTopology X) RingCat.{u + 1} :=
  ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X R))

/-- Module sheaves on the chosen small presentation of the small pro-etale site.
Source: blueprint, order 1288, the category A
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable abbrev smallModules (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  ringedSiteModules.{u + 1} (smallConstantRing X R)

/-- The usual injective-existence instance for module sheaves on the chosen small site.
Source: Stacks, Section 07A5; blueprint, order 1288, proof step 1
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable instance smallModulesEnoughInjectives (X : Scheme.{u})
    (R : Type u) [CommRing R] : EnoughInjectives (smallModules X R) :=
  @IsGrothendieckAbelian.enoughInjectives _ _ _
    (SheafOfModules.isGrothendieckAbelian (smallConstantRing X R))

/-- The standard localization model of the bounded-below derived category.
Source: blueprint, order 1288, D+(A)
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable abbrev smallDerivedPlus (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  @DerivedCategory.Plus (smallModules X R) _ _ (HasDerivedCategory.standard _)

/-- Derived evaluation at a pro-etale object, computed by bounded-below injectives.
Source: blueprint, order 1288, definition of RΓ(W,-)
(blueprint: lem-weil-pbc-basis-derived-detection).
This is Mathlib's right derived functor, not a choice of an arbitrary comparison functor. -/
noncomputable def smallDerivedEvaluation (X : Scheme.{u}) (R : Type u) [CommRing R]
    (W : X.ProEt) :
    smallDerivedPlus X R ⥤
      @DerivedCategory.Plus
        (ModuleCat.{u + 1} ((smallConstantRing X R).obj.obj (op (AsSmall.up.obj W))))
        _ _ (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard (smallModules X R)
  letI := HasDerivedCategory.standard
    (ModuleCat.{u + 1} ((smallConstantRing X R).obj.obj (op (AsSmall.up.obj W))))
  letI : (SheafOfModules.evaluation (smallConstantRing X R)
      (op (AsSmall.up.obj W))).Additive :=
    inferInstanceAs ((SheafOfModules.forget (smallConstantRing X R) ⋙
      PresheafOfModules.evaluation (smallConstantRing X R).obj
        (op (AsSmall.up.obj W))).Additive)
  (SheafOfModules.evaluation (smallConstantRing X R)
    (op (AsSmall.up.obj W))).rightDerivedFunctorPlus

set_option backward.isDefEq.respectTransparency false in
/-- Exact abelian sheafification commutes with homology. The sheafification counit
identifies the sheafified underlying complex with the underlying sheaf complex.
Source: Stacks, Tag 0BKV, the kernel-image calculation; blueprint order 1288, step 4.
(blueprint: lem-weil-pbc-basis-derived-detection). -/
private noncomputable def sheafifiedHomologyIso (X : Scheme.{u}) (R : Type u)
    [CommRing R] (n : ℤ) :
    (SheafOfModules.toSheaf (smallConstantRing X R) ⋙
        sheafToPresheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) n ⋙
          presheafToSheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1} ≅
    HomologicalComplex.homologyFunctor (smallModules X R) (.up ℤ) n ⋙
      SheafOfModules.toSheaf (smallConstantRing X R) := by
  let T := SheafOfModules.toSheaf (smallConstantRing X R)
  let U := sheafToPresheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}
  let S := presheafToSheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}
  let e : (T ⋙ U) ⋙ S ≅ T :=
    Functor.associator T U S ≪≫
      Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction _ _).counit) ≪≫
        T.rightUnitor
  exact Functor.isoWhiskerLeft ((T ⋙ U).mapHomologicalComplex (.up ℤ))
      (S.mapHomologicalComplexHomologyIso (.up ℤ) n).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ))
      (HomologicalComplex.homologyFunctor _ (.up ℤ) n) ≪≫
    T.mapHomologicalComplexHomologyIso (.up ℤ) n

set_option backward.isDefEq.respectTransparency false in
/-- A chain map that is a quasi-isomorphism after evaluation on the affine basis is
already a quasi-isomorphism of module sheaves. Presheaf homology maps become invertible
on the basis; dense-subsite restriction and exact sheafification detect the claim.
Source: blueprint order 1288, steps 4 and 5; Stacks, Tag 0BKV.
(blueprint: lem-weil-pbc-basis-derived-detection). -/
private theorem quasiIso_of_basis_evaluation (X : Scheme.{u}) [IsAffine X]
    (R : Type u) [CommRing R] {I J : CochainComplex (smallModules X R) ℤ}
    (a : I ⟶ J)
    (ha : ∀ W : X.AffineProEt,
      QuasiIso (((SheafOfModules.evaluation (smallConstantRing X R)
        (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W)))).mapHomologicalComplex
          (.up ℤ)).map a)) : QuasiIso a := by
  have : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  have : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsDenseSubsite
      (topology X) (proEtaleModelTopology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsDenseSubsite
      (topology X) ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
        (topology X)))
  let T := SheafOfModules.toSheaf (smallConstantRing X R)
  let U := sheafToPresheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}
  let P := T ⋙ U
  let S := presheafToSheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology a T).mp
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (NatIso.isIso_map_iff (T.mapHomologicalComplexHomologyIso (.up ℤ) n) a).mpr
  apply (NatIso.isIso_map_iff (sheafifiedHomologyIso X R n) a).mp
  let g := (HomologicalComplex.homologyFunctor _ (.up ℤ) n).map
    ((P.mapHomologicalComplex (.up ℤ)).map a)
  change IsIso (S.map g)
  apply ((proEtaleModelTopology X).W_iff g).mp
  apply ((proEtaleModelTopology X).W_whiskerLeft_iff
    (topology X) (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X) g).mp
  apply ((topology X).W_whiskerLeft_iff
    (AffineProEt.topology X) (AffineProEt.toProEt X) _).mp
  have hg : IsIso (Functor.whiskerLeft (AffineProEt.toProEt X).op
      (Functor.whiskerLeft AsSmall.up.op g)) := by
    have (W : X.AffineProEtᵒᵖ) : IsIso
        ((Functor.whiskerLeft (AffineProEt.toProEt X).op
          (Functor.whiskerLeft AsSmall.up.op g)).app W) := by
      let E := (CategoryTheory.evaluation (proEtaleSiteModel X)ᵒᵖ
        AddCommGrpCat.{u + 1}).obj (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W.unop)))
      have hq := ha W.unop
      let M := ModuleCat.{u + 1}
        ((smallConstantRing X R).obj.obj (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W.unop))))
      have : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map
          ((P.mapHomologicalComplex (.up ℤ)).map a)) := by
        change QuasiIso (((forget₂ M AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (((SheafOfModules.evaluation (smallConstantRing X R)
            (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W.unop)))).mapHomologicalComplex
              (.up ℤ)).map a))
        infer_instance
      exact (NatIso.isIso_map_iff (E.mapHomologicalComplexHomologyIso (.up ℤ) n)
        ((P.mapHomologicalComplex (.up ℤ)).map a)).mp (by
          change IsIso (HomologicalComplex.homologyMap
            ((E.mapHomologicalComplex (.up ℤ)).map
              ((P.mapHomologicalComplex (.up ℤ)).map a)) n)
          infer_instance)
    exact NatIso.isIso_of_isIso_app _
  exact (AffineProEt.topology X).W_of_isLocallyBijective _

set_option backward.isDefEq.respectTransparency false in
/-- Derived evaluation on every affine ind-etale basis object detects an isomorphism.
Source: Weil conjectures blueprint, order 1288
(blueprint: lem-weil-pbc-basis-derived-detection).

Proof:
1. Represent the source and target by bounded-below injective complexes. K-injectivity
   lifts the conjugate of the given morphism to a homotopy class, then to a chain map.
2. The right-derived-functor unit is invertible on these injective complexes. Its
   naturality and the hypothesis imply that evaluating the chain map at any basis
   object gives a quasi-isomorphism.
3. Forget the module action and take homology in abelian presheaves. Exact abelian
   sheafification commutes with homology, and its counit identifies the sheafification
   of the original complex with its underlying complex of abelian sheaves. Thus
   sheafification of presheaf homology is the underlying sheaf of module homology.
4. The presheaf homology map is an isomorphism on the affine basis, by step 2 and
   exactness of evaluation on presheaves. Dense-subsite restriction detects morphisms
   inverted by sheafification, both for the affine basis and for the small-site model.
   Step 3 makes the module homology maps isomorphisms, since forgetting the action
   reflects isomorphisms. Hence the chain map is a quasi-isomorphism.
5. Localization inverts this quasi-isomorphism; conjugating back proves the claim.
-/
theorem isIso_of_isIso_basis_derivedEvaluation (X : Scheme.{u}) [IsAffine X]
    (R : Type u) [CommRing R] {K L : smallDerivedPlus X R} (f : K ⟶ L)
    (h : ∀ W : X.AffineProEt,
      IsIso ((smallDerivedEvaluation X R ((AffineProEt.toProEt X).obj W)).map f)) :
    IsIso f := by
  let A := smallModules X R
  let := HasDerivedCategory.standard A
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (K.isGE_ι_obj_iff n).mp hn
  obtain ⟨m, hm⟩ := L.property
  have : L.IsGE m := (L.isGE_ι_obj_iff m).mp hm
  obtain ⟨I, _, ⟨eI⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  obtain ⟨J, _, ⟨eJ⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso L m
  let I' := (InjectiveObject.ι A).mapCochainComplexPlus.obj I
  let J' := (InjectiveObject.ι A).mapCochainComplexPlus.obj J
  let q := HomotopyCategory.Plus.quotient A
  obtain ⟨b, hb⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    (q.obj I') (q.obj J') (by
      change CochainComplex.IsKInjective
        (((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj J.obj)
      infer_instance)).surjective (eI.hom ≫ f ≫ eJ.inv)
  obtain ⟨a, rfl⟩ := q.map_surjective b
  have hqa : ∀ W : X.AffineProEt,
      QuasiIso (((SheafOfModules.evaluation (smallConstantRing X R)
        (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W)))).mapHomologicalComplex
          (.up ℤ)).map a.hom) := by
    intro W
    let E := SheafOfModules.evaluation (smallConstantRing X R)
      (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W)))
    let M := ModuleCat.{u + 1}
      ((smallConstantRing X R).obj.obj (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W))))
    let := HasDerivedCategory.standard M
    have : E.Additive := inferInstanceAs ((SheafOfModules.forget (smallConstantRing X R) ⋙
      PresheafOfModules.evaluation (smallConstantRing X R).obj
        (op (AsSmall.up.obj ((AffineProEt.toProEt X).obj W)))).Additive)
    have hRf : IsIso (E.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a)) := by
      change IsIso ((smallDerivedEvaluation X R ((AffineProEt.toProEt X).obj W)).map
        (DerivedCategory.Plus.Qh.map (q.map a)))
      rw [hb, Functor.map_comp, Functor.map_comp]
      have := h W
      infer_instance
    have : IsIso (E.rightDerivedFunctorPlusUnit.app (q.obj I')) := by
      change IsIso (E.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj I)))
      infer_instance
    have : IsIso (E.rightDerivedFunctorPlusUnit.app (q.obj J')) := by
      change IsIso (E.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj J)))
      infer_instance
    have : IsIso (E.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map (q.map a))) := hRf
    have hnat := E.rightDerivedFunctorPlusUnit.naturality (q.map a)
    have : IsIso ((E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map a) ≫
        E.rightDerivedFunctorPlusUnit.app (q.obj J')) := by
      rw [hnat]
      dsimp only [Functor.comp_map]
      infer_instance
    have : IsIso ((E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map a)) :=
      IsIso.of_isIso_comp_right _ (E.rightDerivedFunctorPlusUnit.app (q.obj J'))
    have : IsIso (DerivedCategory.Qh.map
        ((E.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient A (.up ℤ)).map a.hom))) :=
      Functor.map_isIso DerivedCategory.Plus.ι
        ((E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map a))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
      ((DerivedCategory.isIso_Qh_map_iff _).mp this)
  have : QuasiIso a.hom := quasiIso_of_basis_evaluation X R a.hom hqa
  have : IsIso (DerivedCategory.Plus.Q.map a) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map a)) := by
      change IsIso (DerivedCategory.Q.map a.hom)
      infer_instance
    exact isIso_of_reflects_iso (DerivedCategory.Plus.Q.map a) DerivedCategory.Plus.ι
  have : IsIso (eI.hom ≫ f ≫ eJ.inv) := by
    rw [← hb]
    assumption
  have : IsIso (f ≫ eJ.inv) := IsIso.of_isIso_comp_left eI.hom _
  exact IsIso.of_isIso_comp_right f eJ.inv

end AlgebraicGeometry.Scheme.ProEt
