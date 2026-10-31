/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.StrictEtaleFiniteOrdinaryInverseTransport
import all WeilConjectures.AlgebraicGeometry.StrictEtaleInverseTensorCoherence
import WeilConjectures.CategoryTheory.DerivedSquareIndependentUniverses
import WeilConjectures.CategoryTheory.IndependentLocalizedCube
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Derived inverse-image faces of strict coefficient transport

Source: Stacks Project, Tags 0D6D and 0G7E; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.sheafCompose siteCoefficientTensor
  coefficientQuotientSheaf coefficientQuotientMap siteCoefficientTensorAdj siteScalarUnderlyingIso

namespace TransportCube
universe q
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{q} C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory.{q} D]
  {E : Type*} [Category E] [Abelian E] [HasDerivedCategory.{q} E]
  {F : Type*} [Category F] [Abelian F] [HasDerivedCategory.{q} F]
  {G : Type*} [Category G] [Abelian G] [HasDerivedCategory.{q} G]
  {H : Type*} [Category H] [Abelian H] [HasDerivedCategory.{q} H]
  {I : Type*} [Category I] [Abelian I] [HasDerivedCategory.{q} I]
  {J : Type*} [Category J] [Abelian J] [HasDerivedCategory.{q} J]
  (a : C ⥤ D) [a.Additive]
  (b : D ⥤ E) [b.Additive]
  (c : E ⥤ F) [c.Additive]
  (d : C ⥤ G) [d.Additive]
  (e : G ⥤ E) [e.Additive]
  (f : G ⥤ H) [f.Additive]
  (g : H ⥤ F) [g.Additive]
  (h : C ⥤ I) [h.Additive]
  (i : I ⥤ H) [i.Additive]
  (j : D ⥤ J) [j.Additive]
  (k : J ⥤ F) [k.Additive]
  (m : I ⥤ J) [m.Additive]
  (aD : DerivedCategory C ⥤ DerivedCategory D)
  (bD : DerivedCategory D ⥤ DerivedCategory E)
  (cD : DerivedCategory E ⥤ DerivedCategory F)
  (dD : DerivedCategory C ⥤ DerivedCategory G)
  (eD : DerivedCategory G ⥤ DerivedCategory E)
  (fD : DerivedCategory G ⥤ DerivedCategory H)
  (gD : DerivedCategory H ⥤ DerivedCategory F)
  (hD : DerivedCategory C ⥤ DerivedCategory I)
  (iD : DerivedCategory I ⥤ DerivedCategory H)
  (jD : DerivedCategory D ⥤ DerivedCategory J)
  (kD : DerivedCategory J ⥤ DerivedCategory F)
  (mD : DerivedCategory I ⥤ DerivedCategory J)
  (φa : DerivedCategory.Q ⋙ aD ⟶ a.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φb : DerivedCategory.Q ⋙ bD ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φc : DerivedCategory.Q ⋙ cD ⟶ c.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φd : DerivedCategory.Q ⋙ dD ⟶ d.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φe : DerivedCategory.Q ⋙ eD ⟶ e.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φf : DerivedCategory.Q ⋙ fD ⟶ f.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φg : DerivedCategory.Q ⋙ gD ⟶ g.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φh : DerivedCategory.Q ⋙ hD ⟶ h.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φi : DerivedCategory.Q ⋙ iD ⟶ i.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φj : DerivedCategory.Q ⋙ jD ⟶ j.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φk : DerivedCategory.Q ⋙ kD ⟶ k.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φm : DerivedCategory.Q ⋙ mD ⟶ m.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)


private theorem cube_on_representative
    (q1 : a ⋙ b ≅ d ⋙ e)
    (q2 : e ⋙ c ≅ f ⋙ g)
    (q3 : d ⋙ f ≅ h ⋙ i)
    (q4 : b ⋙ c ≅ j ⋙ k)
    (q5 : a ⋙ j ≅ h ⋙ m)
    (q6 : m ⋙ k ≅ i ⋙ g)
    (s1 : aD ⋙ bD ≅ dD ⋙ eD)
    (s2 : eD ⋙ cD ≅ fD ⋙ gD)
    (s3 : dD ⋙ fD ≅ hD ⋙ iD)
    (s4 : bD ⋙ cD ≅ jD ⋙ kD)
    (s5 : aD ⋙ jD ≅ hD ⋙ mD)
    (s6 : mD ⋙ kD ≅ iD ⋙ gD)
    (P : CochainComplex C ℤ)
    (ht : Mono (gD.map (iD.map (φh.app P)) ≫
      gD.map (φi.app ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φg.app ((i.mapHomologicalComplex (.up ℤ)).obj
        ((h.mapHomologicalComplex (.up ℤ)).obj P))))
    (r1 : s1.hom.app (DerivedCategory.Q.obj P) ≫
      eD.map (φd.app P) ≫
      φe.app ((d.mapHomologicalComplex (.up ℤ)).obj P) =
      bD.map (φa.app P) ≫
      φb.app ((a.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q1.hom (.up ℤ)).app P))
    (r2 : s2.hom.app (DerivedCategory.Q.obj ((d.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      gD.map (φf.app ((d.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φg.app ((f.mapHomologicalComplex (.up ℤ)).obj ((d.mapHomologicalComplex (.up ℤ)).obj P)) =
      cD.map (φe.app ((d.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φc.app ((e.mapHomologicalComplex (.up ℤ)).obj ((d.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q2.hom (.up ℤ)).app
        ((d.mapHomologicalComplex (.up ℤ)).obj P)))
    (r3 : s3.hom.app (DerivedCategory.Q.obj P) ≫
      iD.map (φh.app P) ≫
      φi.app ((h.mapHomologicalComplex (.up ℤ)).obj P) =
      fD.map (φd.app P) ≫
      φf.app ((d.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q3.hom (.up ℤ)).app P))
    (r4 : s4.hom.app (DerivedCategory.Q.obj ((a.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      kD.map (φj.app ((a.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φk.app ((j.mapHomologicalComplex (.up ℤ)).obj ((a.mapHomologicalComplex (.up ℤ)).obj P)) =
      cD.map (φb.app ((a.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φc.app ((b.mapHomologicalComplex (.up ℤ)).obj ((a.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q4.hom (.up ℤ)).app
        ((a.mapHomologicalComplex (.up ℤ)).obj P)))
    (r5 : s5.hom.app (DerivedCategory.Q.obj P) ≫
      mD.map (φh.app P) ≫
      φm.app ((h.mapHomologicalComplex (.up ℤ)).obj P) =
      jD.map (φa.app P) ≫
      φj.app ((a.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q5.hom (.up ℤ)).app P))
    (r6 : s6.hom.app (DerivedCategory.Q.obj ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      gD.map (φi.app ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φg.app ((i.mapHomologicalComplex (.up ℤ)).obj ((h.mapHomologicalComplex (.up ℤ)).obj P)) =
      kD.map (φm.app ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φk.app ((m.mapHomologicalComplex (.up ℤ)).obj ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q6.hom (.up ℤ)).app
        ((h.mapHomologicalComplex (.up ℤ)).obj P)))
    (comm : ∀ X : C,
      c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫ g.map (q3.hom.app X) =
        q4.hom.app (a.obj X) ≫ k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X)) :
    cD.map (s1.hom.app (DerivedCategory.Q.obj P)) ≫
      s2.hom.app (dD.obj (DerivedCategory.Q.obj P)) ≫
      gD.map (s3.hom.app (DerivedCategory.Q.obj P)) =
    s4.hom.app (aD.obj (DerivedCategory.Q.obj P)) ≫
      kD.map (s5.hom.app (DerivedCategory.Q.obj P)) ≫
      s6.hom.app (hD.obj (DerivedCategory.Q.obj P)) := by
  let := ht
  apply (cancel_mono
    (gD.map (iD.map
        (φh.app P)) ≫
      gD.map (φi.app
        ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φg.app
        ((i.mapHomologicalComplex (.up ℤ)).obj
          ((h.mapHomologicalComplex (.up ℤ)).obj P)))).mp
  have h1 := r1
  have h2 := r2
  have h3 := r3
  have h4 := r4
  have h5 := r5
  have h6 := r6
  have n2 := s2.hom.naturality (φd.app P)
  have n4 := s4.hom.naturality (φa.app P)
  have n6 := s6.hom.naturality (φh.app P)
  dsimp only [CategoryTheory.Functor.comp_map] at n2 n4 n6
  have nl : cD.map (s1.hom.app (DerivedCategory.Q.obj P)) ≫
      s2.hom.app (dD.obj (DerivedCategory.Q.obj P)) ≫
      gD.map (s3.hom.app (DerivedCategory.Q.obj P)) ≫
      gD.map (iD.map
        (φh.app P)) ≫
      gD.map (φi.app
        ((h.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φg.app
        ((i.mapHomologicalComplex (.up ℤ)).obj
          ((h.mapHomologicalComplex (.up ℤ)).obj P)) =
      cD.map (bD.map
        (φa.app P)) ≫
      cD.map (φb.app
        ((a.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      φc.app
        ((b.mapHomologicalComplex (.up ℤ)).obj
          ((a.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map
        ((c.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex q1.hom (.up ℤ)).app P) ≫
          (NatTrans.mapHomologicalComplex q2.hom (.up ℤ)).app
            ((d.mapHomologicalComplex (.up ℤ)).obj P) ≫
          (g.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex q3.hom (.up ℤ)).app P)) := by
    erw [← gD.map_comp_assoc, ← gD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h3]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [φg.naturality]
    erw [← reassoc_of% n2, reassoc_of% h2]
    erw [← cD.map_comp_assoc, ← cD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h1]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [NatTrans.naturality_assoc φc]
    simp only [CategoryTheory.Functor.comp_map]
  simp only [Category.assoc]
  erw [nl]
  erw [← reassoc_of% n6]
  erw [h6]
  erw [← kD.map_comp_assoc, ← kD.map_comp_assoc]
  simp only [Category.assoc]
  erw [h5]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [NatTrans.naturality_assoc φk]
  erw [← reassoc_of% n4, reassoc_of% h4]
  simp only [CategoryTheory.Functor.comp_map, ← CategoryTheory.Functor.map_comp]
  repeat' apply congrArg (fun t ↦ _ ≫ t)
  apply congrArg DerivedCategory.Q.map
  ext n
  exact comm (P.X n)

end TransportCube

private theorem cancel_transport_square
    {C : Type*} [Category C] {X Y Z W V : C}
    (a : X ≅ Y) (b : Z ≅ W) (c : V ≅ Z) (t : X ⟶ V) (s : Y ⟶ W)
    (h : t ≫ c.hom ≫ b.hom = a.hom ≫ s) :
    s ≫ b.inv ≫ c.inv = a.inv ≫ t := by
  apply (cancel_epi a.hom).1
  apply (cancel_mono (c.hom ≫ b.hom)).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using h.symm

section Ordinary
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  {a : StrictEtaleCoefficientChange O O' ell mu phi index}
  {T S : Scheme.{u}} {g : T ⟶ S}
  {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
  {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
  (UT : StrictEtaleCoefficientTransport a T PTA PTB)
  (US : StrictEtaleCoefficientTransport a S PSA PSB)
  (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)

private abbrev transport_underlying (V : Scheme.{u}) (n : ℕ) :
    restrictScalars ((sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf V n)) ⋙
        coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n) ≅
      coefficientUnderlying (J := V.smallEtaleTopology) O' mu n :=
  isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf V n))
    (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))

private theorem transport_insertion_formula (V : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel V O ell (index n)) :
    (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) M) =
      (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map
          ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n)).unit.app M) ≫
        (transport_underlying (a := a) V n).hom.app
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).obj M) := by
  dsimp only [siteTensorUnitUnderlying, transport_underlying, coefficientUnderlying,
    CategoryTheory.Functor.comp_map, isoWhiskerRight_hom, whiskerRight_app]
  simp only [CategoryTheory.Functor.map_comp]

private theorem quotient_insertion
    {R : Type (u + 1)} [CommRing R] {t : R} (V : Scheme.{u})
    {m n : ℕ} (h : n ≤ m) (M : strictEtaleLevel V R t m) :
    (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying.{u + 1, u, u + 1}
          (coefficientQuotientMap (J := V.smallEtaleTopology) R t h) M) =
      insertion V.smallEtaleTopology h M := by
  dsimp only [siteTensorUnitUnderlying, insertion, underlying, coefficientUnderlying,
    coefficientRestrictionUnderlying, CategoryTheory.Functor.comp_map,
    isoWhiskerRight_hom, whiskerRight_app]
  simp only [CategoryTheory.Functor.map_comp]

private theorem transport_insertion_naturality
    (V : Scheme.{u}) (n : ℕ) {M N : strictEtaleLevel V O ell (index n)} (f : M ⟶ N) :
    (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map f ≫
        (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) N) =
      (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) M) ≫
        (coefficientUnderlying (J := V.smallEtaleTopology) O' mu n).map
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).map f) := by
  have hu := congrArg
    ((coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map)
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n)).unit.naturality f)
  have hq := (transport_underlying (a := a) V n).hom.naturality
    ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).map f)
  simp only [transport_insertion_formula, CategoryTheory.Functor.map_comp, Category.assoc] at hu ⊢
  dsimp only [coefficientUnderlying, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.id_map] at hu hq ⊢
  rw [reassoc_of% hu, hq]

private theorem transport_transpose (V : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel V O ell (index n)) (N : strictEtaleLevel V O' mu n)
    (f : (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).obj M ⟶ N) :
    (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map
        ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n)).homEquiv M N f) ≫
        (transport_underlying (a := a) V n).hom.app N =
      (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) M) ≫
        (coefficientUnderlying (J := V.smallEtaleTopology) O' mu n).map f := by
  rw [transport_insertion_formula]
  simpa only [Category.assoc] using
    transpose_underlying (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n))
      (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n))
      (coefficientUnderlying (J := V.smallEtaleTopology) O' mu n)
      (transport_underlying (a := a) V n) M N f

set_option maxHeartbeats 1500000 in
-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem scalar_insertion_ext (n : ℕ)
    (M : strictEtaleLevel S O ell (index n)) (N : strictEtaleLevel T O' mu n)
    (f k : (B.lift n).modules.obj
      ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) ⟶ N)
    (he : (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map f =
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map k) : f = k := by
  apply ((B.levelAdj n).homEquiv _ N).injective
  apply ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n)).homEquiv M _).injective
  apply (coefficientUnderlying (J := S.smallEtaleTopology) O ell (index n)).map_injective
  apply (cancel_mono ((transport_underlying (a := a) S n).hom.app
    ((B.right n).obj N) ≫ (B.rightUnderlying n).hom.app N)).1
  have hf := transport_transpose (a := a) S n M ((B.right n).obj N)
    ((B.levelAdj n).homEquiv _ _ f)
  have hk := transport_transpose (a := a) S n M ((B.right n).obj N)
    ((B.levelAdj n).homEquiv _ _ k)
  erw [reassoc_of% hf, reassoc_of% hk]
  have tf := B.levelTranspose n ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) N f
  have tk := B.levelTranspose n ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) N k
  dsimp only [coefficientUnderlying, CategoryTheory.Functor.comp_map] at tf tk
  erw [tf, tk]
  erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  apply congrArg ((strictEtaleSetAdjunction g).homEquiv _ _)
  exact he

set_option maxHeartbeats 1500000 in
-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem ordinary_evaluation
    {DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj}
    {DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj}
    (square : StrictEtaleInverseTransport UT US A B DA DB) (n : ℕ)
    (e : siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (he : ∀ M : strictEtaleLevel S O ell (index n),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map (e.hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    (M : strictEtaleCoefficientSystem S O ell) :
    (B.lift n).modules.map ((US.val.evaluation n).inv.app M) ≫
      (B.inverseEvaluation n).inv.app (US.ordinary.obj M) ≫
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
        (square.val.1.hom.app M) =
    e.hom.app (M.level (index n)) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map
        ((A.inverseEvaluation (index n)).inv.app M) ≫
      (UT.val.evaluation n).inv.app (A.inverse.obj M) := by
  apply scalar_insertion_ext B n (M.level (index n))
  have hs := square.property.1 n M
  have hUS := US.property.2.1 n M
  have hUT := UT.property.2.1 n (A.inverse.obj M)
  have hnB := (B.lift n).moduleUnderlying.inv.naturality
    ((US.val.evaluation n).inv.app M)
  let U := coefficientUnderlying (J := T.smallEtaleTopology) O' mu n
  have hs' := cancel_transport_square
    ((strictEtaleInverseUnderlying A (index n)).app M)
    ((strictEtaleInverseUnderlying B n).app (US.ordinary.obj M))
    ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n ⋙ U).mapIso
      (square.val.1.app M).symm)
    ((UT.setUnit n).app (A.inverse.obj M))
    ((Scheme.etaleSetPullback g).map ((US.setUnit n).app M)) hs
  dsimp only [strictEtaleInverseUnderlying, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    Iso.symm_hom, Iso.symm_inv,
    Iso.trans_inv, NatTrans.comp_app, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    whiskerRight_app, whiskerLeft_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.comp_map] at hs'
  simp only [Category.comp_id, Category.assoc] at hs'
  have hnat' := transport_insertion_naturality (a := a) T n
    ((A.inverseEvaluation (index n)).inv.app M)
  simp only [CategoryTheory.Functor.map_comp]
  dsimp only [underlying, coefficientUnderlying, CategoryTheory.Functor.comp_map] at hnB ⊢
  erw [← reassoc_of% hnB]
  rw [← (Scheme.etaleSetPullback g).map_comp_assoc]
  rw [← CategoryTheory.Functor.map_comp, ← hUS]
  erw [reassoc_of% he (M.level (index n))]
  erw [← reassoc_of% hnat']
  have hUT' := congrArg
    ((sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map) hUT
  simp only [CategoryTheory.Functor.map_comp] at hUT'
  erw [← hUT']
  exact hs'

set_option maxHeartbeats 1500000 in
-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem ordinary_evaluation_forward
    {DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj}
    {DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj}
    (square : StrictEtaleInverseTransport UT US A B DA DB) (n : ℕ)
    (e : siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (he : ∀ M : strictEtaleLevel S O ell (index n),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map (e.hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    (M : strictEtaleCoefficientSystem S O ell) :
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
        (square.val.1.hom.app M) ≫
      (UT.val.evaluation n).hom.app (A.inverse.obj M) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map
        ((A.inverseEvaluation (index n)).hom.app M) =
    (B.inverseEvaluation n).hom.app (US.ordinary.obj M) ≫
      (B.lift n).modules.map ((US.val.evaluation n).hom.app M) ≫
      e.hom.app (M.level (index n)) := by
  apply (cancel_epi ((B.lift n).modules.map ((US.val.evaluation n).inv.app M) ≫
    (B.inverseEvaluation n).inv.app (US.ordinary.obj M))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% ordinary_evaluation UT US A B square n e he M]
  simp only [Iso.inv_hom_id_app_assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  erw [(siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map_id,
    Category.comp_id]

set_option maxHeartbeats 1500000 in
-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem mixed_insertion_ext {m n : ℕ} (h : n ≤ m)
    (M : strictEtaleLevel S O ell (index m)) (N : strictEtaleLevel T O' mu n)
    (f k : (B.lift n).modules.obj ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj
      ((coefficientTensor.{u + 1, u, u + 1} (J := S.smallEtaleTopology) (O := O) (ell := ell)
        (index.monotone h)).obj M)) ⟶ N)
    (he : (Scheme.etaleSetPullback g).map (insertion S.smallEtaleTopology
        (index.monotone h) M) ≫
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) _)) ≫
      (B.lift n).moduleUnderlying.inv.app _ ≫
      (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map f =
      (Scheme.etaleSetPullback g).map (insertion S.smallEtaleTopology
        (index.monotone h) M) ≫
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) _)) ≫
      (B.lift n).moduleUnderlying.inv.app _ ≫
      (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map k) : f = k := by
  apply ((B.levelAdj n).homEquiv _ N).injective
  apply ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n)).homEquiv _ _).injective
  apply ((coefficientTensorAdj.{u + 1, u, u + 1} (J := S.smallEtaleTopology) (O := O) (ell := ell)
    (index.monotone h)).homEquiv M _).injective
  apply (coefficientUnderlying (J := S.smallEtaleTopology) O ell (index m)).map_injective
  have hf := insertion_transpose S.smallEtaleTopology (index.monotone h) M _
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n)).homEquiv _ _
      ((B.levelAdj n).homEquiv _ _ f))
  have hk := insertion_transpose S.smallEtaleTopology (index.monotone h) M _
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n)).homEquiv _ _
      ((B.levelAdj n).homEquiv _ _ k))
  have hf' := transport_transpose (a := a) S n _ ((B.right n).obj N)
    ((B.levelAdj n).homEquiv _ _ f)
  have hk' := transport_transpose (a := a) S n _ ((B.right n).obj N)
    ((B.levelAdj n).homEquiv _ _ k)
  apply (cancel_mono ((coefficientRestrictionUnderlying (J := S.smallEtaleTopology)
    O ell (index.monotone h)).hom.app _ ≫
      (transport_underlying (a := a) S n).hom.app ((B.right n).obj N) ≫
      (B.rightUnderlying n).hom.app N)).1
  erw [reassoc_of% hf, reassoc_of% hk, reassoc_of% hf', reassoc_of% hk']
  have tf := B.levelTranspose n _ N f
  have tk := B.levelTranspose n _ N k
  dsimp only [coefficientUnderlying, CategoryTheory.Functor.comp_map] at tf tk
  erw [tf, tk]
  erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  apply congrArg ((strictEtaleSetAdjunction g).homEquiv _ _)
  exact he

set_option maxHeartbeats 1500000 in
-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem ordinary_quotient
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (qT : StrictEtaleTransportQuotient UT) (qS : StrictEtaleTransportQuotient US)
    (e : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (he : ∀ n (M : strictEtaleLevel S O ell (index n)),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map ((e n).hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    {m n : ℕ} (h : n ≤ m) (M : strictEtaleLevel S O ell (index m)) :
    (B.lift n).modules.map ((qS.val.1 h).hom.app M) ≫
      (DB.tensor h).hom.app ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S m)).obj M) ≫
      (coefficientTensor.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (O := O') (ell := mu) h).map
        ((e m).hom.app M) =
    (e n).hom.app ((coefficientTensor.{u + 1, u, u + 1} (J := S.smallEtaleTopology) (O := O)
      (ell := ell) (index.monotone h)).obj M) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map
        ((DA.tensor (index.monotone h)).hom.app M) ≫
      (qT.val.1 h).hom.app ((A.lift (index m)).modules.obj M) := by
  apply mixed_insertion_ext B h M
  have hS := congrArg
    ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map)
    (qS.property.1 h M)
  have hT := congrArg
    ((sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map)
    (qT.property.1 h ((A.lift (index m)).modules.obj M))
  have hnS := (B.lift n).moduleUnderlying.inv.naturality ((qS.val.1 h).hom.app M)
  have hnA' := transport_insertion_naturality (a := a) T n
    ((DA.tensor (index.monotone h)).hom.app M)
  have hnB := insertion_naturality T.smallEtaleTopology h ((e m).hom.app M)
  dsimp only [CategoryTheory.Functor.comp_map] at hnS
  simp only [CategoryTheory.Functor.map_comp]
  erw [← reassoc_of% hnS]
  simp only [CategoryTheory.Functor.map_comp, quotient_insertion] at hS hT
  have hS' := congrArg ((Scheme.etaleSetPullback g).map) hS
  simp only [CategoryTheory.Functor.map_comp] at hS'
  erw [reassoc_of% hS']
  have hB := tensor_insertion PSB PTB B DB h
    ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S m)).obj M)
  erw [reassoc_of% hB]
  dsimp only [underlying, coefficientUnderlying, CategoryTheory.Functor.comp_map] at hnB ⊢
  erw [← hnB]
  erw [reassoc_of% he m M]
  have hn := he n ((coefficientTensor.{u + 1, u, u + 1}
    (J := S.smallEtaleTopology) (O := O) (ell := ell) (index.monotone h)).obj M)
  conv_rhs => erw [reassoc_of% hn]
  conv_rhs => erw [← reassoc_of% hnA']
  conv_rhs => erw [reassoc_of% tensor_insertion PSA PTA A DA (index.monotone h) M]
  erw [hT]
  rfl

attribute [local semireducible] siteCoefficientTensor

set_option maxHeartbeats 1500000 in
-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem transport_good (V : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (strictEtaleLevel V O ell (index n)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := V.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := V.smallEtaleTopology) O ell (index n))
        (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).mapHomologicalComplex
        (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := V.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := V.smallEtaleTopology) O' mu n)
      ((((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).mapHomologicalComplex
        (.up ℤ)).obj P).X i) := by
  exact isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse (O := O) (t := ell) V.smallEtaleTopology (index n)) (a.sheaf V n)
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n))
    (fun _ ↦ rfl)
    (by intro M N f
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl) P hk hf

end Ordinary



-- Keep the two localization calculations abstract from the chosen comparisons.
set_option maxHeartbeats 300000 in
-- Instantiate the evaluation cube and cancel its component isomorphisms.
private theorem derived_evaluation
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (square : StrictEtaleInverseTransport UT US A B DA.system DB.system)
    (hUT : ∀ n (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ),
      IsIso ((UT.level n).counit.app P))
    (hUS : ∀ n (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ),
      IsIso ((US.level n).counit.app P))
    (ordinary : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (ho : ∀ n (M : strictEtaleLevel S O ell (index n)),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map ((ordinary n).hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    (e : ∀ n, (US.level n).derived ⋙ (DB.level n).inverse ≅
      (DA.level (index n)).inverse ⋙ (UT.level n).derived)
    (he : ∀ n (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ),
      (e n).hom.app (DerivedCategory.Q.obj P) ≫
        (UT.level n).derived.map ((DA.level (index n)).inverseFactors.hom.app P) ≫
        (UT.level n).counit.app
          (((A.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (DB.level n).inverse.map ((US.level n).counit.app P) ≫
        (DB.level n).inverseFactors.hom.app
          (((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app P)) :
    ∀ n K,
        (DB.level n).inverse.map ((US.derivedEvaluation n).inv.app K) ≫
          (DB.inverseEvaluation n).inv.app (US.derived.obj K) ≫
          (PTB.evaluation n).map (square.derived.hom.app K) =
        (e n).hom.app ((PSA.evaluation (index n)).obj K) ≫
          (UT.level n).derived.map ((DA.inverseEvaluation (index n)).inv.app K) ≫
          (UT.derivedEvaluation n).inv.app (DA.system.inverse.obj K) := by
  classical
  let (n : ℕ) (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ) :
      IsIso ((UT.level n).counit.app P) := hUT n P
  let (n : ℕ) (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ) :
      IsIso ((US.level n).counit.app P) := hUS n P
  have hT (n : ℕ) : IsIso (UT.level n).counit := NatIso.isIso_of_isIso_app _
  have hS (n : ℕ) : IsIso (US.level n).counit := NatIso.isIso_of_isIso_app _
  let (n : ℕ) : IsIso (UT.level n).counit := hT n
  let (n : ℕ) : IsIso (US.level n).counit := hS n
  intro n K
  have hc := localized_exactCube
    US.ordinary B.inverse
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n)
    A.inverse UT.ordinary
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n))
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (coefficientEvaluation (J := S.smallEtaleTopology) (O := O) (ell := ell) (index n))
    (A.lift (index n)).modules
    (coefficientEvaluation (J := S.smallEtaleTopology) (O := O') (ell := mu) n)
    (B.lift n).modules (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n))
    US.derived DB.system.inverse (PTB.evaluation n)
    DA.system.inverse UT.derived (PTA.evaluation (index n)) (UT.level n).derived
    (PSA.evaluation (index n)) (DA.level (index n)).inverse (PSB.evaluation n)
    (DB.level n).inverse (US.level n).derived
    US.factors DB.system.inverseFactors (PTB.evaluationFactors n)
    DA.system.inverseFactors UT.factors (PTA.evaluationFactors (index n))
    (asIso (UT.level n).counit) (PSA.evaluationFactors (index n))
    (DA.level (index n)).inverseFactors (PSB.evaluationFactors n)
    (DB.level n).inverseFactors (asIso (US.level n).counit)
    square.val.1 (UT.val.evaluation n) (A.inverseEvaluation (index n))
    (B.inverseEvaluation n) (US.val.evaluation n) (ordinary n)
    square.derived (UT.derivedEvaluation n) (DA.inverseEvaluation (index n))
    (DB.inverseEvaluation n) (US.derivedEvaluation n) (e n)
    square.property.2 (UT.property.2.2.2 n) (DA.inverseEvaluation_rep (index n))
    (DB.inverseEvaluation_rep n) (US.property.2.2.2 n) (he n)
    (ordinary_evaluation_forward UT US A B square n (ordinary n) (ho n))
  have hh := congr_app hc K
  dsimp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hh
  -- Cancel the evaluation isomorphisms before expanding their mapped identities.
  simpa only [Iso.trans_inv, CategoryTheory.Functor.mapIso_inv, Iso.app_inv,
    Category.assoc] using
    (cancel_transport_square
    ((DB.inverseEvaluation n).app (US.derived.obj K) ≪≫
      (DB.level n).inverse.mapIso ((US.derivedEvaluation n).app K))
    ((UT.level n).derived.mapIso ((DA.inverseEvaluation (index n)).app K))
    ((UT.derivedEvaluation n).app (DA.system.inverse.obj K))
    ((PTB.evaluation n).map (square.derived.hom.app K))
    ((e n).hom.app ((PSA.evaluation (index n)).obj K))
    (by simpa only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
      Iso.app_hom, Category.assoc] using hh)).symm

set_option maxHeartbeats 300000 in
-- Instantiate the six-face calculation on one K-flat representative.
private theorem derived_quotient_on_flat
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (qT : StrictEtaleTransportQuotient UT) (qS : StrictEtaleTransportQuotient US)
    (ordinary : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (ho : ∀ n (M : strictEtaleLevel S O ell (index n)),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map ((ordinary n).hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    (e : ∀ n, (US.level n).derived ⋙ (DB.level n).inverse ≅
      (DA.level (index n)).inverse ⋙ (UT.level n).derived)
    (he : ∀ n (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ),
      (e n).hom.app (DerivedCategory.Q.obj P) ≫
        (UT.level n).derived.map ((DA.level (index n)).inverseFactors.hom.app P) ≫
        (UT.level n).counit.app
          (((A.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (DB.level n).inverse.map ((US.level n).counit.app P) ≫
        (DB.level n).inverseFactors.hom.app
          (((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app P))
    {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (strictEtaleLevel S O ell (index m)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := S.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell (index m))
        (P.X i)) :
        (DB.level n).inverse.map ((qS.derived h).hom.app (DerivedCategory.Q.obj P)) ≫
          (DB.derivedTensor h).hom.app ((US.level m).derived.obj (DerivedCategory.Q.obj P)) ≫
          (PTB.scalar h).derived.map ((e m).hom.app (DerivedCategory.Q.obj P)) =
        (e n).hom.app ((PSA.scalar (index.monotone h)).derived.obj (DerivedCategory.Q.obj P)) ≫
          (UT.level n).derived.map
            ((DA.derivedTensor (index.monotone h)).hom.app (DerivedCategory.Q.obj P)) ≫
          (qT.derived h).hom.app ((DA.level (index m)).inverse.obj (DerivedCategory.Q.obj P)) := by
  classical
  let : PreservesFiniteLimits (Scheme.etaleSetPullback g) :=
    (etaleSetInverseImage_exact g).2.2.1
  have hU := transport_good (a := a) S m P hk hf
  have hI := inverse_good PTA A (index m) P hk hf
  have hUI := transport_good (a := a) T m _ hI.1 hI.2
  let := (UT.level m).computes _ hI.1
  let := (PTB.scalar h).computes _ hUI.1
  exact TransportCube.cube_on_representative
    (coefficientTensor.{u + 1, u, u + 1} (J := S.smallEtaleTopology) (O := O) (ell := ell)
      (index.monotone h))
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)) (B.lift n).modules
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S m))
    (coefficientTensor.{u + 1, u, u + 1} (J := S.smallEtaleTopology) (O := O') (ell := mu) h)
    (B.lift m).modules
    (coefficientTensor.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (O := O') (ell := mu) h)
    (A.lift (index m)).modules (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T m))
    (A.lift (index n)).modules (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (coefficientTensor.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (O := O) (ell := ell)
      (index.monotone h))
    (PSA.scalar (index.monotone h)).derived (US.level n).derived (DB.level n).inverse
    (US.level m).derived (PSB.scalar h).derived (DB.level m).inverse
    (PTB.scalar h).derived (DA.level (index m)).inverse (UT.level m).derived
    (DA.level (index n)).inverse (UT.level n).derived
    (PTA.scalar (index.monotone h)).derived
    (PSA.scalar (index.monotone h)).counit (US.level n).counit
    (DB.level n).inverseFactors.hom (US.level m).counit (PSB.scalar h).counit
    (DB.level m).inverseFactors.hom (PTB.scalar h).counit
    (DA.level (index m)).inverseFactors.hom (UT.level m).counit
    (DA.level (index n)).inverseFactors.hom (UT.level n).counit
    (PTA.scalar (index.monotone h)).counit
    (qS.val.1 h) (DB.tensor h) (ordinary m) (ordinary n)
    (DA.tensor (index.monotone h)) (qT.val.1 h)
    (qS.derived h) (DB.derivedTensor h) (e m) (e n)
    (DA.derivedTensor (index.monotone h)) (qT.derived h)
    P (inferInstance)
    (qS.property.2 h P) (DB.derivedTensor_rep h _ hU.1 hU.2)
    (he m P) (he n _) (DA.derivedTensor_rep (index.monotone h) P hk hf)
    (qT.property.2 h _)
    (ordinary_quotient UT US A B DA DB qT qS ordinary ho h)

-- Name the two constructed paths to share their types during the resolution argument.
@[irreducible] private def quotient_left
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (qS : StrictEtaleTransportQuotient US)
    (e : ∀ n, (US.level n).derived ⋙ (DB.level n).inverse ≅
      (DA.level (index n)).inverse ⋙ (UT.level n).derived)
    {m n : ℕ} (h : n ≤ m) :
    (PSA.scalar (index.monotone h)).derived ⋙ (US.level n).derived ⋙
        (DB.level n).inverse ⟶
      (DA.level (index m)).inverse ⋙ (UT.level m).derived ⋙ (PTB.scalar h).derived :=
  (CategoryTheory.Functor.associator (PSA.scalar (index.monotone h)).derived
    (US.level n).derived (DB.level n).inverse).inv ≫
    whiskerRight (qS.derived h).hom (DB.level n).inverse ≫
    (CategoryTheory.Functor.associator (US.level m).derived (PSB.scalar h).derived
      (DB.level n).inverse).hom ≫
    whiskerLeft (US.level m).derived (DB.derivedTensor h).hom ≫
    (CategoryTheory.Functor.associator (US.level m).derived (DB.level m).inverse
      (PTB.scalar h).derived).inv ≫
    whiskerRight (e m).hom (PTB.scalar h).derived ≫
    (CategoryTheory.Functor.associator (DA.level (index m)).inverse
      (UT.level m).derived (PTB.scalar h).derived).hom

@[irreducible] private def quotient_right
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (qT : StrictEtaleTransportQuotient UT)
    (e : ∀ n, (US.level n).derived ⋙ (DB.level n).inverse ≅
      (DA.level (index n)).inverse ⋙ (UT.level n).derived)
    {m n : ℕ} (h : n ≤ m) :
    (PSA.scalar (index.monotone h)).derived ⋙ (US.level n).derived ⋙
        (DB.level n).inverse ⟶
      (DA.level (index m)).inverse ⋙ (UT.level m).derived ⋙ (PTB.scalar h).derived :=
  whiskerLeft (PSA.scalar (index.monotone h)).derived (e n).hom ≫
    (CategoryTheory.Functor.associator (PSA.scalar (index.monotone h)).derived
      (DA.level (index n)).inverse (UT.level n).derived).inv ≫
    whiskerRight (DA.derivedTensor (index.monotone h)).hom (UT.level n).derived ≫
    (CategoryTheory.Functor.associator (DA.level (index m)).inverse
      (PTA.scalar (index.monotone h)).derived (UT.level n).derived).hom ≫
    whiskerLeft (DA.level (index m)).inverse (qT.derived h).hom

set_option maxHeartbeats 300000 in
-- Pass from K-flat representatives to arbitrary derived objects.
private theorem derived_quotient
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (qT : StrictEtaleTransportQuotient UT) (qS : StrictEtaleTransportQuotient US)
    (ordinary : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (ho : ∀ n (M : strictEtaleLevel S O ell (index n)),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map ((ordinary n).hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    (e : ∀ n, (US.level n).derived ⋙ (DB.level n).inverse ≅
      (DA.level (index n)).inverse ⋙ (UT.level n).derived)
    (he : ∀ n (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ),
      (e n).hom.app (DerivedCategory.Q.obj P) ≫
        (UT.level n).derived.map ((DA.level (index n)).inverseFactors.hom.app P) ≫
        (UT.level n).counit.app
          (((A.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (DB.level n).inverse.map ((US.level n).counit.app P) ≫
        (DB.level n).inverseFactors.hom.app
          (((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app P)) :
    ∀ {m n : ℕ} (h : n ≤ m) K,
        (DB.level n).inverse.map ((qS.derived h).hom.app K) ≫
          (DB.derivedTensor h).hom.app ((US.level m).derived.obj K) ≫
          (PTB.scalar h).derived.map ((e m).hom.app K) =
        (e n).hom.app ((PSA.scalar (index.monotone h)).derived.obj K) ≫
          (UT.level n).derived.map
            ((DA.derivedTensor (index.monotone h)).hom.app K) ≫
          (qT.derived h).hom.app ((DA.level (index m)).inverse.obj K) := by
  classical
  intro m n h K
  let α := quotient_left UT US A B DA DB qS e h
  let β := quotient_right UT US A B DA DB qT e h
  have hk_eq : α.app K = β.app K := by
    obtain ⟨P, q, hk, hf, hq, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell (index m))
      (DerivedCategory.Q.objPreimage K)
    let := hq
    let i : DerivedCategory.Q.obj P ≅ K :=
      asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    apply (cancel_epi (((PSA.scalar (index.monotone h)).derived ⋙
      (US.level n).derived ⋙ (DB.level n).inverse).map i.hom)).1
    rw [α.naturality, β.naturality]
    have hh : α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
      simpa only [α, β, quotient_left, quotient_right, NatTrans.comp_app,
        whiskerRight_app, whiskerLeft_app, CategoryTheory.Functor.associator_hom_app,
        CategoryTheory.Functor.associator_inv_app, Category.id_comp, Category.comp_id] using
        derived_quotient_on_flat UT US A B DA DB qT qS ordinary ho e he h P hk
          (fun j ↦ (exactFunctor _ _).prop_of_iso
            (siteSheafTensorRightIso _ (P.X j)).symm (hf j))
    rw [hh]
  simpa only [α, β, quotient_left, quotient_right, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, CategoryTheory.Functor.associator_hom_app,
    CategoryTheory.Functor.associator_inv_app, Category.id_comp, Category.comp_id] using hk_eq

set_option maxHeartbeats 300000 in
-- Descend the finite comparisons and combine their compatibility faces.
/-- The finite derived inverse-image comparisons satisfy their evaluation and quotient
cubes. This statement uses only inverse images and scalar extension; no proper-image
mate or scalar-equivalence hypothesis is involved.
Source: Stacks Project, Cohomology on Sites, Tags 0D6D and 0G7E; Zheng,
Construction 4.1, Construction 5.15 and Lemma 5.16.
(blueprint: lem-pur-strict-etale-derived-inverse-transport-faces).

Proof: construct the finite ordinary comparison from the normalized balanced
scalar/inverse-image comparison for the constant quotient ring square. Its map
sends inverse image of the scalar insertion to insertion after inverse image.
The coefficient generators and the constants equations of the supplied algebraic
lifts verify the ring square. The supplied hUT and hUS turn the finite scalar
counits into factorization isomorphisms on all cochain complexes. Conjugate the
termwise ordinary comparison by these maps and the inverse-image factors.
Fully faithful whiskering by localization descends it to the finite comparison e.
For evaluation, precompose the desired natural-transformation equation by the
system localization Q, which is faithful on natural transformations. Substitute
the transport representative equations, the inverse-evaluation representative
equations, and the defining factorization equation of e. All finite scalar
counits are now invertible by hUT and hUS. Cancel them and the factorization
isomorphisms. The equation is the ordinary component comparison, fixed uniquely
by the setUnit normalization of square and the scalar-adjunction Hom bijection.
For quotient extension, the two coefficient paths agree on every quotient generator.
The normalized ordinary quotient comparisons are the scalar associators, by the
scalar-adjunction Hom bijections and their unit equations. The normalized derived
representative equations for qT, qS and the two derivedTensor maps identify their
components with those associators on common flat-term K-flat representatives.
Balanced pullback composition makes the resulting ordinary cube commute. Cancel
its computation isomorphisms and use naturality across resolutions to obtain the
second displayed cube, without assuming flat quotient maps or strict index growth. -/
theorem nonempty_strictEtaleDerivedInverseTransportFaces
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O ell _ _ _ A PSA PTA)
    (DB : CoefficientSystemDerivedImage (J := S.smallEtaleTopology)
      (K := T.smallEtaleTopology) O' mu _ _ _ B PSB PTB)
    (qT : StrictEtaleTransportQuotient UT) (qS : StrictEtaleTransportQuotient US)
    (square : StrictEtaleInverseTransport UT US A B DA.system DB.system)
    (hUT : ∀ n (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ),
      IsIso ((UT.level n).counit.app P))
    (hUS : ∀ n (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ),
      IsIso ((US.level n).counit.app P)) :
    ∃ e : ∀ n, (US.level n).derived ⋙ (DB.level n).inverse ≅
      (DA.level (index n)).inverse ⋙ (UT.level n).derived,
      (∀ n K,
        (DB.level n).inverse.map ((US.derivedEvaluation n).inv.app K) ≫
          (DB.inverseEvaluation n).inv.app (US.derived.obj K) ≫
          (PTB.evaluation n).map (square.derived.hom.app K) =
        (e n).hom.app ((PSA.evaluation (index n)).obj K) ≫
          (UT.level n).derived.map ((DA.inverseEvaluation (index n)).inv.app K) ≫
          (UT.derivedEvaluation n).inv.app (DA.system.inverse.obj K)) ∧
      (∀ {m n : ℕ} (h : n ≤ m) K,
        (DB.level n).inverse.map ((qS.derived h).hom.app K) ≫
          (DB.derivedTensor h).hom.app ((US.level m).derived.obj K) ≫
          (PTB.scalar h).derived.map ((e m).hom.app K) =
        (e n).hom.app ((PSA.scalar (index.monotone h)).derived.obj K) ≫
          (UT.level n).derived.map
            ((DA.derivedTensor (index.monotone h)).hom.app K) ≫
          (qT.derived h).hom.app ((DA.level (index m)).inverse.obj K)) := by
  classical
  let (n : ℕ) (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ) :
      IsIso ((UT.level n).counit.app P) := hUT n P
  let (n : ℕ) (P : CochainComplex (strictEtaleLevel S O ell (index n)) ℤ) :
      IsIso ((US.level n).counit.app P) := hUS n P
  have hT (n : ℕ) : IsIso (UT.level n).counit := NatIso.isIso_of_isIso_app _
  have hS (n : ℕ) : IsIso (US.level n).counit := NatIso.isIso_of_isIso_app _
  let (n : ℕ) : IsIso (UT.level n).counit := hT n
  let (n : ℕ) : IsIso (US.level n).counit := hS n
  obtain ⟨ordinary, ho⟩ := Classical.axiomOfChoice
    (fun n ↦ strictEtaleFiniteOrdinaryInverseTransport a A B n)
  obtain ⟨e, he⟩ := Classical.axiomOfChoice (fun n ↦
    exists_derivedSquare_independentUniverses
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n))
    (A.lift (index n)).modules (B.lift n).modules
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (US.level n).derived (DA.level (index n)).inverse (DB.level n).inverse
    (UT.level n).derived (asIso (US.level n).counit)
    (DA.level (index n)).inverseFactors (DB.level n).inverseFactors
    (asIso (UT.level n).counit) (ordinary n))
  exact ⟨e,
    derived_evaluation UT US A B DA DB square hUT hUS ordinary ho e he,
    derived_quotient UT US A B DA DB qT qS ordinary ho e he⟩


end AlgebraicGeometry
