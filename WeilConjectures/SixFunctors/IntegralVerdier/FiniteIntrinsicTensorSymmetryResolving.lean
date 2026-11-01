/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteScalarSignedRepresentativeSquare
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealizationNormalization
import WeilConjectures.SixFunctors.Supporting.FixedCoefficientRepresentativeBraiding

/-! # Resolving representative part of finite intrinsic tensor symmetry

This is the flat-term K-flat representative calculation used by the intrinsic
symmetry theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-! The instance and transparency settings below serve the proof only. They are scoped to this
section so that the public statement keeps its published elaboration. -/
section ResolvingProof

set_option synthInstance.maxSize 4096

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor
attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CategoryTheory.Equivalence.mapDerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

private theorem mapped_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} {a : A ⟶ B} {b : B ⟶ D'} {c : A ⟶ C'} {d : C' ⟶ D'}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem inverse_square
    {D : Type*} [Category D] {A B C E : D}
    (t : A ≅ B) (t' : C ≅ E) (b : A ⟶ C) (s : B ⟶ E)
    (h : b ≫ t'.hom = t.hom ≫ s) : t.inv ≫ b = s ≫ t'.inv := by
  apply (cancel_epi t.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply (cancel_mono t'.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem paste_inverse_middle
    {D : Type*} [Category D] {A B C E G H I J : D}
    (r : A ≅ B) (r' : C ≅ E) (t : B ≅ G) (t' : E ≅ H)
    (g : G ≅ I) (g' : H ≅ J)
    {b : B ⟶ E} {f : A ⟶ C} {m : A ⟶ I} {m' : C ⟶ J}
    {s : G ⟶ H} {s' : I ⟶ J}
    (hsource : r.hom ≫ b = f ≫ r'.hom)
    (hn : r.hom ≫ t.hom ≫ g.hom = m)
    (hn' : r'.hom ≫ t'.hom ≫ g'.hom = m')
    (hmiddle : f ≫ m' = m ≫ s') (hnat : g.hom ≫ s' = s ≫ g'.hom) :
    t.inv ≫ b = s ≫ t'.inv := by
  apply inverse_square t t' b s
  apply (cancel_epi r.hom).1
  apply (cancel_mono g'.hom).1
  simp only [Category.assoc]
  calc
    r.hom ≫ b ≫ t'.hom ≫ g'.hom = f ≫ (r'.hom ≫ t'.hom ≫ g'.hom) := by
      rw [← Category.assoc r.hom b, hsource, Category.assoc]
    _ = f ≫ m' := by rw [hn']
    _ = m ≫ s' := hmiddle
    _ = (r.hom ≫ t.hom ≫ g.hom) ≫ s' := by rw [hn]
    _ = r.hom ≫ t.hom ≫ s ≫ g'.hom := by rw [Category.assoc, Category.assoc, hnat]

/-- The resolving square, elaborated with the proof's instance settings. -/
private theorem finiteIntrinsicTensorSymmetry_resolving_aux
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (hs : ∀ (K L K' L' : proEtaleDerivedCategory X B)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (b : CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) ≅
      (CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))).flip)
    (hb : ∀ K L, HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding'
        (DerivedCategory.Qh (C := Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
        (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (.up ℤ)) K L).hom)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    (finiteIntrinsicTensorRealization X B a).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (sfIntrinsicDerivedEquivalence X B).functor.map
        ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
    (s.swap ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj P))
      ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj Q))).hom ≫
      (finiteIntrinsicTensorRealization X B a).hom.app
        (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) := by
  let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
  let F := (sfIntrinsicDerivedEquivalence X B).functor
  let e := (sfIntrinsicModuleEquivalence X B).functor.mapDerivedCategoryFactors
  let r := finiteScalarRepresentativeTensorIso
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
    (finiteScalarFlatRepresentatives X B) (finiteScalarFlatRepresentatives_kFlat X B)
  let p : (finiteScalarFlatRepresentatives X B).FullSubcategory := ⟨P, hP⟩
  let q : (finiteScalarFlatRepresentatives X B).FullSubcategory := ⟨Q, hQ⟩
  exact paste_inverse_middle
    (F.mapIso (r.app (p, q))) (F.mapIso (r.app (q, p)))
    ((finiteIntrinsicTensorRealization X B a).symm.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    ((finiteIntrinsicTensorRealization X B a).symm.app
      (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
    (a.tensor.mapIso (Iso.prod (e.app P) (e.app Q)))
    (a.tensor.mapIso (Iso.prod (e.app Q) (e.app P)))
    (mapped_square F (finiteScalarFixedRepresentativeSwap X B b hb P Q hP hQ))
    (intrinsic_realization_normalization X B a P Q hP hQ)
    (intrinsic_realization_normalization X B a Q P hQ hP)
    (finiteScalarSignedRepresentativeSquare X B a s P Q hP hQ)
    (hs _ _ _ _ (e.hom.app P) (e.hom.app Q))

end ResolvingProof

/-- The signed tensor square commutes on the chosen flat-term K-flat representatives.

Source: the first two proof steps of
`lem-sf-finite-intrinsic-tensor-symmetry`; Stacks Project, Tags 00YV, 06YL and 0FPT.
The proof is the normalized pure-tensor calculation: finite scalar representative
normalization identifies the realization with the total tensor model, and the
representative equation of `s` and the `hb` normalization identify both swaps.
(blueprint: lem-sf-finite-intrinsic-tensor-symmetry-resolving).
-/
theorem finiteIntrinsicTensorSymmetry_resolving
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (hs : ∀ (K L K' L' : proEtaleDerivedCategory X B)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (b : CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) ≅
      (CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))).flip)
    (hb : ∀ K L, HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding'
        (DerivedCategory.Qh (C := Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
        (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (.up ℤ)) K L).hom)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    (finiteIntrinsicTensorRealization X B a).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (sfIntrinsicDerivedEquivalence X B).functor.map
        ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
    (s.swap ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj P))
      ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj Q))).hom ≫
      (finiteIntrinsicTensorRealization X B a).hom.app
        (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) :=
  finiteIntrinsicTensorSymmetry_resolving_aux X B a s hs b hb P Q hP hQ

end WeilConjectures.IntegralVerdier
