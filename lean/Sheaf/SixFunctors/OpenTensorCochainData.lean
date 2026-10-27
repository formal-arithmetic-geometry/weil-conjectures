/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels

/-! # Ordinary input to open tensor descent

Source: Stacks 0E8I, 0GL1, 07A4, 0G7E and Homology 012Z
(blueprint: def-sf-open-tensor-cochain-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
  (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R)
  (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    SemilinearSections.Mod.{c, v, max c v r} J' R')
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G)
  (H : C ⥤ C')
  (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ),
    N.val.obj V → (G.obj N).val.obj (H.op.obj V))

/-- Ordinary and cochain data for an exact open adjunction. No derived tensor is
chosen here. The projection and its total are natural in both variables, and the
ordinary inverse is the specified unit transpose. Source: Stacks 0E8I, 0GL1, 07A4,
0G7E and Homology 012Z (blueprint: def-sf-open-tensor-cochain-data). -/
structure OpenTensorCochainData where
  right : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R
  pullAdjunction : G ⊣ right
  pullTensor : ∀ M N : SemilinearSections.Mod.{c, v, max c v r} J R,
    G.obj (ordinaryTensor.{c, v, r} J R M N) ≅
      ordinaryTensor.{c, v, r} J' R' (G.obj M) (G.obj N)
  pullNaturality : ∀ {M M' N N' : SemilinearSections.Mod.{c, v, max c v r} J R}
    (f : M ⟶ M') (g : N ⟶ N'),
    G.map (ordinaryTensorHom.{c, v, r} J R f g) ≫ (pullTensor M' N').hom =
      (pullTensor M N).hom ≫ ordinaryTensorHom.{c, v, r} J' R' (G.map f) (G.map g)
  pullPure : ∀ (M N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V),
    (pullTensor M N).hom.val.app (H.op.obj V)
        (sectionPull (ordinaryTensor.{c, v, r} J R M N) V
          (tensorSection.{c, v, r} J R M N V x y)) =
      tensorSection.{c, v, r} J' R' (G.obj M) (G.obj N) (H.op.obj V)
        (sectionPull M V x) (sectionPull N V y)
  pullKFlat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R')
      ((G.mapHomologicalComplex (.up ℤ)).obj P)
  pullFlat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    flatTerms.{c, v, r} J' R' ((G.mapHomologicalComplex (.up ℤ)).obj P)
  ordinary : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J' R')
    (N : SemilinearSections.Mod.{c, v, max c v r} J R),
    ordinaryTensor.{c, v, r} J R (F.obj M) N ≅
      F.obj (ordinaryTensor.{c, v, r} J' R' M (G.obj N))
  ordinaryInverse : ∀ M N,
    adj.homEquiv _ _ (ordinary M N).inv =
      ordinaryTensorHom.{c, v, r} J' R' (adj.unit.app M) (𝟙 (G.obj N)) ≫
        (pullTensor (F.obj M) N).inv
  ordinaryNaturality : ∀ {M M' : SemilinearSections.Mod.{c, v, max c v r} J' R'}
    {N N' : SemilinearSections.Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N'),
    ordinaryTensorHom.{c, v, r} J R (F.map f) g ≫ (ordinary M' N').hom =
      (ordinary M N).hom ≫ F.map (ordinaryTensorHom.{c, v, r} J' R' f (G.map g))
  chain : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ),
    (totalTensor.{c, v, r} J R).obj ((F.mapHomologicalComplex (.up ℤ)).obj P, Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj ((totalTensor.{c, v, r} J' R').obj
        (P, (G.mapHomologicalComplex (.up ℤ)).obj Q))
  summand : ∀ P Q (a b k : ℤ) (h : a + b = k),
    tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj P) Q a b k h ≫
        (chain P Q).hom.f k =
      (ordinary (P.X a) (Q.X b)).hom ≫
        F.map (tensorSummand.{c, v, r} J' R' P
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) a b k h)
  chainNaturality : ∀ {P P' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ}
    {Q Q' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q'),
    (totalTensor.{c, v, r} J R).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) g) ≫ (chain P' Q').hom =
      (chain P Q).hom ≫ (F.mapHomologicalComplex (.up ℤ)).map
        ((totalTensor.{c, v, r} J' R').map
          (Prod.mkHom f ((G.mapHomologicalComplex (.up ℤ)).map g)))

end WeilConjectures.CoefSupportOpenTensor
