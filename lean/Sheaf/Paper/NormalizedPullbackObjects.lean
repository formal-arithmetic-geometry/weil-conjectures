/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.AdicFibreComparisonCoherence

/-! # Objectwise normalized pullback of geometric fibres

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Remark 6.8.15;
Stacks Tag 03Q1(3) (blueprint: lem-per-normalized-pullback-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- Objectwise comparison data with the prescribed integral local models. No naturality,
identity or composition equation is included here.
Source: BS 6.8.4(1),(4),(6), Remark 6.8.15; Stacks 03Q1(3).
(blueprint: lem-per-normalized-pullback-objects). -/
structure ObjectwiseNormalizedPullback (ω : Fibres (k := k) l R) where
  component : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
    (F : NormalizedFibre.Heart l A (base l X)),
    ((ω A Y).point κ y).functor.obj ((heartPull l A R g).obj F) ≅
      ((ω A X).point κ (y ≫ g)).functor.obj F
  unit_normalization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l A (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme A))
    (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M),
    ∃ e' : (R.realization A (base l Y)).J.obj ((heartPull l A R g).obj F).obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((modulePull g (R.along A (X := base l Y) (Y := base l X) g).coefficient).obj M),
      e'.hom = pullModelMap l R A g F M e ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (U : X.scheme.ProEt)
        (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange (y ≫ g)).obj U)
        (q' : ProEt.mk (𝟙 (Spec (.of κ))) ⟶
          (proEtaleBaseChange y).obj ((proEtaleBaseChange g).obj U))
        (_hq : q.left ≫ pullback.fst U.hom (y ≫ g) =
          q'.left ≫ pullback.fst ((proEtaleBaseChange g).obj U).hom y ≫
            pullback.fst U.hom g) (m : M.val.obj (op U)),
        (presentedFibre l R A ω X F M e κ (y ≫ g)).hom
          (((component A g κ y F).hom)
            ((presentedFibre l R A ω Y ((heartPull l A R g).obj F) _ e' κ y).inv
              (germ l A _ κ y ((proEtaleBaseChange g).obj U) q'
                (moduleUnit g (R.along A (X := base l Y) (Y := base l X) g).coefficient
                  M U m)))) = germ l A M κ (y ≫ g) U q m
  local_normalization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l A (base l X)) (C : NormalizedFibre.Chart l (base l X))
    (hC : C.Adapted l A (R.realization A (base l X)) F)
    (N : NormalizedFibre.Lattice l A C.scheme)
    (φ : (C.restrict l A (R.realization A (base l X))).obj F ≅ N.rational l A)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
    (s : Spec (.of κ) ⟶ C.scheme) (hs : s ≫ C.map = y ≫ g)
    (W₀ : (pullback g C.map).affineOpens)
    (t₀ : Spec (.of κ) ⟶ W₀.1.toScheme)
    (_ht₀ : t₀ ≫ W₀.1.ι = pullback.lift y s hs.symm),
    ∃ (D : NormalizedFibre.Chart l (base l Y)) (f : D.scheme ⟶ C.scheme)
      (t : Spec (.of κ) ⟶ D.scheme) (i₀ : D.scheme ≅ W₀.1.toScheme)
      (hD : D.Adapted l A (R.realization A (base l Y)) ((heartPull l A R g).obj F))
      (M : NormalizedFibre.Lattice l A D.scheme)
      (ψ : (D.restrict l A (R.realization A (base l Y))).obj
        ((heartPull l A R g).obj F) ≅ M.rational l A)
      (hsystem : M.system = N.system ⋙ Etale.upperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)) f)
      (q : (D.restrict l A (R.realization A (base l Y))).obj
        ((heartPull l A R g).obj F) ≅
          (modulePull f (NormalizedFibre.coefficient l A f)).obj
            ((C.restrict l A (R.realization A (base l X))).obj F))
      (η : (modulePull f (NormalizedFibre.coefficient l A f)).obj
        (N.rational l A) ≅ M.rational l A)
      (P : PullLimit l A f N M κ t
        (pullTowerIso l A f N M (eqToIso hsystem) κ t)),
      D.map = i₀.hom ≫ W₀.1.ι ≫ pullback.fst g C.map ∧
      f = i₀.hom ≫ W₀.1.ι ≫ pullback.snd g C.map ∧ t ≫ i₀.hom = t₀ ∧
      D.map ≫ g = f ≫ C.map ∧ t ≫ D.map = y ∧ t ≫ f = s ∧
      (∃ (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((NormalizedFibre.realize l A (base l X) (R.realization A (base l X))).obj F))
    (e' : (R.realization A (base l Y)).J.obj ((heartPull l A R g).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((modulePull g (R.along A (X := base l Y) (Y := base l X) g).coefficient).obj
          ((NormalizedFibre.realize l A (base l X) (R.realization A (base l X))).obj F))),
    ((DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).hom = 𝟙 _ ∧
    e'.hom = pullModelMap l R A g F _ e ∧
    ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ D.scheme)
      (W : X.scheme.ProEt)
      (a : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange t).obj
        ((proEtaleBaseChange D.map).obj ((proEtaleBaseChange g).obj W)))
      (b : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange t).obj
        ((proEtaleBaseChange f).obj ((proEtaleBaseChange C.map).obj W)))
      (_hab : a.left ≫ pullback.fst _ t ≫ pullback.fst _ D.map ≫ pullback.fst W.hom g =
        b.left ≫ pullback.fst _ t ≫ pullback.fst _ f ≫ pullback.fst W.hom C.map)
      (m : ((NormalizedFibre.realize l A (base l X)
        (R.realization A (base l X))).obj F).val.obj (op W)),
      (NormalizedFibre.ambient l A κ t).map q.hom
        (germ l A _ κ t _ a
          (moduleUnit D.map (NormalizedFibre.coefficient l A D.map) _ _
            (((DerivedCategory.homologyFunctor _ 0).mapIso e' ≪≫
                (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).inv.val.app
                  (op ((proEtaleBaseChange g).obj W))
              (moduleUnit g (R.along A (X := base l Y) (Y := base l X) g).coefficient
                _ W m)))) =
        germ l A _ κ t _ b (moduleUnit f (NormalizedFibre.coefficient l A f) _ _
          (moduleUnit C.map (NormalizedFibre.coefficient l A C.map) _ W m))) ∧
      (∃ δ : (NormalizedFibre.forgetIntegral l A C.scheme).obj N.integral ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((NormalizedFibre.forgetIntegral l A D.scheme).obj M.integral),
    (∀ n : ℕ, δ ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        (M.reduction.app (op n)) = N.reduction.app (op n) ≫
      ((supportSiteProEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).inv.app _ ≫
          (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} D.scheme).map
            ((supportSiteEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
              |>.symm
        ((sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map
          ((supportSiteEtaleComparisonAdjunction
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)) f).unit.app
              (N.system.obj (op n))) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
            ((sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map
              ((eqToIso hsystem).inv.app (op n)))))))) ∧
    ∀ (W : C.scheme.ProEt) (m : N.integral.val.obj (op W)),
      η.hom.val.app (op ((proEtaleBaseChange f).obj W))
        (moduleUnit f (NormalizedFibre.coefficient l A f) (N.rational l A) W
          (pbcTensorSection (integralRationalCoefficientMap l A C.scheme) N.integral
            (op W) 1 m)) =
        pbcTensorSection (integralRationalCoefficientMap l A D.scheme) M.integral
          (op ((proEtaleBaseChange f).obj W)) 1 (δ.hom.app (op W) m)) ∧
      ψ.hom = q.hom ≫ (modulePull f (NormalizedFibre.coefficient l A f)).map φ.hom ≫
        η.hom ∧
      HEq ((component A g κ y F).hom)
        (((ω A Y).normalization D ((heartPull l A R g).obj F) hD M ψ κ t).hom ≫
          (ModuleCat.extendScalars.{u, u, u + 1}
            (Padic.coefficientExtensionIntegers l A).subtype).map
            P.iso.hom ≫
          ((ω A X).normalization C F hC N φ κ (t ≫ f)).inv)

/-- Objectwise normalized pullback comparisons exist.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Remark 6.8.15; Stacks 03Q1(3).
(blueprint: lem-per-normalized-pullback-objects).

Proof: choose the intrinsic normalized fibres from normalized fibre exactness, retaining
its intrinsic local-lattice comparisons. Realization and its specified derived counit
identify completed pullback on a heart object with ordinary module pullback in degree
zero. On a pulled finite-free chart this is the balanced tensor map, so it is invertible,
including rank zero. Compose module inverse images to the geometric point, evaluate at
the final object, and use the intrinsic identifications to define each component.
For an arbitrary degree-zero presentation the same counit and its naturality give the
unit_normalization equation on every section germ. For a specified adapted chart, pull
its stratification back, then restrict to the chosen affine open W₀. Use W₀ itself for
the chart scheme; its etale map is the base change of the original etale chart restricted
to W₀. The two projections give f and the lifted point, with the six geometric equations
by the pullback universal property. The lisse completed-system equivalence reconstructs
M from the literal pulled reduction system. Its reduction cone is the finite inverse-image
unit mate, giving δ; balanced rationalization gives η and its integral-section equation.
The restriction comparison q is obtained from the same counit; composition of its units
gives the displayed germ equation. Set ψ to q followed by pullback of φ and η.
At each positive reduction level the stalk comparison sends the germ of a pulled section
to the original germ and commutes with transitions. Apply limit.mapIso to that tower
isomorphism; limit.map_π gives PullLimit.projection. Rationalize and use the chosen
intrinsic lattice normalizations. This is the component already constructed, since both
are obtained by pulling the reductions to the point before taking their limit. This proves
local_normalization on every specified affine open, without commuting stalks and limits.
Identity, composition, and naturality of these objectwise components are separate steps. -/
theorem objectwise_normalized_fibre_pullback :
    ∃ ω : Fibres (k := k) l R, Nonempty (ObjectwiseNormalizedPullback l R ω) := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
