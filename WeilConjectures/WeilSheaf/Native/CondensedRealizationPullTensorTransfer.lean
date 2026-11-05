/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ComparisonCompatibleOfIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.CategoryTheory.Monoidal.UncurriedComparison
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTensorModels

/-!
# Transfer of the pullback–tensor comparison to condensed modules

Let `h : Z' ⟶ Y'` be a morphism of schemes and `Λ` a commutative condensed ring. Let `G : B_Y ⥤ B_Z`
be an exact functor of abelian categories, carrying derived tensor products `D_Y`, `D_Z` computed on
K-flat models, and a derived pullback–tensor comparison `φ : G(A ⊗ B) ≅ G A ⊗ G B` normalized on
K-flat representatives by a comparison `t` of total tensor complexes. Let `N_Y : B_Y ⥤ Mod_{Λ_Y'}`
and `N_Z : B_Z ⥤ Mod_{Λ_Z'}` be exact *realizations* in condensed `Λ`-modules, carrying K-flat
complexes to K-flat complexes, with derived tensor comparisons `m_Y`, `m_Z` normalized on K-flat
representatives by comparisons of total tensor complexes, and let `u : N_Y ⋙ h^* ≅ G ⋙ N_Z`.

If `u` carries `t` to the comonoidal structure of `h^*` on complexes, then the derived square
`D(N_Y) ⋙ Lh^* ≅ D(G) ⋙ D(N_Z)` carries `φ` to the comparison
`Lh^*(K ⊗ᴸ L) ⟶ Lh^* K ⊗ᴸ Lh^* L` of `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`
(`AlgebraicGeometry.ProEtale.CondensedRing.comparisonCompatible_of_normalized`): this is the
hypothesis `CategoryTheory.Adjunction.ComparisonCompatible` under which projection formulas transfer
along the realizations (`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv`).

The proof is a computation on K-flat representatives, to which every object is isomorphic: there
all comparisons are localizations of chain maps, and the statement reduces to the given
compatibility on complexes. The categories `B_Y`, `B_Z` and the functors are kept abstract, so the
statement can be instantiated with concrete functors (pro-étale Weil sheaves and their
condensed realizations) without the kernel unfolding them.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor

open scoped CategoryTheory.Obj

-- Use Mathlib's Grothendieck instance on module categories, as the native tensor files do.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
/-- Condensed `ℚ̲̄_ℓ`-modules on the geometric fibre of `X`. -/
local notation "𝐂[" X "]" => CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology
  (Scheme.Hom.geometricFiber (X ↘ Spec (CommRingCat.of k₀)))) Ab.{u + 1})
  (condensedRingObj (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiber (X ↘ Spec (CommRingCat.of k₀))))

variable (G : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (N_Y : ProEtaleWeilSheaf k₀ l Y ⥤ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology
      (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀)))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀))))) (N_Z : ProEtaleWeilSheaf k₀ l Z ⥤ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology
      (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))))
  [N_Y.Additive] [PreservesFiniteLimits N_Y] [PreservesFiniteColimits N_Y]
  [N_Z.Additive] [PreservesFiniteLimits N_Z] [PreservesFiniteColimits N_Z]
  (TY : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ ⥤ CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ ⥤ CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
  (TZ : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ ⥤ CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ ⥤ CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
  (DY : DerivedCategory (ProEtaleWeilSheaf k₀ l Y) × DerivedCategory (ProEtaleWeilSheaf k₀ l Y) ⥤ DerivedCategory (ProEtaleWeilSheaf k₀ l Y))
  (DZ : DerivedCategory (ProEtaleWeilSheaf k₀ l Z) × DerivedCategory (ProEtaleWeilSheaf k₀ l Z) ⥤ DerivedCategory (ProEtaleWeilSheaf k₀ l Z))
  (flatY : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ → Prop) (flatZ : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ → Prop)
  (hG : ∀ T, flatY T → flatZ ((G.mapHomologicalComplex (.up ℤ)).obj T))
  (modelY : ∀ P T, flatY P → flatY T →
    (DY.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TY.obj P).obj T)))
  (modelZ : ∀ P T, flatZ P → flatZ T →
    (DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TZ.obj P).obj T)))
  (t : Functor.uncurry.obj TY ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    (G.mapHomologicalComplex (.up ℤ)).prod (G.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj TZ)
  (φ : DY ⋙ G.mapDerivedCategory ≅ G.mapDerivedCategory.prod G.mapDerivedCategory ⋙ DZ)
  (hφ : OpenTensorRestrictionNormalization G TZ TY DZ DY flatZ flatY hG modelZ modelY
    (fun P T ↦ t.app (P, T)) φ)
  (hNY : ∀ P, flatY P → (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
    ((HomotopyCategory.quotient _ (.up ℤ)).obj ((N_Y.mapHomologicalComplex (.up ℤ)).obj P)))
  (hNZ : ∀ P, flatZ P → (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
    ((HomotopyCategory.quotient _ (.up ℤ)).obj ((N_Z.mapHomologicalComplex (.up ℤ)).obj P)))
  (totalY : Functor.uncurry.obj TY ⋙ N_Y.mapHomologicalComplex (.up ℤ) ≅
    (N_Y.mapHomologicalComplex (.up ℤ)).prod (N_Y.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj (curriedTensor _).map₂CochainComplex)
  (totalZ : Functor.uncurry.obj TZ ⋙ N_Z.mapHomologicalComplex (.up ℤ) ≅
    (N_Z.mapHomologicalComplex (.up ℤ)).prod (N_Z.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj (curriedTensor _).map₂CochainComplex)
  (mY : DY ⋙ N_Y.mapDerivedCategory ≅
    N_Y.mapDerivedCategory.prod N_Y.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _))
  (mZ : DZ ⋙ N_Z.mapDerivedCategory ≅
    N_Z.mapDerivedCategory.prod N_Z.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _))
  (hmY : ∀ P T (hP : flatY P) (hT : flatY T),
    mY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      (Functor.uncurry.obj (curriedTensor _)).map
        (Prod.mkHom (N_Y.mapDerivedCategoryFactors.hom.app P)
          (N_Y.mapDerivedCategoryFactors.hom.app T)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q ((N_Y.mapHomologicalComplex (.up ℤ)).obj P)
        ((N_Y.mapHomologicalComplex (.up ℤ)).obj T) =
    N_Y.mapDerivedCategory.map (modelY P T hP hT).hom ≫
      N_Y.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (totalY.app (P, T)).hom)
  (hmZ : ∀ P T (hP : flatZ P) (hT : flatZ T),
    mZ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      (Functor.uncurry.obj (curriedTensor _)).map
        (Prod.mkHom (N_Z.mapDerivedCategoryFactors.hom.app P)
          (N_Z.mapDerivedCategoryFactors.hom.app T)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q ((N_Z.mapHomologicalComplex (.up ℤ)).obj P)
        ((N_Z.mapHomologicalComplex (.up ℤ)).obj T) =
    N_Z.mapDerivedCategory.map (modelZ P T hP hT).hom ≫
      N_Z.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (totalZ.app (P, T)).hom)
  (u : N_Y ⋙ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) ≅ G ⋙ N_Z)

/-- The isomorphism `u : N_Y ⋙ h^* ≅ G ⋙ N_Z` on cochain complexes, degreewise. -/
noncomputable def upperStarComplexIso :
    N_Y.mapHomologicalComplex (.up ℤ) ⋙ ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))).mapHomologicalComplex (.up ℤ) ≅
      G.mapHomologicalComplex (.up ℤ) ⋙ N_Z.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) _ ≪≫
    NatIso.mapHomologicalComplex u _ ≪≫ (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm

variable
    (hC : Functor.whiskerLeft (Functor.uncurry.obj TY) (upperStarComplexIso k₀ l g G N_Y N_Z u).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight t.hom (N_Z.mapHomologicalComplex (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((G.mapHomologicalComplex (.up ℤ)).prod
            (G.mapHomologicalComplex (.up ℤ))) totalZ.hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight totalY.hom (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))).mapHomologicalComplex (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((N_Y.mapHomologicalComplex (.up ℤ)).prod
            (N_Y.mapHomologicalComplex (.up ℤ)))
          (HomologicalComplex.mapBifunctorComparisonUncurried
            (Functor.OplaxMonoidal.δNatTrans ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))))) (.up ℤ)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((Functor.prodCompIso _ _).hom ≫
            NatTrans.prod (upperStarComplexIso k₀ l g G N_Y N_Z u).hom
              (upperStarComplexIso k₀ l g G N_Y N_Z u).hom ≫
            (Functor.prodCompIso _ _).inv)
          (Functor.uncurry.obj (curriedTensor _).map₂CochainComplex) ≫
        (Functor.associator _ _ _).hom)

set_option maxHeartbeats 8000000 in
-- the derived categories of condensed module objects make the unification slow
open DerivedCategory Functor.LaxMonoidal in
include hφ hmZ in
/-- The left side of the compatibility, after the factorizations through `Q` and the lax monoidal
structure of `Q`: the localization of the total comparisons `t` and `totalZ`. -/
lemma comparisonCompatible_aux_left (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : flatY P) (hT : flatY T) :
    N_Z.mapDerivedCategory.map (φ.hom.app (Q.obj P, Q.obj T)) ≫
      mZ.hom.app (G.mapDerivedCategory.obj (Q.obj P), G.mapDerivedCategory.obj (Q.obj T)) ≫
      (Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
        (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
          N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
        (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T) ≫
          N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj T))) ≫
      μ Q ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
        ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj T)) =
    N_Z.mapDerivedCategory.map (G.mapDerivedCategory.map (modelY P T hP hT).hom) ≫
      N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app ((TY.obj P).obj T)) ≫
      N_Z.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj ((TY.obj P).obj T)) ≫
      Q.map ((N_Z.mapHomologicalComplex (.up ℤ)).map (t.hom.app (P, T)) ≫
        (totalZ.app ((G.mapHomologicalComplex (.up ℤ)).obj P,
          (G.mapHomologicalComplex (.up ℤ)).obj T)).hom) := by
  have h₁ : mZ.hom.app (G.mapDerivedCategory.obj (Q.obj P), G.mapDerivedCategory.obj (Q.obj T)) ≫
      (Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
        (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P))
        (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T))) =
      N_Z.mapDerivedCategory.map (DZ.map (Prod.mkHom (G.mapDerivedCategoryFactors.hom.app P)
        (G.mapDerivedCategoryFactors.hom.app T))) ≫
      mZ.hom.app (Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P),
        Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj T)) :=
    (mZ.hom.naturality (Prod.mkHom (G.mapDerivedCategoryFactors.hom.app P)
      (G.mapDerivedCategoryFactors.hom.app T))).symm
  have h₂ := hmZ _ _ (hG P hP) (hG T hT)
  have h₃ := hφ P T hP hT
  have h₄ := N_Z.mapDerivedCategoryFactors_hom_naturality (t.hom.app (P, T))
  have hm : ∀ {A B C A' B' C' : DerivedCategory 𝐂[Z]}
      (a : A ⟶ B) (b : B ⟶ C) (c : A' ⟶ B') (d : B' ⟶ C'),
      (Prod.mkHom (a ≫ b) (c ≫ d) : (A, A') ⟶ (C, C')) = Prod.mkHom a c ≫ Prod.mkHom b d :=
    fun _ _ _ _ ↦ rfl
  have h₃' : N_Z.mapDerivedCategory.map (φ.hom.app (Q.obj P, Q.obj T)) ≫
      N_Z.mapDerivedCategory.map (DZ.map (Prod.mkHom (G.mapDerivedCategoryFactors.hom.app P)
        (G.mapDerivedCategoryFactors.hom.app T))) ≫
      N_Z.mapDerivedCategory.map (modelZ _ _ (hG P hP) (hG T hT)).hom =
      N_Z.mapDerivedCategory.map (G.mapDerivedCategory.map (modelY P T hP hT).hom) ≫
      N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app ((TY.obj P).obj T)) ≫
      N_Z.mapDerivedCategory.map (Q.map (t.hom.app (P, T))) := by
    simp only [← Functor.map_comp]
    exact congrArg N_Z.mapDerivedCategory.map h₃
  rw [hm, Functor.map_comp, Category.assoc, reassoc_of% h₁, h₂]
  have h₄' : N_Z.mapDerivedCategory.map (Q.map (t.hom.app (P, T))) ≫
      N_Z.mapDerivedCategoryFactors.hom.app ((TZ.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj T)) =
      N_Z.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj ((TY.obj P).obj T)) ≫
      Q.map ((N_Z.mapHomologicalComplex (.up ℤ)).map (t.hom.app (P, T))) := h₄
  erw [reassoc_of% h₃']
  rw [reassoc_of% h₄', (DerivedCategory.Q).map_comp]

set_option maxHeartbeats 8000000 in
-- the derived categories of condensed module objects make the unification slow
open DerivedCategory Functor.LaxMonoidal in
include hmY hC in
/-- The right side of the compatibility, after the factorizations through `Q` and the lax monoidal
structure of `Q`: on the images of native K-flat complexes `P`, `T`, the condensed comparison
`Lḡ^*(K ⊗ᴸ L) ⟶ Lḡ^* K ⊗ᴸ Lḡ^* L` (`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`)
applied to the realizations, followed by the derived square `α` in both variables, is `α` followed
by the localization of the total comparisons `t` and `totalZ`.

Mathematically: `α` is the counit of `Lḡ^*` followed by `u` on complexes
(`CategoryTheory.Functor.leftDerivedFunctorSquareIso_hom_app_Q_obj`); the comparison of `Lḡ^*` is
the counit followed by the comonoidal structure of `ḡ^*` on complexes
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_app_app_fac`); the realization
`m_Y` is the localization of `totalY` (`hmY`); and `u` carries `totalY` to `t` and `totalZ`
(`hC`). This is a computation in the derived category of condensed module objects; it is not yet
formalized, because the identification of the tensor product of complexes with the tensor product
in the homotopy category, needed to read
`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_app_app_fac` through
`DerivedCategory.Q`, goes through definitions that are not exposed to this file. -/
lemma comparisonCompatible_aux_right (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : flatY P) (hT : flatY T) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
        (mY.hom.app (Q.obj P, Q.obj T)) ≫
      ((CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).app
          (N_Y.mapDerivedCategory.obj (Q.obj P))).app (N_Y.mapDerivedCategory.obj (Q.obj T)) ≫
      (Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
        ((Functor.leftDerivedFunctorSquareIso u).hom.app (Q.obj P) ≫
          N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
          N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
        ((Functor.leftDerivedFunctorSquareIso u).hom.app (Q.obj T) ≫
          N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T) ≫
          N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj T))) ≫
      μ Q ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
        ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj T)) =
    (Functor.leftDerivedFunctorSquareIso u).hom.app (DY.obj (Q.obj P, Q.obj T)) ≫
      N_Z.mapDerivedCategory.map (G.mapDerivedCategory.map (modelY P T hP hT).hom) ≫
      N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app ((TY.obj P).obj T)) ≫
      N_Z.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj ((TY.obj P).obj T)) ≫
      Q.map ((N_Z.mapHomologicalComplex (.up ℤ)).map (t.hom.app (P, T)) ≫
        (totalZ.app ((G.mapHomologicalComplex (.up ℤ)).obj P,
          (G.mapHomologicalComplex (.up ℤ)).obj T)).hom) :=
  sorry


set_option maxHeartbeats 8000000 in
-- the derived categories of condensed module objects make the unification slow
open DerivedCategory Functor.LaxMonoidal in
include hφ hNY hNZ hmY hmZ hC in
/-- **Transfer of the pullback–tensor comparison to condensed modules.** If the isomorphism
`u : N_Y ⋙ h^* ≅ G ⋙ N_Z` carries the total comparison `t` to the comonoidal structure of `h^*`
on complexes (`hC`), then the derived square `D(N_Y) ⋙ Lh^* ≅ D(G) ⋙ D(N_Z)` carries the derived
comparison `φ` to `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`, up to the
realizations `m_Y`, `m_Z` of the derived tensor products. -/
theorem comparisonCompatible_of_normalized
    [((ObjectProperty.ι flatY) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l Y) (.up ℤ)).inverseImage (ObjectProperty.ι flatY))]
 :
    Adjunction.ComparisonCompatible (Functor.leftDerivedFunctorSquareIso u)
      (Functor.curryCompIsoOfIso φ).hom (CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (Functor.curryCompIsoOfIso' mZ) (Functor.curryCompIsoOfIso' mY) := by
  refine Adjunction.comparisonCompatible_of_iso _ _ _ _ _
    (fun a ↦ ∃ P, flatY P ∧ a = DerivedCategory.Q.obj P) (fun a ↦ ?_) ?_
  · let L := ObjectProperty.ι flatY ⋙ DerivedCategory.Q
    have : L.EssSurj := Localization.essSurj L
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l Y) (.up ℤ)).inverseImage (ObjectProperty.ι flatY))
    exact ⟨_, ⟨(L.objPreimage a).1, (L.objPreimage a).2, rfl⟩, ⟨(L.objObjPreimageIso a).symm⟩⟩
  rintro _ _ ⟨P, hP, rfl⟩ ⟨T, hT, rfl⟩
  have hL := comparisonCompatible_aux_left (hφ := hφ) (hmZ := hmZ) (P := P) (T := T) (hP := hP)
    (hT := hT)
  have hR := comparisonCompatible_aux_right (hmY := hmY) (hC := hC) (P := P) (T := T) (hP := hP)
    (hT := hT)
  have hμ := DerivedCategory.isIso_μ_Q_of_kFlat
    ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj T))
    (hNZ _ (hG P hP))
  have hU : IsIso ((Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
      (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
      (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T) ≫
        N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj T)))) := by
    change IsIso (_ ▷ _ ≫ _ ◁ _)
    infer_instance
  rw [← cancel_mono ((Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
      (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
      (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T) ≫
        N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj T))) ≫
    μ Q ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
      ((N_Z.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj T)))]
  refine ((Category.assoc _ _ _).trans hL).trans ?_
  have hm : ∀ {A B C A' B' C' : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology
      (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))))}
      (a : A ⟶ B) (b : B ⟶ C) (c : A' ⟶ B') (d : B' ⟶ C'),
      (Prod.mkHom (a ≫ b) (c ≫ d) : (A, A') ⟶ (C, C')) = Prod.mkHom a c ≫ Prod.mkHom b d :=
    fun _ _ _ _ ↦ rfl
  have hcomb : (Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
      ((Functor.leftDerivedFunctorSquareIso u).hom.app (Q.obj P) ≫
        N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
      ((Functor.leftDerivedFunctorSquareIso u).hom.app (Q.obj T) ≫
        N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T) ≫
        N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj T))) =
      ((curriedTensor _).map ((Functor.leftDerivedFunctorSquareIso u).hom.app (Q.obj P))).app _ ≫
      ((curriedTensor _).obj _).map ((Functor.leftDerivedFunctorSquareIso u).hom.app (Q.obj T)) ≫
      (Functor.uncurry.obj (curriedTensor _)).map (Prod.mkHom
        (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
          N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
        (N_Z.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app T) ≫
          N_Z.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj T))) := by
    rw [hm, Functor.map_comp]
    exact Category.assoc _ _ _
  simp only [Functor.curryCompIsoOfIso'_hom_app_app, Category.assoc]
  erw [← reassoc_of% hcomb, hR, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtaleWeilSheaf
