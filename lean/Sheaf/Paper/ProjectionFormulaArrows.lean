/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
public import Sheaf.Paper.StrictPerfectCoefficientPackage
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SplitPerfectTensorKInjective

/-!
# Projection-formula arrows and their specified finite-total inverse

Source: Weil conjectures blueprint, proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
-/

@[expose] public section

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive] (adj : L ⊣ V)
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

/-- The ordinary counit mate t_{M,P}.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionMate (M : B) (P : A) :
    V.obj M ⊗ P ⟶ V.obj (M ⊗ L.obj P) :=
  adj.homEquiv _ _ ((e (V.obj M) P).hom ≫ (adj.counit.app M ⊗ₘ 𝟙 (L.obj P)))

/-- For finite free coefficients the ordinary mate is the finite-product comparison.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: the unit equation reduces the mate in rank one to the identity by the
adjunction triangle identity. Naturality and additivity identify rank N with the
N-fold finite-sum map. Finite sums are products and the right adjoint preserves
products, including the empty product. Thus the comparison is invertible. -/
theorem tensorAdjunctionMate_free_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (N : ℕ) :
    IsIso (tensorAdjunctionMate L V adj e M (∏ᶜ fun _ : Fin N ↦ 𝟙_ A)) := sorry

/-- The specified free inverse q_{M,N}, the inverse of t and not an arbitrary map.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionFreeInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (N : ℕ) :=
  @inv _ _ _ _ (tensorAdjunctionMate L V adj e M (∏ᶜ fun _ : Fin N ↦ 𝟙_ A))
    (tensorAdjunctionMate_free_isIso L V adj e he j hj M N)

/-- The displayed splitting formula for s_{a,r}, equally for any single retract.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionRetractInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (P : A) (N : ℕ)
    (i : P ⟶ ∏ᶜ fun _ : Fin N ↦ 𝟙_ A)
    (p : (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ⟶ P) :
    V.obj (M ⊗ L.obj P) ⟶ V.obj M ⊗ P :=
  V.map (𝟙 M ⊗ₘ L.map i) ≫ tensorAdjunctionFreeInverse L V adj e he j hj M N ≫
    (𝟙 (V.obj M) ⊗ₘ p)

/-- The chain mate whose degree maps are the sums of the ordinary t_{I^a,F^r}.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionTotal
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      F (curriedTensor A) ⟶
    (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor I ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (curriedTensor B)) := by
  letI := tensorPullbackTotal_isIso L e he V adj
    ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _
    (inv (tensorPullbackTotal L e he
      ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F) ≫
        HomologicalComplex.mapBifunctorMap
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)
          (𝟙 ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
          (curriedTensor B) (ComplexShape.up ℤ))

/-- Bounded split-free coefficients make the total mate an isomorphism of complexes.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: in bidegree (a,r) the splitting formula is inverse to t. The two identities
follow by naturality of t at i_r,p_r, their splitting relation, and the inverse
identities of q. Multiplying naturality by these inverses proves compatibility
with each differential; their indices agree and so do the signs (-1)^a.
There are finitely many nonzero summands in each degree. The right adjoint preserves
these finite sums, so the degree maps of the total mate are invertible. -/
theorem tensorAdjunctionTotal_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :
    IsIso (tensorAdjunctionTotal L V adj e he I F) := sorry

/-- The finite-total chain inverse, determined uniquely by the forward chain map.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionTotalInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :=
  @inv _ _ _ _ (tensorAdjunctionTotal L V adj e he I F)
    (tensorAdjunctionTotal_isIso L V adj e he j hj I F hbounded N i p hsplit)

/-- The inverse just constructed has exactly the summand formula required by definition 1264.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: precompose the total inverse identity with the (a,r) coprojection.
The ordinary retract formula is inverse to the corresponding t. Cancel that
invertible t; the remaining equality is the displayed summand formula. The
finite-product identification for V is characterized by these same coprojections. -/
theorem tensorAdjunctionTotalInverse_summand
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) (a r n : ℤ) (h : a + r = n) :
    V.map (CochainComplex.ιMapBifunctor I
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) (curriedTensor B) a r n h) ≫
        (tensorAdjunctionTotalInverse L V adj e he j hj I F hbounded N i p hsplit).f n =
      tensorAdjunctionRetractInverse L V adj e he j hj (I.X a) (F.X r) (N r) (i r) (p r) ≫
        CochainComplex.ιMapBifunctor
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F (curriedTensor A) a r n h :=
  sorry

/-- The target tensor total is K-injective for the specified bounded split-free package.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: additivity transports the bounded support and each splitting through L.
The unit isomorphism j and finite-sum preservation identify L of a finite free
object with a finite free object. Hence L(F) is bounded split-free. Dualize its
finite free retracts termwise: evaluation identifies tensoring with L(F) with
Hom from its bounded dual, with the usual signed differential. That dual is
K-flat. Hom from a K-flat complex into K is K-injective, yielding the claim
(lem-weil-pbc-split-perfect-tensor-kinjective). -/
theorem tensorAdjunctionTotal_target_isKInjective
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (K : CochainComplex B ℤ) (hK : K.IsKInjective) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :
    (CochainComplex.mapBifunctor K
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) (curriedTensor B)).IsKInjective :=
  sorry

end CategoryTheory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- The uncurried presentation of the existing right-adjoint projection map.
This only transports the bifunctor interface; the mate itself is the upstream
`CategoryTheory.Adjunction.rightAdjointProjectionMap`.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaMate
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (F : A) :
    TR.obj (V.obj E, F) ⟶ V.obj (TS.obj (E, L.obj F)) :=
  ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TS)
    (T_D := Functor.curry.obj TR)
    (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L TS).hom)).app E).app F

/-- The derived free-coefficient inverse rho_N, inverting the specified projection mate.
The isomorphism instance is the finite-sum identification, proved from preservation
of finite products in the free-coefficient case.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaFreeInverse
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (Free : A)
    [IsIso (derivedProjectionFormulaMate L V adj TR TS alpha E Free)] :
    V.obj (TS.obj (E, L.obj Free)) ⟶ TR.obj (V.obj E, Free) :=
  inv (derivedProjectionFormulaMate L V adj TR TS alpha E Free)

/-- The displayed derived splitting formula rho_{F^r}.
At a sheaf coefficient term the objects and maps here are their degree-zero
images in the derived category. The formula has no arbitrary inverse-map argument.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaRetractInverse
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (P Free : A)
    (i : P ⟶ Free) (p : Free ⟶ P)
    [IsIso (derivedProjectionFormulaMate L V adj TR TS alpha E Free)] :
    V.obj (TS.obj (E, L.obj P)) ⟶ TR.obj (V.obj E, P) :=
  V.map (TS.map (CategoryTheory.Prod.mkHom (𝟙 E) (L.map i))) ≫
    derivedProjectionFormulaFreeInverse L V adj TR TS alpha E Free ≫
      TR.map (CategoryTheory.Prod.mkHom (𝟙 (V.obj E)) p)

end CategoryTheory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
  (PR : ObjectProperty (CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ))
  (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
  (TR : DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) × DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
  (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
    ((@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) _ (monoidalCategory R)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
        ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)

include hPR in
set_option synthInstance.maxSize 2048 in
/-- The canonical tensor representative when just the coefficient factor is K-flat.
The square specifies the comparison on every K-flat resolution of the first factor.
Source: definition 1264, the displayed representations C and J
(blueprint: def-weil-pbc-projection-formula-arrows).
Proof: choose a K-flat flat-term resolution P to A. Since F is K-flat, total tensor
of that resolution with F is a quasi-isomorphism. Compose the inverse representative
comparison rR with its image under Q and the inverse image of the resolution under
TR. Common refinements of resolutions and naturality of rR give the stated square
for every resolution. Its left factor is invertible, so it also proves uniqueness. -/
theorem mixedTensorRepresentative_existsUnique
    (A F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hf : PR F) :
    ∃! z : TR.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor A F (@curriedTensor (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _ (monoidalCategory R))),
      ∀ (P : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hp : PR P) (p : P ⟶ A), QuasiIso p →
        TR.map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj F))) ≫ z.hom =
          (rR.inv.app (⟨P, hp⟩, ⟨F, hf⟩)) ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap p (𝟙 F)
              (@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ (monoidalCategory R)) (ComplexShape.up ℤ)) := sorry

set_option synthInstance.maxSize 2048 in
/-- The mixed tensor comparison is chosen from a unique, fully specified representative square.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def mixedTensorRepresentative
    (A F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hf : PR F) :=
  Classical.choose (mixedTensorRepresentative_existsUnique R PR hPR TR rR A F hf).exists

/-- A bounded strict-perfect package is K-flat with flat terms.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: each term is a retract of its finite free sheaf by the package splitting.
Tensoring it is a retract of a finite sum of the identity functor, hence exact.
Thus each term is flat. The bounded-above flat K-flat theorem applies to the upper
bound supplied by boundedness, giving the first conclusion. -/
theorem StrictPerfectCoefficientPackage.isKFlat_flat
    (F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (P : StrictPerfectCoefficientPackage ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R) F)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    F.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (F.X n).IsFlat := sorry

end SheafOfModules

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- The definition keeps all ordinary and derived representative identifications explicit.
/-- The pair (pi,rho) of definition 1264 on arbitrary small ringed sites.
Source: proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
The site morphism is uInv adjoint to uPush, with inverse-image lift I and ring map c.
The object and map equations specify ordinary module pullback uStar; am is its ordinary
module adjunction. LF,epsilon,computeL specify derived pullback; TR,TS,rR,rS specify
derived tensor. RF,eta,hRF,computeR specify the K-injective total right derived functor.
canonicalAdj fixes the derived adjunction from the ordinary one on K-injective objects.
P is the degreewise splitting package and hbounded is its finite support. K with repE
is the chosen K-injective representative. None of the ordinary or derived comparisons
is an arbitrary natural isomorphism: k has its generalized pure-tensor characterization,
alpha is selected from its unique representative square, and both mixed tensor
representatives are selected from unique resolution squares.
The first component is the explicit counit mate. The second is Q(s) between the canonical
representatives C and B. s is the inverse of the finite-total ordinary mate; the theorem
tensorAdjunctionTotalInverse_summand states its precise splitting formula on every (a,r)
summand, hence identifies it with the finite-total chain map specified in the source.
The inverse is determined uniquely, so no unconstrained data is chosen from existence. -/
noncomputable def ringedProjectionFormulaArrows
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V)
    [V.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)))
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : ∀ G : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)),
      Function.Bijective (fun b : RF ⟶ G ↦ eta ≫ Functor.whiskerLeft DerivedCategory.Qh b))
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        IsIso (derivedPullbackComplexComparison uStar LF epsilon P))
    (adjD : LF ⊣ RF)
    (canonicalAdj : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      LF.map (derivedPushforwardComplexComparison V RF eta K) ≫
          adjD.counit.app (DerivedCategory.Q.obj K) =
        derivedPullbackComplexComparison uStar LF epsilon
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((am.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))) (K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ) (hK : K.IsKInjective)
    (repE : E ≅ DerivedCategory.Q.obj K)
    (F : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ)
    (P : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) F)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    (TR.obj (RF.obj E, DerivedCategory.Q.obj F) ⟶
      RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F)))) ×
    (RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ⟶
      TR.obj (RF.obj E, DerivedCategory.Q.obj F)) := by
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  have _ := hRF
  have _ := canonicalAdj
  let hf := StrictPerfectCoefficientPackage.isKFlat_flat R F P hbounded
  let hfR : PR F := (hPR F).mpr hf
  let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let pullF := (uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let J := CochainComplex.mapBifunctor K pullF (curriedTensor (SheafOfModules.{u} ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
  let hfS : PS pullF := (hPS pullF).mpr
    ((ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
      hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).1 F hf.1 hf.2)
  let unitData := canonicalRingedTensorComparison_unit R S RI uInv I c uStar hobj hmap k
  let j := Classical.choose unitData.exists
  have hj := (Classical.choose_spec unitData.exists)
  let s := tensorAdjunctionTotalInverse uStar V am k.mu k.naturality j hj K F
    hbounded P.N P.i P.p P.splitting
  let eF : LF.obj (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj pullF :=
    @asIso _ _ _ _ (derivedPullbackComplexComparison uStar LF epsilon F)
      (computeL F hf.1 hf.2)
  let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
    (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)).symm
  let eC : TR.obj (RF.obj E, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F (curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) :=
    TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A F hfR
  have hJ : J.IsKInjective := tensorAdjunctionTotal_target_isKInjective uStar j K hK F
    hbounded P.N P.i P.p P.splitting
  let eB : RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    RF.mapIso (TS.mapIso (Iso.prod repE eF) ≪≫
      mixedTensorRepresentative S PS hPS TS rS K pullF hfS) ≪≫
        (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta J) (computeR J hJ)).symm
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  exact ⟨derivedProjectionFormulaMate LF RF adjD TR TS alpha E (DerivedCategory.Q.obj F),
    eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv⟩

end SheafOfModules
