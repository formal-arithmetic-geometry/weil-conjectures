/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Tensor compatibility of the universal pullback counit

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-counit-coordinate-equation).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.isGrothendieckAbelian

/-- The shared pullback counit is compatible with the localization tensor maps,
without a K-flatness assumption on either argument. The chain comparison is
specified on every tensor summand, so its underlying map is uniquely determined.

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
Proof: first suppose both complexes are K-flat. The canonical comparison predicate
supplies a chain isomorphism and its coordinate equation. The prescribed equations
on the coproduct summands determine the chain map uniquely: apply the inverse of
one comparison and check the resulting endomorphism on every tensor summand. The
invertible module tensor comparison cancels, giving the identity on each summand.
Thus that coordinate equation holds for the specified comparison.
For arbitrary P and G, choose K-flat resolutions P0 -> P and G0 -> G, as in Stacks
06YS. Their images under Q are isomorphisms. The localization tensor map is natural
in both factors. Pullback of the total tensor complex has the chain comparison
specified by the module tensor isomorphisms; its summand equations and module
naturality show that it too is natural in both factors. Naturality of the shared
counit applies to the tensor resolution map and to each separate resolution map.
Write r:P0 -> P, s:G0 -> G, t=Tot(r tensor s), and
v=Tot(k*r tensor k*s). For the comparison phi0 at P0,G0, the summand equations give
k*(t);phi = phi0;v. Put d=Lk*(Qr tensor Qs). Naturality of the localization map
and of the counit gives
  d;Lk*(mu(P,G));epsilon(H);Q(phi)
    = Lk*(mu(P0,G0));epsilon(H0);Q(phi0);Q(v).
Naturality of tau, the two factor counits, and the target localization map gives
  d;tau(QP,QG);(epsilon(P) tensor epsilon(G));mu(k*P,k*G)
    = tau(QP0,QG0);(epsilon(P0) tensor epsilon(G0));mu(k*P0,k*G0);Q(v).
The right sides agree by the K-flat equation. Since Qr and Qs are isomorphisms,
d is an isomorphism and cancels. No quasi-isomorphism assumption on either ordinary
pulled-back resolution map is used. This gives the displayed equation.
(blueprint: lem-pc-tensor-counit-coordinate-equation). -/
theorem tensorCounit_coordinateEquation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (k : T ⟶ X)
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback k).obj (A ⊗ B) ⟶
        (derivedPullback k).obj A ⊗ (derivedPullback k).obj B)
    (hτ : IsCanonicalPullbackTensorComparison k τ) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.monoidalCategory T.sheaf
    letI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
    ∀ φ : ((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P G) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback k).map
            (HomologicalComplex.ιMapBifunctor P G (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor k)) (P.X p) (G.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G)
            (curriedTensor (SheafOfModules.{u} (moduleRings T.toRingedSpace)))
            (.up ℤ) p q n h) →
      (derivedPullback k).map (pullbackTensorModelMap X P G) ≫
          (SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P G)) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj G) ≫
          ((SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj G)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G) := by sorry

end AlgebraicGeometry
