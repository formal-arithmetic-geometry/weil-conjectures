/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

set_option autoImplicit false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

namespace CategoryTheory

/-!
# Integral cone counit realization

Source: Stacks Project, Cohomology on Sites, Tag 0941;
(blueprint: lem-trf-integral-cone-counit-realization).
-/

/-- The cone lift of a compatible family is recovered by the derived-limit counit.

Source: Stacks Project, Cohomology on Sites, Tag 0941;
(blueprint: lem-trf-integral-cone-counit-realization).
Here `Δ` is the exact constant-tower functor `Functor.const ℕᵒᵖ`, not an arbitrary
operation on morphisms. Its action on `rTheta` is `Δ.mapDerivedCategory.map rTheta`.
The two `mapDerivedCategoryFactors` components identify its endpoints with the
localized constant complexes in the source and target of the ordinary limit cone.
The paper's positive index `m` is Lean's index `m-1`.

Proof, following the six DAG steps:
1. In each degree p the tower J = I.X p is injective. For F in the module category,
   the tower T_n(F) equals F through level n and is zero above n. Its maps to J are
   precisely maps F to J_n. The inclusion T_n(F) to T_(n+1)(F) is levelwise monic,
   hence monic by lem-weil-tower-category-levelwise-abelian. Apply injectivity
   (def-sp-injective-resolutions), with F = J_n and the map corresponding to its
   identity, to obtain a section σ_n of the transition t_n. On the product define
   τ_0 = 0 and τ_(n+1) = σ_n (τ_n - pr_n). Then
   pr_n (1-s) τ = τ_n - t_n σ_n (τ_n - pr_n) = pr_n, so 1-s is degreewise split epi.
   Its kernel is the compatible-family limit. The theorem
   lem-weil-degreewise-epi-kernel-cocone-qis identifies its zero-shifted-component
   inclusion `ι` into the shifted cone as a quasi-isomorphism. The sections and τ
   are degreewise only; no compatibility with differentials is needed for this step.
2. The family θ_n followed by q_n is compatible, by hθ and the strict naturality
   of q. The limit universal property supplies the unique chain map b from P to
   lim I with b followed by pr_n equal to θ_n followed by q_n. The K-injective
   tower model of lem-weil-pbc-ringed-strict-tower-homotopy-limit identifies lim I
   with Rlim X.
3. The coordinate conditions hι, hρ and hθLift say respectively that ι has
   coordinates (0,pr), ρ acts by the product map of q in both coordinates, and
   θLift has coordinates (0,θ). Thus b followed by ι and θLift followed by ρ
   both have coordinates (0,(θ_n followed by q_n)_n); product and biproduct
   extensionality, and the coordinate isomorphism, give b ≫ ι = θLift ≫ ρ.
4. Localize this chain equality. Since ι is a quasi-isomorphism, its localized
   image is invertible. Compose with its inverse and use hrTheta to obtain
   rTheta = DerivedCategory.Q.map b.
5. The degree-p, level-n component of Δ(b) followed by lambdaMap is b followed
   by the nth limit projection, namely θ_n followed by q_n. By hlambdaMap and
   hthetaDelta this is also the component of thetaDelta followed by q. Equality
   of complex and natural-transformation components gives
   Δ(b) ≫ lambdaMap = thetaDelta ≫ q before localization.
6. Naturality of `Functor.mapDerivedCategoryFactors` identifies the displayed
   conjugate of Δ.mapDerivedCategory.map (Q.map b) with Q.map (Δ(b)). Apply Q
   to Step 5, substitute hepsilon, and cancel Q.map q with its inverse to get
   Q.map thetaDelta. This is the equality in D(Tow(A)), with no further functor
   and no passage to quotient derived categories. No exactness of countable
   products is used in any step.
-/
theorem integralConeCounitRealization
    {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
    (q : X ⟶ I) [QuasiIso q] [I.IsKInjective]
    [∀ p : ℤ, Injective (I.X p)]
    (P : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ)
    (θ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hθ : ∀ n : ℕ,
      θ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = θ n)
    (ι : limit I.asFunctor ⟶ strictRoosComplex I) [QuasiIso ι]
    (hι : ∀ p : ℤ,
      ι.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)))
    (ρ : strictRoosComplex X ⟶ strictRoosComplex I)
    (hρ : ∀ p : ℤ,
      ρ.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        (strictRoosCoordinates X p).hom ≫
          biprod.map ((strictRoosProductMap q).f p) ((strictRoosProductMap q).f (p + 1)))
    (θLift : P ⟶ strictRoosComplex X)
    (hθLift : ∀ p : ℤ,
      θLift.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ θ n)).f (p + 1)))
    (lambdaMap : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (limit I.asFunctor) ⟶ I)
    (hlambdaMap : ∀ (n : ℕ) (p : ℤ),
      (lambdaMap.f p).app (op n) = (limit.π I.asFunctor (op n)).f p)
    (thetaDelta : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ X)
    (hthetaDelta : ∀ (n : ℕ) (p : ℤ), (thetaDelta.f p).app (op n) = (θ n).f p)
    (epsilon :
      (DerivedCategory.Q (C := ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)).obj
          (((Functor.const ℕᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (limit I.asFunctor)) ⟶
        DerivedCategory.Q.obj X)
    (hepsilon : epsilon =
      DerivedCategory.Q.map lambdaMap ≫
        inv (DerivedCategory.Q.map q))
    (rTheta : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (limit I.asFunctor))
    (hrTheta : rTheta = DerivedCategory.Q.map θLift ≫ DerivedCategory.Q.map ρ ≫
      inv (DerivedCategory.Q.map ι))
    : ((Functor.const ℕᵒᵖ : ringedSiteModules.{max uC vC r} R ⥤
          (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)).mapDerivedCategoryFactors).inv.app P ≫
        ((Functor.const ℕᵒᵖ : ringedSiteModules.{max uC vC r} R ⥤
          (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)).mapDerivedCategory).map rTheta ≫
        ((Functor.const ℕᵒᵖ : ringedSiteModules.{max uC vC r} R ⥤
          (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)).mapDerivedCategoryFactors).hom.app
            (limit I.asFunctor) ≫ epsilon =
      DerivedCategory.Q.map thetaDelta := by
  -- The supplied strict tower map already contains the compatibility of θ.
  have _compatibility := hθ
  let a := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (thetaDelta ≫ q)
  let c : Cone I.asFunctor :=
    { pt := P
      π :=
        { app := fun n ↦ a.app n
          naturality := fun n m f ↦ by
            apply HomologicalComplex.Hom.ext
            funext p
            change (𝟙 (P.X p)) ≫ ((thetaDelta ≫ q).f p).app m =
              ((thetaDelta ≫ q).f p).app n ≫ (I.X p).map f
            exact ((thetaDelta ≫ q).f p).naturality f } }
  let b : P ⟶ limit I.asFunctor := limit.lift I.asFunctor c
  have hb (n : ℕ) (p : ℤ) :
      b.f p ≫ (limit.π I.asFunctor (op n)).f p =
        (θ n).f p ≫ (q.f p).app (op n) := by
    have h := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limit.lift_π c (op n))
    change b.f p ≫ (limit.π I.asFunctor (op n)).f p =
      ((thetaDelta ≫ q).f p).app (op n) at h
    simpa only [HomologicalComplex.comp_f, NatTrans.comp_app, hthetaDelta] using h
  clear_value b
  clear c a
  have hbprod : b ≫ Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n)) =
      Pi.lift (fun n : ℕ ↦ θ n) ≫ strictRoosProductMap q := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
      strictRoosProductMap, Pi.map_π]
    apply HomologicalComplex.Hom.ext
    funext p
    exact hb n p
  have hcone : b ≫ ι = θLift ≫ ρ := by
    apply HomologicalComplex.Hom.ext
    funext k
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
    apply (cancel_mono (strictRoosCoordinates I p).hom).1
    simp only [HomologicalComplex.comp_f, Category.assoc, hι, hρ]
    rw [← Category.assoc, hθLift]
    dsimp only [strictRoosProduct]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst,
        biprod.lift_fst, biprod.lift_fst_assoc, comp_zero, zero_comp]
    · have h := congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1)) hbprod
      dsimp only [strictRoosProduct] at h
      simpa only [HomologicalComplex.comp_f, Category.assoc, biprod.map_snd,
        biprod.map_snd_assoc, biprod.lift_snd, biprod.lift_snd_assoc] using h
  have hr : rTheta = DerivedCategory.Q.map b := by
    rw [hrTheta, ← Functor.map_comp_assoc, ← hcone, Functor.map_comp]
    simp
  have hdelta : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).map b ≫
      lambdaMap = thetaDelta ≫ q := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply NatTrans.ext
    funext n
    simp only [HomologicalComplex.comp_f, NatTrans.comp_app,
      Functor.mapHomologicalComplex_map_f, Functor.const_map_app]
    simpa only [hlambdaMap, hthetaDelta] using hb n.unop p
  let Δ : ringedSiteModules.{max uC vC r} R ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) := Functor.const ℕᵒᵖ
  have hnat : Δ.mapDerivedCategoryFactors.inv.app P ≫
      Δ.mapDerivedCategory.map (DerivedCategory.Q.map b) ≫
      Δ.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) =
        DerivedCategory.Q.map ((Δ.mapHomologicalComplex (ComplexShape.up ℤ)).map b) := by
    have h := Functor.mapDerivedCategoryFactors_hom_naturality Δ b
    rw [h]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  calc
    _ = (Δ.mapDerivedCategoryFactors.inv.app P ≫
        Δ.mapDerivedCategory.map (DerivedCategory.Q.map b) ≫
        Δ.mapDerivedCategoryFactors.hom.app (limit I.asFunctor)) ≫ epsilon := by
      rw [hr]
      simp only [Category.assoc]
      rfl
    _ = DerivedCategory.Q.map ((Δ.mapHomologicalComplex (ComplexShape.up ℤ)).map b) ≫
        epsilon := congrArg (fun f ↦ f ≫ epsilon) hnat
    _ = DerivedCategory.Q.map
        ((Δ.mapHomologicalComplex (ComplexShape.up ℤ)).map b ≫ lambdaMap) ≫
          inv (DerivedCategory.Q.map q) := by rw [hepsilon, Functor.map_comp, Category.assoc]
    _ = DerivedCategory.Q.map (thetaDelta ≫ q) ≫ inv (DerivedCategory.Q.map q) :=
      congrArg (fun f ↦ DerivedCategory.Q.map f ≫ inv (DerivedCategory.Q.map q)) hdelta
    _ = DerivedCategory.Q.map thetaDelta := by rw [Functor.map_comp]; simp

end CategoryTheory
