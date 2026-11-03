/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.CochainUniverseTransport.CochainCoefficientUniverseTransport
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorCompositionEquation
import WeilConjectures.SecSmoothPurity.ModuleTensorCoefficientEquations

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (blueprint: lem-pur-cochain-pullback-tensor-coherence).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe w uC vC uD vD uE vE uA vA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] changed extensionFunctor scalarAssociation compositionModule
attribute [local irreducible] SheafOfModules.monoidalCategory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

@[reassoc]
private theorem comparison_ι (f : RingedPullback R S) (k : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (hpq : p + q = n) :
    f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq) ≫
        (comparison f k P Q).hom.f n =
      (k.mu (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor
        ((pull f).obj P) ((pull f).obj Q) (curriedTensor (Modules S)) p q n hpq := by
  apply (cancel_mono ((comparison f k P Q).inv.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f]
  change _ = (k.mu (P.X p) (Q.X q)).hom ≫ _ ≫
    (tensorPullbackTotal f.L k.mu k.naturality P Q).f n
  simp only [tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
  exact Category.comp_id _

@[reassoc]
private theorem tensor_ι {A : Type uA} [Category.{vA} A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCoproducts.{0} A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {P Q P' Q' : CochainComplex A ℤ} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) :
    CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q n hpq ≫ (a ⊗ₘ b).f n =
      (a.f p ⊗ₘ b.f q) ≫
        CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) p q n hpq := by
  change _ ≫ (HomologicalComplex.mapBifunctorMap a b (curriedTensor A) (.up ℤ)).f n = _
  simp only [HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app,
    curriedTensor_obj_map, tensorHom_def, Category.assoc]

private theorem composition_of_modules
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h)
    (a : CompositePresentation f g h kf kg kh)
    (hm : ∀ M N : Modules R,
      (kh.mu M N).hom ≫
          ((compositionModule f g h a.rightModules).hom.app M ⊗ₘ
            (compositionModule f g h a.rightModules).hom.app N) =
        (compositionModule f g h a.rightModules).hom.app (M ⊗ N) ≫
          g.L.map (kf.mu M N).hom ≫ (kg.mu (f.L.obj M) (f.L.obj N)).hom) :
    IsCompatibleWithComposition f g h kf kg kh a := by
  let := h.moduleAdj.isLeftAdjoint
  intro P Q
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map h.L
  intro p q hpq
  let c := compositionModule f g h a.rightModules
  let iR := CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq
  let iS := CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
    (curriedTensor (Modules S)) p q n hpq
  let iT := CochainComplex.ιMapBifunctor ((pull g).obj ((pull f).obj P))
    ((pull g).obj ((pull f).obj Q)) (curriedTensor (Modules T)) p q n hpq
  change h.L.map iR ≫ (comparison h kh P Q).hom.f n ≫ _ =
    h.L.map iR ≫ c.hom.app ((P ⊗ Q).X n) ≫ _
  rw [comparison_ι_assoc h kh P Q p q n hpq]
  rw [tensor_ι (composition f g h a P).hom (composition f g h a Q).hom p q n hpq]
  change (kh.mu (P.X p) (Q.X q)).hom ≫
      (c.hom.app (P.X p) ⊗ₘ c.hom.app (Q.X q)) ≫ iT =
    h.L.map iR ≫ c.hom.app ((P ⊗ Q).X n) ≫
      g.L.map ((comparison f kf P Q).hom.f n) ≫
        (comparison g kg ((pull f).obj P) ((pull f).obj Q)).hom.f n
  erw [c.hom.naturality_assoc iR]
  change _ = c.hom.app (P.X p ⊗ Q.X q) ≫ g.L.map (f.L.map iR) ≫ _
  erw [← g.L.map_comp_assoc]
  erw [comparison_ι f kf P Q p q n hpq, g.L.map_comp]
  simp only [Category.assoc]
  erw [comparison_ι g kg ((pull f).obj P) ((pull f).obj Q) p q n hpq]
  exact congrArg (fun z ↦ z ≫ iT) (hm (P.X p) (Q.X q))

private theorem coefficients_extension_of_modules
    (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (hm : ∀ M N : Modules R,
      (changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
          (k'.mu ((extensionFunctor d.sourceMap).obj M)
            ((extensionFunctor d.sourceMap).obj N)).hom ≫
          ((scalarAssociation f k d k').hom.app M ⊗ₘ
            (scalarAssociation f k d k').hom.app N) =
        (scalarAssociation f k d k').hom.app (M ⊗ N) ≫
          (extensionFunctor d.targetMap).map (k.mu M N).hom ≫
          ((extensionComparison d.targetMap).mu (f.L.obj M) (f.L.obj N)).hom)
    (P Q : Complex R) :
    (pull (changed f d)).map (epsilon d.sourceMap P Q).hom ≫
        (comparison (changed f d) k'
          ((extend d.sourceMap).obj P) ((extend d.sourceMap).obj Q)).hom ≫
          ((kappa f k d k' P).hom ⊗ₘ (kappa f k d k' Q).hom) =
      (kappa f k d k' (P ⊗ Q)).hom ≫
        (extend d.targetMap).map (comparison f k P Q).hom ≫
          (epsilon d.targetMap ((pull f).obj P) ((pull f).obj Q)).hom := by
  let := (extensionAdjunction d.sourceMap).isLeftAdjoint
  let := (changed f d).moduleAdj.isLeftAdjoint
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (extensionFunctor d.sourceMap ⋙ (changed f d).L)
  intro p q hpq
  let b := scalarAssociation f k d k'
  let iR := CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq
  let iT := CochainComplex.ιMapBifunctor
    ((extend d.targetMap).obj ((pull f).obj P))
    ((extend d.targetMap).obj ((pull f).obj Q))
    (curriedTensor (Modules d.S')) p q n hpq
  change (changed f d).L.map ((extensionFunctor d.sourceMap).map iR) ≫
      (changed f d).L.map ((epsilon d.sourceMap P Q).hom.f n) ≫
        (comparison (changed f d) k'
          ((extend d.sourceMap).obj P) ((extend d.sourceMap).obj Q)).hom.f n ≫ _ =
    (changed f d).L.map ((extensionFunctor d.sourceMap).map iR) ≫
      b.hom.app ((P ⊗ Q).X n) ≫ _
  erw [← (changed f d).L.map_comp_assoc,
    comparison_ι (extensionPullback d.sourceMap), (changed f d).L.map_comp]
  dsimp only [extensionPullback, pull, extend, restrictComplex,
    Functor.mapHomologicalComplex, Functor.comp_obj]
  simp only [Category.assoc]
  erw [comparison_ι_assoc (changed f d), tensor_ι]
  change (changed f d).L.map ((extensionComparison d.sourceMap).mu (P.X p) (Q.X q)).hom ≫
      (k'.mu ((extensionFunctor d.sourceMap).obj (P.X p))
        ((extensionFunctor d.sourceMap).obj (Q.X q))).hom ≫
      (b.hom.app (P.X p) ⊗ₘ b.hom.app (Q.X q)) ≫ iT =
    (changed f d).L.map ((extensionFunctor d.sourceMap).map iR) ≫
      b.hom.app ((P ⊗ Q).X n) ≫
        (extensionFunctor d.targetMap).map ((comparison f k P Q).hom.f n) ≫
          (epsilon d.targetMap ((pull f).obj P) ((pull f).obj Q)).hom.f n
  erw [b.hom.naturality_assoc iR]
  change _ = b.hom.app (P.X p ⊗ Q.X q) ≫
    (extensionFunctor d.targetMap).map (f.L.map iR) ≫ _
  erw [← (extensionFunctor d.targetMap).map_comp_assoc,
    comparison_ι f k P Q p q n hpq, (extensionFunctor d.targetMap).map_comp]
  dsimp only [extensionPullback, pull, extend, restrictComplex,
    Functor.mapHomologicalComplex, Functor.comp_obj]
  simp only [Category.assoc]
  erw [comparison_ι (extensionPullback d.targetMap)]
  simpa only [extensionPullback, pull, extend, Functor.mapHomologicalComplex,
    Category.assoc, b, iT] using
      congrArg (fun z ↦ z ≫ iT) (hm (P.X p) (Q.X q))

private theorem tau_f (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (P : Complex R) (n : ℤ) :
    (tau f k d k' P).f n = (transitionModule f k d k').app (P.X n) := rfl

@[reassoc]
private theorem restrictionTensor_ι {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) (p q n : ℤ) (hpq : p + q = n) :
    CochainComplex.ιMapBifunctor ((restrictComplex a).obj P) ((restrictComplex a).obj Q)
        (curriedTensor (Modules A)) p q n hpq ≫ (restrictionTensor a P Q).f n =
      restrictionTensorModule a (P.X p) (Q.X q) ≫ (restrictionFunctor a).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules B)) p q n hpq) := by
  change _ ≫ restrictionTensorComponent a P Q n = _
  simp only [restrictionTensorComponent, HomologicalComplex.ι_mapBifunctorDesc]
  rfl

private theorem coefficients_transition_of_modules
    (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (hm : ∀ M N : Modules R,
      (k.mu M N).hom ≫
          ((transitionModule f k d k').app M ⊗ₘ (transitionModule f k d k').app N) ≫
          restrictionTensorModule d.targetMap
            ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj M))
            ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj N)) =
        (transitionModule f k d k').app (M ⊗ N) ≫ (restrictionFunctor d.targetMap).map
          ((changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
            (k'.mu ((extensionFunctor d.sourceMap).obj M)
              ((extensionFunctor d.sourceMap).obj N)).hom)) (P Q : Complex R) :
    (comparison f k P Q).hom ≫ (tau f k d k' P ⊗ₘ tau f k d k' Q) ≫
        restrictionTensor d.targetMap
          ((pull (changed f d)).obj ((extend d.sourceMap).obj P))
          ((pull (changed f d)).obj ((extend d.sourceMap).obj Q)) =
      tau f k d k' (P ⊗ Q) ≫ (restrictComplex d.targetMap).map
        ((pull (changed f d)).map (epsilon d.sourceMap P Q).hom ≫
          (comparison (changed f d) k'
            ((extend d.sourceMap).obj P) ((extend d.sourceMap).obj Q)).hom) := by
  let := f.moduleAdj.isLeftAdjoint
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map f.L
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [comparison_ι_assoc f k, tensor_ι_assoc, restrictionTensor_ι]
  simp only [tau_f]
  dsimp only [extensionPullback, pull, extend, restrictComplex,
    Functor.mapHomologicalComplex, Functor.comp_obj]
  erw [(transitionModule f k d k').naturality_assoc]
  dsimp only [extensionPullback, pull, extend, restrictComplex,
    Functor.mapHomologicalComplex, Functor.comp_obj]
  simp only [Functor.comp_map]
  erw [← (restrictionFunctor d.targetMap).map_comp,
    ← (changed f d).L.map_comp_assoc,
    comparison_ι (extensionPullback d.sourceMap), (changed f d).L.map_comp]
  dsimp only [extensionPullback, pull, extend, restrictComplex,
    Functor.mapHomologicalComplex, Functor.comp_obj]
  simp only [Category.assoc]
  erw [comparison_ι (changed f d)]
  simpa only [pull, extend, restrictComplex, Functor.mapHomologicalComplex,
    extensionPullback, curriedTensor_obj_obj, Functor.map_comp, Category.assoc] using congrArg
      (fun z ↦ z ≫ (restrictionFunctor d.targetMap).map
        (CochainComplex.ιMapBifunctor
          ((pull (changed f d)).obj ((extend d.sourceMap).obj P))
          ((pull (changed f d)).obj ((extend d.sourceMap).obj Q))
          (curriedTensor (Modules d.S')) p q n hpq)) (hm (P.X p) (Q.X q))

/-- The complete coherence conclusion: usual monoidal maps, composable ringed
morphisms and both canonical coefficient diagrams, including quotient transitions.  The
statement is independent of boundedness and flatness assumptions.
Source: Stacks 03EL, 07A4 and 0D6D
(blueprint: lem-pur-cochain-pullback-tensor-coherence). -/
def HasTensorCoherence (f : RingedPullback R S) (k : Comparison f) : Prop :=
  IsCoherent f k ∧
      (∀ {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
        {H : GrothendieckTopology E}
        [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
        {T : Sheaf H CommRingCat.{w}} (g : RingedPullback S T)
        (h : RingedPullback R T) (kg : Comparison g) (kh : Comparison h)
        (a : CompositePresentation f g h k kg kh),
        IsCompatibleWithComposition f g h k kg kh a) ∧
      (∀ (d : CoefficientSquare f) (k' : Comparison (changed f d)),
        IsCompatibleWithCoefficients f k d k')

/-- Signed cochain tensor comparison, composition, and coefficient coherence.
Source: Stacks 07A4, 03EL, and 0D6D
(blueprint: lem-pur-cochain-pullback-tensor-coherence).

Proof:
1. Use the normalized ordinary comparison of
   lem-weil-pbc-ringed-topoi-module-pullback-tensor on each pair of degrees.
   The adjunction lem-weil-pbc-ringed-topoi-module-adjunction preserves the full
   coproduct indexed by p+q=n. This gives c and its scalar-contraction inverse.
2. Naturality of the ordinary comparison commutes with d_P and d_Q; additivity
   preserves the factor (-1)^p in def-pc-tensor-complex-sheaves. Thus c is a chain map.
3. The insertion/contraction composites are identities on pure tensors.
   The sheaf tensor universal property lem-pc-sites-sheaf-tensor-bilinear-universal
   extends this equality and the two-variable naturality to sheaf morphisms.
4. On triple homogeneous tensors, the associator routes insert the same units.
   The braiding routes have the same (-1)^(pq); the two action-unit routes multiply
   by the same scalar. Use lem-pc-sheaf-modules-tensor-closed and total-tensor signs.
5. Use def-weil-pbc-composite-adjunction and
   lem-weil-pbc-conjugate-iso-unit-equation to identify a with scalar association.
   Both tensor routes then insert the same units and multiply the same scalars.
6. The compatible coefficient square makes kappa balanced. On generalized pure
   tensors the first equation sends s' tensor ((x tensor y) tensor 1) to
   ((1 tensor x) tensor s') tensor ((1 tensor y) tensor 1) by either route.
   For the second, both routes send s tensor (x tensor y) to
   (bar(s) tensor (x tensor 1)) tensor (1 tensor (y tensor 1)). Sheafification
   extends equality; tau is S-linear only after restriction of scalars as displayed.
7. These are degreewise calculations on the full coproduct, with no boundedness
   or flatness restriction. Apply the transition equation at each m >= n of a
   quotient tower; it asserts commutation with transitions, with no inverse claimed.
-/
theorem cochainPullbackTensorCoherence (f : RingedPullback R S) (k : Comparison f) :
    HasTensorCoherence.{w, uC, vC, uD, vD, uE, vE} f k := by
  refine ⟨?_, ?_, ?_⟩
  · exact cochainComparison_monoidal f k
  · intro E _ _ H _ T g h kg kh a
    exact composition_of_modules f g h k kg kh a
      (cochainModuleTensorComposition f g h k kg kh a)
  · intro d k'
    obtain ⟨he, ht⟩ := cochainModuleTensorCoefficients f k d k'
    exact ⟨coefficients_extension_of_modules f k d k' he,
      coefficients_transition_of_modules f k d k' ht⟩

set_option maxHeartbeats 600000 in
-- Three ringed functors require repeated dependent termwise conversions.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Nested scalar-extension presentations require explicit termwise conversions.
-- Termwise scalar restriction and the two scalar extensions have dependent sources.
end CategoryTheory.CochainPullback

universe r m t
namespace CategoryTheory.CochainPullback

end CategoryTheory.CochainPullback
