/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Finite exterior and tensor-dual Koszul comparison

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison).

The site and coefficient transports and the termwise-limit comparison are constructed
here. The remaining source lemma concerns only finite Koszul levels, power transitions
and the augmentation. Products, cones and derived transport are proved by consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The pro-etale category with its morphisms lifted to the coefficient universe.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechSite := AsSmall.{0} X.ProEt

/-- The canonical equivalence with the category whose Hom universe has been lifted.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechSiteEquiv : X.ProEt ≌ completedCechSite X := AsSmall.equiv

/-- The topology induced along the inverse of the canonical site equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechTopology :=
  (completedCechSiteEquiv X).inverse.inducedTopology (ProEt.topology X)

/-- The actual completed ring sheaf pulled to the canonical small site.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechRing : Sheaf (completedCechTopology X) CommRingCat.{u + 1} :=
  ((completedCechSiteEquiv X).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
    (completedCechTopology X) (ProEt.topology X)).obj (pbcAdicCompletion X d)

/-- The module-sheaf equivalence induced by the canonical ringed-site equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechModulesEquiv :
    pbcModules X (pbcAdicCompletion X d) ≌ ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
      ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d)) := by
  let e := completedCechSiteEquiv X
  let J := ProEt.topology X
  let K := completedCechTopology X
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (pbcAdicCompletion X d)
  let R' : Sheaf K RingCat.{u + 1} :=
    (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R
  let φ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R' :=
    ⟨Functor.whiskerRight (NatTrans.op e.unitInv) R.obj⟩
  let ψ : R' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R := 𝟙 _
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) R'.obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.inverse.map (e.counit.app U.unop)).op =
      R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op
    rw [e.unitInv_app_inverse]
  have h₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) R.obj = 𝟙 R.obj := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.unitInv.app U.unop).op ≫
      (𝟙 _ ≫ R.obj.map (e.unit.app U.unop).op) = 𝟙 _
    rw [Category.id_comp, ← R.obj.map_comp, ← op_comp, e.unitIso.hom_inv_id_app]
    exact R.obj.map_id _
  exact (SheafOfModules.pushforwardPushforwardEquivalence.{u + 1} e φ ψ h₁ h₂).symm

/-- The standard derived category in the original ambient derived universe.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
instance : HasDerivedCategory.{u + 2} (ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
    ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (completedCechRing X d))) := HasDerivedCategory.standard _

/-- The exact module equivalence is additive because it preserves products and zero.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
instance : (completedCechModulesEquiv X d).functor.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- The equivalence induced on unbounded derived categories by the module equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechDerivedEquiv : PbcCompletedDerived X d ≌
    ringedSiteDerived.{u + 1, u + 2} (completedCechRing X d) :=
  (completedCechModulesEquiv X d).mapDerivedCategory

/-- The compatible-residue scalar map, followed by the fixed coefficient comparison.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechScalarMap :
    (Functor.const (completedCechSite X)ᵒᵖ).obj (CommRingCat.of A) ⟶
      (completedCechRing X d).obj :=
  Functor.whiskerLeft (completedCechSiteEquiv X).inverse.op
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (adicDatumScalar X (intrinsicPresentationDatum d)).hom ≫
        (pbcCompletedComparison X d).hom.hom)

/-- The actual compatible-residue scalar as a global section on the canonical small site.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechScalar (a : A) :
    ((completedCechRing X d).obj ⋙ CategoryTheory.forget CommRingCat.{u + 1}).sections := by
  refine ⟨fun U ↦ (completedCechScalarMap X d).app U a, ?_⟩
  intro U V f
  exact congrArg (fun g ↦ g a) ((completedCechScalarMap X d).naturality f).symm


/-- The strict-tower derived category in the same ambient universe.
Source: Stacks, Tag 0941
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
instance : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤
    ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
      ((sheafCompose (completedCechTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d))) := HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison between limits of complexes and termwise limits.
Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedKoszulTermwiseLimitIso {B : Type*} [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ≅
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.coneOfHasLimitEval_π_app_f,
      HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite exterior Koszul tower agrees with the ordered tensor-dual tower.

Source: Stacks Project, more-algebra.tex Tag 0664, Lemma 15.29.12
(tensor decomposition), and algebraization.tex Tag 0A0E,
proof of lemma-derived-completion-koszul (finite-free duality identification).
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison).

Proof: on the free module with ordered basis Fin r, use the sorted subset basis of
its exterior powers. A k-subset indexes degree -k. Identify its basis vector with the
dual tensor coordinate, multiplied by (-1)^(k*(k-1)/2). The ratio in adjacent degrees
is the sign in the Hom-complex differential, so the exterior contraction differential
agrees with the dual of the ordered positive tensor differential. This gives inverse
chain maps, identity in degree zero. The same calculation can be organized by induction
on r, splitting off the last exterior generator and the last two-term tensor factor.
Apply the actual constant-module construction and its completed coefficient extension.
The coefficient comparison is an isomorphism and the site change is an equivalence;
their tensor and finite-sum comparisons therefore carry this finite chain isomorphism
through the displayed functor H. Tensor with the arbitrary complex C: in each total
degree the Koszul coordinate has finite support, so the same coordinates give an
isomorphism on the total complexes. Use the identity-on-sections round trip to identify
the transported input with N. For a transition, both subset coordinates are multiplied
by the product of the corresponding generators, hence the chain isomorphisms commute
with the power transitions. In degree zero the empty subset has sign +1, giving exactly
the displayed augmentation equation. No products, inverse limits or cones occur here.

For r=0 both finite complexes are the tensor unit and the comparison is the unit
isomorphism. The formulas allow zero or invertible generators, a zero coefficient ring,
and an empty site; no regularity or generation hypothesis is used. -/
theorem completedKoszulFiniteComparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let G := (completedCechModulesEquiv X d).functor
    let H := (intrinsicPresentationModulesBack X d ⋙ G).mapHomologicalComplex (.up ℤ)
    let P := (intrinsicPresentationComplex X d).obj C
    let O := completedCechRing X d
    let b := fun i ↦ completedCechScalar X d (a i)
    let N := (G.mapHomologicalComplex (.up ℤ)).obj C
    let T := ringedKoszulTensorTowerComplex O r b N
    ∃ e : ∀ m : ℕ, H.obj
        (completedKoszulTensor X (intrinsicPresentationDatum d) r a P m) ≅
          T.asFunctor.obj (op m),
      (∀ m, H.map
          (completedKoszulTensorTransition X (intrinsicPresentationDatum d) r a P m) ≫
            (e m).hom = (e (m + 1)).hom ≫
              T.asFunctor.map (homOfLE (Nat.le_succ m)).op) ∧
      (∀ (m : ℕ) (q : ℤ),
        G.map ((intrinsicPresentationRoundTrip X d).hom.app (C.X q) ≫
          (intrinsicPresentationModulesBack X d).map
            ((completedKoszulTensorUnit X (intrinsicPresentationDatum d) r a P m).f q)) ≫
              (e m).hom.f q = (ringedKoszulTensorUnitComponent O r b N (op m)).f q) := by
  sorry

end AlgebraicGeometry.Scheme
