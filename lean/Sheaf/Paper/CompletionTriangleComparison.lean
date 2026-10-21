/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.PrincipalReductionConeCalculus
public import Sheaf.Algebra.Homology.RoosConeCalculus
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison

/-! # Exact principal completion and its canonical triangle map

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`,
Cones paragraph and shifts sentence; Stacks Tag 05RU
(blueprint: lem-pe-completion-triangle-comparison).

## Main definitions and statement

* `CompletionTriangle.tower` assembles the specified strict principal reductions.
* `CompletionTriangle.complexCompletion` applies the existing Roos functor.
* `CompletionTriangle.completion_triangle_comparison` gives the augmented exact descent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale.CompletionTriangle

open AlgebraicGeometry.ProEtale.AdicCompletion
open AlgebraicGeometry.ProEtale.PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Degreewise assembly of the existing strict reduction tower into a complex of towers.
Source: blueprint first-reduction proof, strict towers in the Cones paragraph
(blueprint: lem-pe-completion-triangle-comparison). -/
def tower (data : PrincipalReductionConeData l E X) : CochainComplex (Modules l E X) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ Modules l E X) ℤ where
  obj M :=
    { X := fun q ↦ (Functor.ofOpSequence (data.T)).flip.obj M ⋙
        HomologicalComplex.eval (Modules l E X) (.up ℤ) q
      d := fun q r ↦
        { app := fun n ↦ ((data.D n.unop).obj M).d q r
          naturality := fun _n _m f ↦
            (((Functor.ofOpSequence (data.T)).map f).app M).comm q r }
      shape := fun q r h ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((data.D n.unop).obj M).shape q r h))
      d_comp_d' := fun q r t _ _ ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((data.D n.unop).obj M).d_comp_d q r t)) }
  map f :=
    { f := fun q ↦
        { app := fun n ↦ ((data.D n.unop).map f).f q
          naturality := fun _n _m g ↦
            congrArg (fun h ↦ h.f q)
              (((Functor.ofOpSequence (data.T)).map g).naturality f).symm }
      comm' := fun q r _ ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((data.D n.unop).map f).comm q r)) }
  map_id M := HomologicalComplex.Hom.ext (funext (fun q ↦
    NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
      congrArg (fun h ↦ h.f q) ((data.D n.unop).map_id M)))))
  map_comp f g := HomologicalComplex.Hom.ext (funext (fun q ↦
    NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
      congrArg (fun h ↦ h.f q) ((data.D n.unop).map_comp f g)))))

/-- The actual composite of the principal tower and the published strict Roos functor.
Source: blueprint first-reduction proof, Cones paragraph
(blueprint: lem-pe-completion-triangle-comparison). -/
abbrev complexCompletion (data : PrincipalReductionConeData l E X) :
    CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  tower l E X data ⋙ roosF

/-- Principal completion descends with its specified augmentation, coherent shifts,
and morphism of distinguished triangles.

Source: blueprint main-20261015, first-reduction proof, Cones paragraph and shifts
sentence; Stacks Tag 05RU (blueprint: lem-pe-completion-triangle-comparison).

Proof plan, following the nine steps of the DAG node:
1. Compose the strict additive principal-reduction tower of
   lem-pe-principal-reduction-cone-calculus with H of lem-pe-roos-cone-calculus.
   Both preserve the relevant quasi-isomorphisms. Compatible j_n give the natural
   augmentation ((j_n m)_n,0), retaining its specified zero nullhomotopy.
2. Apply lem-weil-pbc-localization-universal-property to QG and Q of the augmentation.
   Full faithfulness of precomposition with Q descends their identities.
3. The images of the ordinary biproduct diagrams are biproduct diagrams, since Q and
   G are additive. Every derived object has a complex representative, so F preserves
   biproducts. Express addition by diagonal and codiagonal maps to obtain additivity.
4. Compose the principal and Roos signed shift comparisons. On their four coordinates
   the signs are (1,(-1)^r,(-1)^r,1), coherent under addition of integers. They fix the
   augmentation's first coordinate; descend the comparisons and identities through Q.
5. Use lem-pe-internal-section-tensor-comparison and lem-pc-kflat-resolution to compute
   the canonical reductions on a termwise flat K-flat P. The units are p ↦ p tensor 1
   by sk-def-sfb-derived-extension-of-scalars and sk-def-pe-derived-completion.
6. Tensor the exact coefficient sequence of det-pe-derived-nakayama-resolution with
   each flat term (def-pc-flat-sheaf-modules). By lem-pc-cone-short-exact-quasi-iso,
   (x,y) ↦ x tensor 1 gives a quasi-isomorphism from each principal cone to the tensor
   reduction. These commute strictly with transitions and carry j to the tensor unit.
7. Apply H to this augmented tower map. Exact countable products from
   lem-weil-proetale-countable-products-exact and lem-weil-strict-roos-comparison
   identify it with the specified total-derived-limit map. The sign change (v,u) ↦
   (v,-u) identifies H's coordinates with AdicCompletion.roos and fixes the unit.
   Naturality cancels the representative isomorphism, giving psi c = completionMap;
   sk-def-pe-derived-completion then identifies completeness with invertibility of c.
8. Compose the principal and Roos cone comparisons. They preserve inclusions and the
   negative-projection boundary after the shift comparison, so images of cone triangles
   are distinguished, with the specified augmentation on the third vertex.
9. Every distinguished triangle has a cone representative by
   def-weil-abstract-derived-category. Transport step 8 along that isomorphism.
   Naturality gives the first two squares; the last is
   c_C F(w) sigma = w c_K[1], by naturality and the shift equation from step 4. -/
theorem completion_triangle_comparison :
    ∃ data : PrincipalReductionConeData l E X, data.IsCanonical l E X ∧
    ∃ (a : 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ complexCompletion l E X data)
      (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
      (c : 𝟭 (DerivedCategory (Modules l E X)) ⟶ F)
      (κ : DerivedCategory.Q ⋙ F ≅ complexCompletion l E X data ⋙ DerivedCategory.Q)
      (sF : F.CommShift ℤ),
      F.Additive ∧
      (∀ (M : CochainComplex (Modules l E X) ℤ) (p : ℤ),
        (a.app M).f (p + 1) ≫ (roosχ ((tower l E X data).obj M) p).hom =
          biprod.lift 0 ((Pi.lift
            (f := fun n : ℕ ↦ ((tower l E X data).obj M).asFunctor.obj (op n))
            (fun n : ℕ ↦ (data.j n).app M)).f (p + 1))) ∧
      (∀ M : CochainComplex (Modules l E X) ℤ,
        c.app (DerivedCategory.Q.obj M) ≫ κ.hom.app M =
          DerivedCategory.Q.map (a.app M)) ∧
      (∀ (K : DerivedCategory (Modules l E X))
        (P : CochainComplex (Modules l E X) ℤ)
        (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
        (e : DerivedCategory.Q.obj P ≅ K),
        ∃ ψ : F.obj K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P),
          c.app K ≫ ψ.hom = completionMap l E X K P e) ∧
      (∀ K : DerivedCategory (Modules l E X),
        IsDerivedComplete l E X K ↔ IsIso (c.app K)) ∧
      (∀ (K : DerivedCategory (Modules l E X)) (r : ℤ),
        c.app (K⟦r⟧) ≫ (Functor.commShiftIso (self := sF) F r).hom.app K =
          (c.app K)⟦r⟧') ∧
      (∀ (T : Triangle (DerivedCategory (Modules l E X)))
        (_hT : T ∈ distTriang (DerivedCategory (Modules l E X))),
        Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
            (F.map T.mor₃ ≫
              (Functor.commShiftIso (self := sF) F (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (DerivedCategory (Modules l E X)) ∧
        ∃ γ : T ⟶ Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
          (F.map T.mor₃ ≫
            (Functor.commShiftIso (self := sF) F (1 : ℤ)).hom.app T.obj₁),
          γ.hom₁ = c.app T.obj₁ ∧ γ.hom₂ = c.app T.obj₂ ∧ γ.hom₃ = c.app T.obj₃) := by
  sorry

end AlgebraicGeometry.ProEtale.CompletionTriangle
