/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns
import Sheaf.Algebra.Homology.DerivedTensorShiftDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent

/-!
# Transport through an oriented derived tensor product

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/cor-pur-dualizing-object-purity.proof.md, three-arrow composite;
Stacks, Tags 0FNH, 06YS, 06YT and 06YU
(blueprint: lem-pur-oriented-derived-tensor-transport).

The tensor is the recorded fixed-ring pro-etale tensor, not a new tensor construction.
The second-variable comparison is characterized on every K-flat representative.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u vI uI uC vC

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A]

/-- The complete normalization and transport specification, using the actual total tensor,
localization comparison and degree-zero embedding. The local colimit instance only
specializes the existing sheaf colimits to countable totalization diagrams.
Source: Stacks, Tags 0FNH and 06YU; cor-pur-dualizing-object-purity.proof.md
(blueprint: lem-pur-oriented-derived-tensor-transport). -/
def orientedDerivedTensorTransportSpec
    (C : Type uC) [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{vC} C] (d : ℕ) : Prop :=
  letI : Limits.HasColimitsOfSize.{0, 0} C :=
    Limits.hasColimitsOfSizeShrink.{0, 0, vC, vC} C
  letI hasTotal (Q B : CochainComplex C ℤ) :
      CochainComplex.HasMapBifunctor Q B (curriedTensor C) := fun _ ↦ inferInstance
  ∃ a : ∀ (M : _root_.DerivedCategory C) (T : C),
      (M ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj T)⟦(2 * (d : ℤ))⟧ ≅
        M ⊗ ((_root_.DerivedCategory.singleFunctor _ 0).obj T)⟦(2 * (d : ℤ))⟧,
    (∀ (M M' : _root_.DerivedCategory C) (T T' : C) (f : M ⟶ M') (g : T ⟶ T'),
      (f ⊗ₘ (_root_.DerivedCategory.singleFunctor _ 0).map g)⟦(2 * (d : ℤ))⟧' ≫
          (a M' T').hom =
        (a M T).hom ≫
          (f ⊗ₘ ((_root_.DerivedCategory.singleFunctor _ 0).map g)⟦(2 * (d : ℤ))⟧')) ∧
    (∀ (Q : CochainComplex C ℤ) (T : C) (p q r q' r' : ℤ) (hpq : p + q = r)
      (hq : q' = q + 2 * (d : ℤ)) (hr : r' = r + 2 * (d : ℤ)),
      CochainComplex.ιMapBifunctor Q
          (((CochainComplex.singleFunctor _ 0).obj T)⟦(2 * (d : ℤ))⟧)
          (curriedTensor C) p q r hpq ≫
        (CochainComplex.mapBifunctorShift₂Iso Q ((CochainComplex.singleFunctor _ 0).obj T)
          (curriedTensor C)
          (2 * (d : ℤ))).hom.f r =
      (Q.X p ◁ (CochainComplex.shiftFunctorObjXIso ((CochainComplex.singleFunctor _ 0).obj T)
            (2 * (d : ℤ)) q q' hq).hom) ≫
        CochainComplex.ιMapBifunctor Q ((CochainComplex.singleFunctor _ 0).obj T)
          (curriedTensor C)
          p q' r' (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mapBifunctor Q ((CochainComplex.singleFunctor _ 0).obj T)
            (curriedTensor C))
          (2 * (d : ℤ)) r r' hr).inv) ∧
    (∀ (Q : CochainComplex C ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
      ∀ (T : C)
        (M : _root_.DerivedCategory C)
        (e : _root_.DerivedCategory.Q.obj Q ≅ M),
      (a M T).hom ≫
          (e.inv ▷ ((_root_.DerivedCategory.singleFunctor _ 0).obj T)⟦(2 * (d : ℤ))⟧) ≫
          (_root_.DerivedCategory.Q.obj Q ◁
            ((_root_.DerivedCategory.Q.commShiftIso (2 * (d : ℤ))).inv.app
              ((CochainComplex.singleFunctor _ 0).obj T))) ≫
          Functor.LaxMonoidal.μ _root_.DerivedCategory.Q Q
            (((CochainComplex.singleFunctor _ 0).obj T)⟦(2 * (d : ℤ))⟧) ≫
          _root_.DerivedCategory.Q.map
            (CochainComplex.mapBifunctorShift₂Iso Q ((CochainComplex.singleFunctor _ 0).obj T)
              (curriedTensor C) (2 * (d : ℤ))).hom ≫
          ((_root_.DerivedCategory.Q.commShiftIso (2 * (d : ℤ))).hom.app
            (CochainComplex.mapBifunctor Q ((CochainComplex.singleFunctor _ 0).obj T)
              (curriedTensor C))) =
        ((e.inv ▷ (_root_.DerivedCategory.singleFunctor _ 0).obj T) ≫
          Functor.LaxMonoidal.μ _root_.DerivedCategory.Q Q
            ((CochainComplex.singleFunctor _ 0).obj T))⟦(2 * (d : ℤ))⟧') ∧
    (∀ (T : C) (ω : _root_.DerivedCategory C)
      (π : ω ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj T)⟦(2 * (d : ℤ))⟧)
      (I : Type uI) [Category.{vI} I] (P H : I ⥤ _root_.DerivedCategory C)
      (θ : P ⋙ (curriedTensor (_root_.DerivedCategory C)).flip.obj ω ≅ H),
    ∃ G : P ⋙
        (curriedTensor (_root_.DerivedCategory C)).flip.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj T) ⋙
        shiftFunctor _ (2 * (d : ℤ)) ≅ H,
      (∀ i : I, G.hom.app i =
        (a (P.obj i) T).hom ≫
          (P.obj i ◁ π.inv) ≫ θ.hom.app i) ∧
      (∀ i : I, G.inv.app i = θ.inv.app i ≫ (P.obj i ◁ π.hom) ≫
        (a (P.obj i) T).inv))

/-- The even-shift comparison is natural in both variables, is sign-free on the total
complex, and has the specified normalization on every K-flat representative.
Source: Stacks, Tags 0FNH, 06YS, 06YT and 06YU, and the three-arrow composite in
cor-pur-dualizing-object-purity.proof.md
(blueprint: lem-pur-oriented-derived-tensor-transport).

Proof: (1) The second tensor shift on first degree p has coefficient (-1)^(2dp)=1.
Its inverse is therefore identity reindexing; when the second complex is concentrated
in degree zero both differentials are d_Q tensor 1. (2) Descend through the resolving
localization using site-derived-tensor-descent and derived-tensor-shift-descent.
The comparison with a fixed flat-term K-flat Q is obtained by uniquely extending the
resolving tensor comparisons and their inverses. (3) For an arbitrary K-flat Q choose a
flat-term K-flat resolution R to Q. Resolution independence and naturality of the chain
shift identify the square for Q with that for R. The cocycle identity identifies any
two choices. The existing derived tensor shift has exactly this localization
normalization. Naturality then gives the same square for every isomorphism Q(Q) to M.
No flatness assumption on the sheaf T is used.
(4) Tensoring with Pi inverse is natural and invertible, so compose a, this tensor map,
and theta. Naturality of these three factors gives H(u) G_i = G_j F(u) for every u.
(5) Reverse the three inverse factors. Associativity and their inverse equations give
both identity composites, and multiplying the naturality equation by these inverses
gives naturality of the inverse family. All factors are prescribed, with no scalar,
sign or geometric normalization choice. -/
theorem orientedDerivedTensorTransport (d : ℕ) :
    orientedDerivedTensorTransportSpec
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) d := by
  sorry

end AlgebraicGeometry.ProEtale
