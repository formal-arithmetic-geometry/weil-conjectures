/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdierModels
import all WeilConjectures.SixFunctors.IntegralVerdier
import all WeilConjectures.SixFunctors.IntegralVerdierSignedCalculus
import WeilConjectures.AlgebraicGeometry.IntegralHomEvaluationNaturality
import WeilConjectures.CategoryTheory.ScalarLocalizationBiduality

/-! # Transported signed symmetry naturality for the rational Verdier datum -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private def restrictedSelfAdjunction
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : Datum D l hl X E wE)
    (s : IntegralVerdier.SignedSymmetry X _ A.ordinary)
    (hs : ∀ (K L K' L' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X)) (f : K ⟶ K') (g : L ⟶ L'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f)) :
    (IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).rightOp ⊣
      IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves :=
  Adjunction.mkOfHomEquiv
    { homEquiv K M :=
        { toFun f := ObjectProperty.homMk
            ((A.ordinary.adjunction M.unop.obj).homEquiv K.obj wE.omega.obj
              ((s.swap M.unop.obj K.obj).hom ≫
                ((A.ordinary.adjunction K.obj).homEquiv _ _).symm f.unop.hom))
          invFun g := (ObjectProperty.homMk
            ((A.ordinary.adjunction K.obj).homEquiv M.unop.obj wE.omega.obj
              ((s.swap M.unop.obj K.obj).inv ≫
                ((A.ordinary.adjunction M.unop.obj).homEquiv _ _).symm g.hom))).op
          left_inv f := by
            apply Quiver.Hom.unop_inj
            apply ObjectProperty.hom_ext
            dsimp only [ObjectProperty.homMk]
            erw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
            rfl
          right_inv g := by
            apply ObjectProperty.hom_ext
            dsimp only [ObjectProperty.homMk]
            erw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply] }
      homEquiv_naturality_left_symm := by
        intro K K' M f g
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        change (A.ordinary.adjunction K.obj).homEquiv _ _
            ((s.swap M.unop.obj K.obj).inv ≫
              ((A.ordinary.adjunction M.unop.obj).homEquiv _ _).symm (f.hom ≫ g.hom)) =
          (A.ordinary.adjunction K'.obj).homEquiv _ _
            ((s.swap M.unop.obj K'.obj).inv ≫
              ((A.ordinary.adjunction M.unop.obj).homEquiv _ _).symm g.hom) ≫
            (IntegralHom.hom.{u, u} X _).map (Prod.mkHom f.hom.op (𝟙 wE.omega.obj))
        rw [← tensorTranspose_source X A.ordinary
          (IntegralHom.evaluation_naturality X _ A.ordinary)]
        apply ((A.ordinary.adjunction K.obj).homEquiv _ _).congr_arg
        erw [Adjunction.homEquiv_naturality_left_symm]
        apply (cancel_epi (s.swap M.unop.obj K.obj).hom).1
        simp only [Iso.hom_inv_id_assoc]
        rw [← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id_assoc]
        rfl
      homEquiv_naturality_right := by
        intro K M M' f g
        apply ObjectProperty.hom_ext
        change (A.ordinary.adjunction M'.unop.obj).homEquiv _ _
            ((s.swap M'.unop.obj K.obj).hom ≫
              ((A.ordinary.adjunction K.obj).homEquiv _ _).symm
                (g.unop.hom ≫ f.unop.hom)) =
          (A.ordinary.adjunction M.unop.obj).homEquiv _ _
            ((s.swap M.unop.obj K.obj).hom ≫
              ((A.ordinary.adjunction K.obj).homEquiv _ _).symm f.unop.hom) ≫
            (IntegralHom.hom.{u, u} X _).map
              (Prod.mkHom g.unop.hom.op (𝟙 wE.omega.obj))
        rw [← tensorTranspose_source X A.ordinary
          (IntegralHom.evaluation_naturality X _ A.ordinary)]
        apply ((A.ordinary.adjunction M'.unop.obj).homEquiv _ _).congr_arg
        erw [Adjunction.homEquiv_naturality_left_symm]
        change (s.swap M'.unop.obj K.obj).hom ≫
            A.ordinary.tensor.map (Prod.mkHom (𝟙 K.obj) g.unop.hom) ≫ _ = _
        rw [← Category.assoc, ← hs, Category.assoc] }

-- The representative witnesses in the unchanged statement do not occur in its equation.
set_option linter.unusedVariables false in
/-- A K-flat normalized swap can be transported to a datum with the same ordinary
presentation and an everywhere-natural signed swap; the biduality isomorphism is
re-chosen for the transported swap.

Source: blueprint thm-coef-rational-verdier, proof step 5
(blueprint: lem-coef-rational-verdier-datum-naturality).

Proof:
1. Every derived object `K` is isomorphic to `Q P` for a K-flat complex `P` (K-flat
   resolutions of sheaves of modules on a site, Stacks 06YF); choose such
   `φ_K : Q P_K ≅ K`, taking `P_K = P` and `φ_K = 𝟙` when `K` is `Q P` for a K-flat `P`.
2. `hflat` extends to all derived maps between K-flat objects: a derived map
   `Q P ⟶ Q P'` is `(Q s)⁻¹ ≫ Q f` for a quasi-isomorphism `s : P'' ⟶ P` and a chain map
   `f : P'' ⟶ P'`, and `P''` may be taken K-flat (resolve the middle of the roof). The
   naturality squares for `Q s` and `Q f` give the square for the composite.
3. Define `swap' K L` as `A.symmetry.swap (Q P_K) (Q P_L)` conjugated by `φ_K` and `φ_L`
   under the ordinary tensor. By step 2 it is natural for arbitrary derived maps, and on
   K-flat pairs it equals `A.symmetry.swap` (step 2 applied to the identifications), so the
   `representative` clause of `A.symmetry` holds for `swap'` with the same Koszul chain
   swaps.
4. Keep every field of `A` that does not read the swap (`ordinary`, `completion`,
   `preserves`, the dual functor with its object, linearity, pure-tensor, equivalence and
   exactness clauses, and evaluation). Only `bidual` changes. With the natural Koszul swap,
   `delta` is the standard biduality map `K ⟶ RHom(RHom(K, ω), ω)`. It is natural in `K` and
   invertible on integral constructible objects by integral Verdier biduality
   (thm-coef-integral-verdier).
5. Every rational constructible object is the localization of an integral constructible
   object. The new `bidual` has the localized new `delta` as its components. Naturality for
   a rational map `c ⊗ f` is integral naturality of `delta` multiplied by `c`, through the
   `pure` and `linear` clauses of the dual; additivity extends it to sums. The components
   are invertible, so `bidual_integral` holds by construction.
-/
theorem datum_naturality_of_kflat
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : Datum D l hl X E wE)
    (hflat : ∀ (P P' Q Q' : CochainComplex (IntegralHom.Modules.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)) ℤ)
        (hP : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) P)
        (hP' : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) P')
        (hQ : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) Q)
        (hQ' : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) Q')
        (f : P ⟶ P') (g : Q ⟶ Q'),
        A.ordinary.tensor.map (Prod.mkHom (DerivedCategory.Q.map f)
          (DerivedCategory.Q.map g)) ≫
            (A.symmetry.swap (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj Q')).hom =
          (A.symmetry.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
            A.ordinary.tensor.map (Prod.mkHom (DerivedCategory.Q.map g)
              (DerivedCategory.Q.map f))) :
    ∃ A' : Datum D l hl X E wE,
      A'.ordinary = A.ordinary ∧
      ∀ (K L K' L' : IntegralHom.Derived.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X))
        (f : K ⟶ K') (g : L ⟶ L'),
        A'.ordinary.tensor.map (Prod.mkHom f g) ≫ (A'.symmetry.swap K' L').hom =
          (A'.symmetry.swap K L).hom ≫
            A'.ordinary.tensor.map (Prod.mkHom g f) := by
  classical
  clear hflat
  obtain ⟨s, hs⟩ := IntegralVerdier.presentation_symmetry X _ A.ordinary
  let U := IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves
  obtain ⟨a₀, s₀, m₀, t₀, hcats, hp, hU, hrest⟩ :=
    integral_verdier_biduality D l hl E X wE.omega wE.reduction
  have : U.IsEquivalence := hU
  let adj : U.rightOp ⊣ U := restrictedSelfAdjunction D l hl X E wE A s hs
  let b₀ : 𝟭 (sfIntegralConstructibleCategory l E X) ≅ U.rightOp ⋙ U := asIso adj.unit
  have hb₀ (K : sfIntegralConstructibleCategory l E X) :
      b₀.hom.app K = ObjectProperty.homMk
        (IntegralVerdier.delta X A.ordinary s wE.omega.obj K.obj) := by
    apply ObjectProperty.hom_ext
    change (A.ordinary.adjunction _).homEquiv _ _
        ((s.swap _ _).hom ≫
          ((A.ordinary.adjunction K.obj).homEquiv _ _).symm (𝟙 _)) = _
    rw [Adjunction.homEquiv_symm_id]
    rfl
  let : A.dual.Additive := A.additive
  obtain ⟨b, hb⟩ := ScalarLocalization.biduality
    (Padic.coefficientExtensionUniformizer l E) U A.dual A.objects A.pure b₀
  refine ⟨{ A with symmetry := s, bidual := b, bidual_integral := ?_ }, rfl, hs⟩
  intro K
  exact (hb ((sfRationalConstructibleLocalization l E X).obj K)).trans
    (heq_of_eq (congrArg ((sfRationalConstructibleLocalization l E X).map) (hb₀ K)))

end WeilConjectures.RationalVerdier
