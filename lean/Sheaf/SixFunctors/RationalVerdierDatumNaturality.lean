/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # Descent of the signed symmetry naturality equation -/

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

/-- K-flat naturality of the Koszul representative swap descends through K-flat
resolutions to arbitrary derived maps in the ordinary tensor presentation.
Source: blueprint thm-coef-rational-verdier, proof step 5
(blueprint: lem-coef-rational-verdier-datum-naturality).

Proof: replace each derived object by a K-flat representative and lift each derived map
to a roof. Naturality of the chain-level signed swap gives commutative squares for the
chosen representatives. The representative isomorphisms and their inverses transport
these squares to the derived category; independence of the roofs follows from
functoriality of the derived localization. -/
theorem datum_naturality_of_kflat
    -- STATEMENT-DISPUTED: `SignedSymmetry` constrains `swap` only on literal
    -- K-flat representatives.  Its `swap` family has no naturality or
    -- normalization condition at arbitrary derived objects, so changing one
    -- non-K-flat component by an automorphism preserves `hflat` and all
    -- structure fields while changing the displayed conclusion.  A valid
    -- descent theorem needs an additional naturality/transport hypothesis.
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
    ∀ (K L K' L' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : L ⟶ L'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' L').hom =
        (A.symmetry.swap K L).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f) := by
  sorry

end WeilConjectures.RationalVerdier
