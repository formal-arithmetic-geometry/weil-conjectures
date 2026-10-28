/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

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
  sorry

end WeilConjectures.RationalVerdier
