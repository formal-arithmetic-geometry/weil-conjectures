/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierReductionPairingTransition
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierReductionPairingDelta

/-! # Reduction of signed evaluation pairings

Source: Stacks Project, Tags 06YL and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The two coefficient compatibility identities for normalized evaluation: its
finite transition square, and reduction of its double-dual transpose.

Source: thm-coef-integral-verdier proof steps 4 and 6; the chain calculations of
lem-coef-integral-hom-reduction and lem-weil-delta-restriction
(blueprint: lem-sf-integral-verdier-reduction-pairing).

Proof: represent each source by a K-flat complex and omega by a K-injective
complex. The quotient has its two-term perfect resolution. The ordinary
coefficient unit sends x to 1 tensor x; quotient transitions preserve this
unit. The normalized tensor comparison multiplies the two scalar factors.
On homogeneous sections, reduction of Hom sends f tensor q to the map
x to (-1)^(degree(q)*degree(x)) f(x) tensor q. Substituting these formulas in
evaluation proves its square with quotient transitions. The scalar adjunction
then gives the first identity, after inserting the specified isomorphisms r
and the restricted Hom comparisons; their consecutive inverse factors cancel.
For the second identity, uncurry the left side with respect to the finite
adjunction for the finite dual of K. The evaluation compatibility and
all-transpose equation identify it with reduction of interchanged evaluation.
The tensor comparison preserves the signed swap: both chain maps send
x_i tensor y_j to (-1)^(ij) y_j tensor x_i after scalar multiplication.
This is exactly the inverse transpose of the finite delta. Injectivity of
the finite adjunction proves the equality. The inverse of the comparison at K
occurs because the Hom variable is contravariant. These calculations are
independent of constructibility, boundedness, and the chosen reductions r. -/
theorem reductionPairing
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
    (hs : ∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (t : ∀ n : ℕ, SignedSymmetry X (integralCoefficientCommRingSheaf l E X n)
      (m n).target)
    (ht : ∀ (n : ℕ) (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      (m n).target.tensor.map (Prod.mkHom f g) ≫ ((t n).swap K' L').hom =
        ((t n).swap K L).hom ≫ (m n).target.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheaf l E X D hl)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (het : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      (m n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((m n).target.adjunction K').counit.app W =
      (m n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((m n).target.adjunction K).counit.app W)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (h : ∀ (K : Ambient l E X) (n : ℕ), IsIso (comparison l E X D hl (m n) ω r K)) :
    (∀ (K : Ambient l E X) (n : ℕ),
      a.tensor.map (Prod.mkHom (𝟙 K) (finiteTransition l E X D hl m ω r K (h K) n)) ≫
        finiteEvaluation l E X D hl m K n =
      finiteEvaluation l E X D hl m K (n + 1) ≫ dualizingTransition l E X D ω r n) ∧
    (∀ (K : Ambient l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E X n).map (delta X a s ω.obj K) ≫
        comparison l E X D hl (m n) ω r ((dual l E X ω.obj).obj (op K)) ≫
        (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (@asIso _ _ _ _ (comparison l E X D hl (m n) ω r K)
            (h K n)).inv.op (𝟙 (integralDualizingFiniteTerm l E D X n))) =
      delta X (m n).target (t n) (integralDualizingFiniteTerm l E D X n)
        ((scalarReductionDerivedExtension l E X n).obj K)) := by
  constructor
  · exact reductionPairing_transition D l hl E X a s hs m t ht he het ω r h
  · exact reductionPairing_delta D l hl E X a s hs m t ht he het ω r h

end WeilConjectures.IntegralVerdier
