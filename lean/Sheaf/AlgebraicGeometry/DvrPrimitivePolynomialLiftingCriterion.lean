module

public import Sheaf.RepresentationTheory.RationalHopfModuleData
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import Sheaf.AlgebraicGeometry.GroupoidModuleLimitsColimits
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Primitive invariant polynomials imply symmetric-power lifting over a DVR

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 9.2.5(5),(5-double-prime), Remark 9.2.4(i), and Lemma 4.1.8, pp.502--504,521--523.
The primitive-vector formulation corrects the arbitrary-injection wording in Remark 9.2.7.
(blueprint: lem-sfb-dvr-primitive-polynomial-lifting-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Primitive invariant polynomial separation implies arbitrary symmetric-power lifting.
Source: Alper, Lemma 9.2.5(5),(5-double-prime), Remark 9.2.4(i), Lemma 4.1.8;
corrected primitive-vector reading of Remark 9.2.7.
(blueprint: lem-sfb-dvr-primitive-polynomial-lifting-criterion)

Proof:
1. A DVR is Noetherian, and the flat affine finitely presented group gives a flat
   Noetherian affine groupoid. No reductivity or completion regularity is needed.
2. Translate a rational module into its quasi-coherent groupoid module. On affine
   sections its linearization sends m tensor b to sum m_0 tensor m_1 b; the inverse
   uses the antipode. Counit and coassociativity give the identity and cocycle laws.
3. Coherent approximation and the affine module-section correspondence express M as
   a filtered colimit of finite rational modules. Represent a preimage of 1 at one
   finite stage N, so N to M to A remains surjective; N to M need not be injective.
4. The DVR resolution property supplies an equivariant finite free cover P to N.
   Its composite a : P to A is surjective. In V = P dual the vector a is invariant
   and primitive: if it belonged to the maximal-ideal multiple, every value of a
   would lie in that ideal, contradicting a(z) = 1. Apply the polynomial hypothesis.
5. The finite free evaluation map P to its bidual is an equivariant isomorphism.
   Transport the resulting polynomial f through this isomorphism and P to M.
   Symmetric functoriality preserves degree and invariance. On a product of linear
   generators, evaluation at a is the product of their a-values. Products span the
   homogeneous part, so the image under Sym(lambda), evaluated at 1, equals f(a) = 1.
-/
theorem symmetric_lifting_of_primitive_invariant_polynomials
    (A : CommRingCat.{u}) [IsDomain A] [IsDiscreteValuationRing A]
    (H : Scheme.{u}) [H.Over (Spec A)] [GrpObj (H.asOver (Spec A))]
    [IsAffine H] [Flat (H ↘ Spec A)]
    [LocallyOfFinitePresentation (H ↘ Spec A)]
    (hprimitive : ∀ (V : Type (max u w)) [AddCommGroup V] [Module A V]
      [Module.Free A V] [Module.Finite A V]
      (ρ : RationalHopfModule.Coaction A Γ(H, ⊤) V) (v : V),
      ρ.map v = v ⊗ₜ[A] (1 : Γ(H, ⊤)) →
      v ∉ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A V) →
      ∃ (n : ℕ) (_ : 1 ≤ n)
        (f : RationalHopfModule.degree A (Module.Dual A V) n),
        RationalHopfModule.symmetricMap A Γ(H, ⊤) (Module.Dual A V)
            (RationalHopfModule.dualMap A Γ(H, ⊤) V ρ) f =
          (f : SymmetricAlgebra A (Module.Dual A V)) ⊗ₜ[A] (1 : Γ(H, ⊤)) ∧
        SymmetricAlgebra.lift (Module.Dual.eval A V v) f = 1)
    (M : Type w) [AddCommGroup M] [Module A M]
    (ρ : RationalHopfModule.Coaction A Γ(H, ⊤) M)
    (lam : M →ₗ[A] A) (hlam : Function.Surjective lam)
    (hequiv : ∀ m : M, lam.rTensor Γ(H, ⊤) (ρ.map m) =
      (lam m) ⊗ₜ[A] (1 : Γ(H, ⊤))) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (q : RationalHopfModule.degree A M n),
      RationalHopfModule.symmetricMap A Γ(H, ⊤) M ρ.map q =
        (q : SymmetricAlgebra A M) ⊗ₜ[A] (1 : Γ(H, ⊤)) ∧
      SymmetricAlgebra.lift lam q = 1 := by
  sorry

end AlgebraicGeometry
