/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.RepresentationTheory.LAdic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport

/-! # Continuity of the rationalized finite-path action

Source: Deligne, Weil II (1.1.1) b)-c), (1.1.6).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme
open FiniteEtale

/-- Finite-cover evaluation makes the rationalized inverse-limit action continuous.
Source: Deligne, Weil II (1.1.1) b)-c), (1.1.6), pp.146-150; the integral and rational
steps of the proof of `cor-galois-lisse-representations`.
(blueprint: new-b5-rational-finite-path-continuity).

Proof: each level stalk is a finite module over the quotient of the coefficient
integers by the specified uniformizer power. Its finite-cover germs exhaust the
stalk. For such a germ the displayed finite action is evaluation on a finite etale
cover, so its orbit map is continuous for the discrete topology. The projection
identity transfers these orbit maps to the inverse limit. The surjective transition
maps with their specified kernels identify the inverse limit with a finite complete
module over the coefficient integers, with quotients exactly the level stalks.
Its adic topology is consequently the topology induced from the product of these
finite discrete stalks. The finite-level actions therefore give a jointly continuous
integral action: at a fixed level, choose a lift of a stalk element; its open
stabilizer together with the kernel of that projection is a product neighbourhood
on which the action has the prescribed value. The tensor formula identifies the
rational action with localization of this integral action. A finite set of integral
generators spans the rational fibre, proving finite dimension. Inverting the
uniformizer on a finite module identifies the quotient topology on each bounded
denominator lattice with the spectral-norm module topology; these lattices cover
the rational fibre and are open. Continuity on each such lattice, followed by
translation, proves joint continuity of the rational action. Torsion is killed on
rationalization; zero fibres and rank-zero systems satisfy the same argument. -/
theorem rationalFinitePathAction_continuous
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (t : Spec (.of Ω) ⟶ Y) (F : LisseRationalSheaf l E Y)
    (A : Aut (fiber t) →
      (lisseIntegralFiber l E Y t F.integral ≃ₗ[Padic.coefficientExtensionIntegers l E]
        lisseIntegralFiber l E Y t F.integral))
    (B : ∀ n : ℕ, Aut (fiber t) →
      (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          (F.integral.obj.obj (op n)) ≃ₗ[Padic.coefficientExtensionIntegers l E]
       ((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          (F.integral.obj.obj (op n))))
    (hB : ∀ (n : ℕ) (g : Aut (fiber t)) (P : Y.FiniteEtale)
      (a : (fiber t).obj P) (s : (F.integral.obj.obj (op n)).obj.obj (op P.obj)),
      B n g ((pointSmallEtale t).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩
        (F.integral.obj.obj (op n)).obj s) =
      (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber P.obj ⟨g.hom.app P a⟩
        (F.integral.obj.obj (op n)).obj s)
    (hA : ∀ (g : Aut (fiber t)) (n : ℕ)
      (x : lisseIntegralFiber l E Y t F.integral),
      limit.π (F.integral.obj ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber) (op n)
          (A g x) =
        B n g (limit.π
          (F.integral.obj ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber) (op n) x))
    (ρ : Aut (fiber t) →*
      (lisseRationalFiber l E Y t F ≃ₗ[E] lisseRationalFiber l E Y t F))
    (hρ : ∀ (g : Aut (fiber t)) (a : E)
      (x : lisseIntegralFiber l E Y t F.integral),
      ρ g (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] x) =
        a ⊗ₜ[Padic.coefficientExtensionIntegers l E] (A g x)) :
    Representation.IsContinuousCoefficient l E (ProfiniteGrp.of (Aut (fiber t)))
      (lisseRationalFiber l E Y t F) ρ := by sorry

end AlgebraicGeometry.Scheme
