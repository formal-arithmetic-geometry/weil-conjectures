/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker R3
-/
module

public import Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.FieldTheory.GaloisAutomorphismExtension

/-!
# Constant prime-field quotient identification

Source: Stacks Project, Tag 04JQ; blueprint `lem-sc-affine-generic-second`,
proof paragraphs 1--2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 04JQ; blueprint `lem-sc-affine-generic-second`,
proof paragraphs 1--2.
(blueprint: lem-sc-primary-constant-quotient-identification)

Proof: Let Q be the explicitly constructed additive quotient B/A. Its elements are
represented by x in B. The condition ell*x in A implies ell*q=0 for every q in Q.
An abelian group annihilated by ell has the canonical ZMod ell module structure,
induced by integer multiplication modulo ell. Because ell is prime this ring is a
field. Q is finite as a quotient of a subgroup of the finite ambient module, hence
finite-dimensional over this field. Choose a finite basis of cardinal d. Its coordinate
map identifies Q with d copies of ZMod ell, additively and equivariantly since the
specified action on both sides is trivial. Under C, a constant sheaf has its value as
geometric stalk and trivial monodromy: constant germs stay constant when the pointed
lift changes. Conversely the canonical stalk/action comparison and full faithfulness
identify the associated sheaf of a trivial representation with that constant sheaf.
Preservation of finite products and coproducts transports the coordinate isomorphism
to finite biproducts, with the zero-dimensional case giving the zero sheaf. Pullback
across e preserves constant sheaves and binary biproducts; induction on d identifies
this biproduct with the displayed Nat.rec expression. When A=B or B=0, d=0 works.
There is no terminal sheaf or chain in this assertion. -/
theorem primaryTrivialQuotient_constant
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (H : OpenSubgroup (Gal(Ks/K))) (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K))) [Finite R.obj.V]
    (A B : AddSubgroup R.obj.V) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hkill : ∀ x : R.obj.V, x ∈ B → ℓ • x ∈ A) :
    ∃ d : ℕ, Nonempty
      (primaryAssociatedSheaf K Ks H Ω C T e (primaryTrivialQuotient K Ks H R A B) ≅
        Nat.rec (0 : _) (fun _ V ↦ V ⊞ T.constantZMod ℓ) d) := by sorry

end AlgebraicGeometry.Scheme
