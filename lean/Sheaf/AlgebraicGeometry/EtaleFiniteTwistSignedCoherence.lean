/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistLocalBases
/-! # Coherent ordinary pullback and multiplication of signed finite Tate powers -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
/-- Ordinary finite Tate comparisons preserve local basis tensors and evaluation.
Source: Stacks Project, Etale Cohomology, Tags 03PK and 03Q1; Modules on Sites,
Tags 03EL, 03EM and 04TT (blueprint: lem-asd-finite-twist-signed-coherence).
Proof: Use finiteEtaleTwistCommonLocalBases to fix a common cyclic roots cover.
The normalized roots comparison is an isomorphism by the source library's
isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit. Its additive
adjunct preserves powers, hence is ZMod m-linear. Extend scalars to A and
sheafify; on pure tensors this sends a tensor z to a tensor the pulled-back root.
Inverse image commutes with this extension since both are left adjoints; its
strong monoidal comparison gives the positive recursion and its constant-sheaf
comparison gives degree zero. For a positive line L, pull back evaluation
L tensor Hom(L,A) -> A and use the inverse positive comparison in the first
variable to obtain the negative comparison. On the common basis it sends the
dual basis to the dual of the pulled-back basis, so it is invertible and has the
stated evaluation identity. Define multiplication of signed powers by sending
basis[a] tensor basis[b] to basis[a+b], using concatenation and evaluation.
Replacing the line basis by u times that basis multiplies basis[a] by u^a for
all integers a, so the maps are independent of the basis and descend. The zero
and positive-successor maps are the displayed unit and identity maps by their
construction. Associativity, symmetry, and mixed evaluation follow by applying
them to basis tensors and multiplying coefficients. The identity, composition,
and tensor-compatibility diagrams for pullback likewise agree on these basis
tensors, since ring pullback preserves coefficients and the roots comparison
has its normalized adjunct. Equality of these sheaf maps is local, so the
identities descend from the common cover to the required global identities. -/
theorem finiteEtaleTwistSignedCoherence (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) :
    ∃ (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
      (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)),
(∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf m).obj.obj W),
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
        (c v hT hT' 1).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)).hom.app W z)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))),
      c v hT hT' 0 = (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      c v hT hT' (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1))) (finiteEtaleTateLine T m A hA)) ≪≫
          tensorIso (c v hT hT' (.ofNat (n + 1))) (c v hT hT' 1)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map
          ((ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T hA 0)) ≫ (c v hT hT' 0).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
          (finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
          tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' (.negSucc n)).hom ≫
          (ihom.ev (finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T' hA 0)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a)) ∧
    (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
        (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
        (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ),
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app
          (finiteEtaleTateSheaf A m T hA a) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT 0 a = λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT a 0 = ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      p T hT (.ofNat (n + 1)) 1 = Iso.refl _) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b d : ℤ),
      (p T hT a b).hom ▷ finiteEtaleTateSheaf A m T hA d ≫ (p T hT (a + b) d).hom =
        (α_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)
          (finiteEtaleTateSheaf A m T hA d)).hom ≫
        finiteEtaleTateSheaf A m T hA a ◁ (p T hT b d).hom ≫
          (p T hT a (b + d)).hom ≫
            eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_assoc a b d).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b : ℤ),
      (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
          (p T hT b a).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        (p T hT a b).hom) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      (p T hT (.ofNat (n + 1)) (.negSucc n)).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
            (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (finiteEtaleTateSheaf A m T hA 0)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map (p T hT a b).hom ≫
          (c v hT hT' (a + b)).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b) ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫ (p T' hT' a b).hom) := by sorry

end AlgebraicGeometry.Scheme
