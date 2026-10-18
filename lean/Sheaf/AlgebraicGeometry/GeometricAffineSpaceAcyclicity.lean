/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.KunnethGlobalSections
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
import Sheaf.AlgebraicGeometry.KummerAffineLine

/-!
# Finite-coefficient acyclicity of geometric affine space

Source: Milne, Lectures on Etale Cohomology, Section 16, Example 16.3 and the opening
paragraphs on twists, and Section 22
(blueprint: lem-per-geometric-affine-space-acyclicity).

All coefficients are lifted to the universe of the small-etale module sheaves. The
constants map is actual section pullback, followed by the normalized twist comparison
and the inverse of the degree-zero derived-to-underived comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The finite cyclic coefficient ring, lifted without changing its scalars.
Source: Milne Section 16 (blueprint: lem-per-geometric-affine-space-acyclicity). -/
abbrev geometricAffineCoefficient (ℓ n : ℕ) := ULift.{u + 1} (ZMod (ℓ ^ n))


/-- The canonical annihilation of the finite cyclic coefficient ring.
Source: Milne Section 16 (blueprint: lem-per-geometric-affine-space-acyclicity). -/
abbrev geometricAffineAnnihilation (ℓ n : ℕ) :
    ((ℓ ^ n : ℕ) : geometricAffineCoefficient.{u} ℓ n) = 0 :=
  congrArg (ULift.up : ZMod (ℓ ^ n) → geometricAffineCoefficient.{u} ℓ n)
    (ZMod.natCast_self (ℓ ^ n))
/-- The existing signed roots-of-unity twist with finite cyclic coefficients.
Source: Milne Section 16, opening paragraphs
(blueprint: lem-per-geometric-affine-space-acyclicity). -/
def geometricAffineTwist (ℓ n : ℕ) (T : Scheme.{u}) (t : ℤ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n)) :=
  Scheme.finiteEtaleTateSheaf (geometricAffineCoefficient.{u} ℓ n) (ℓ ^ n) T
    (geometricAffineAnnihilation ℓ n) t

/-- Ordinary integer-indexed small-etale cohomology of the finite twist.
Source: Milne Section 16, Example 16.3; Stacks Tag 03QQ
(blueprint: lem-per-geometric-affine-space-acyclicity). -/
def geometricAffineTwistCohomology (ℓ n : ℕ) (T : Scheme.{u}) (t q : ℤ) :
    ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n) :=
  (Etale.cohomology (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n)) T q).obj
    ((DerivedCategory.singleFunctor _ 0).obj (geometricAffineTwist ℓ n T t))

/-- The canonical comparison of a finite twist along a scheme morphism, obtained from the
normalized comparisons of the finite-twist dependency. This selects its second witness
from the full normalized existence statement: the root comparison is fixed by its monic
inclusion in G_m, the first twist by the pure-tensor formula, degree zero by constants,
positive twists by recursion, and negative twists by evaluation on a locally free line.
Thus these normalizations determine the chosen maps up to equality.
Source: Milne Section 16 (blueprint: lem-per-geometric-affine-space-acyclicity). -/
@[irreducible]
noncomputable def geometricAffineTwistPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0)
    (T T' : Scheme.{u}) (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
    (hT' : IsUnit (m : Γ(T', ⊤))) (a : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} A) v).obj
        (Scheme.finiteEtaleTateSheaf A m T hA a) ≅
      Scheme.finiteEtaleTateSheaf A m T' hA a :=
  Classical.choose (Classical.choose_spec
    (Scheme.etaleFiniteTwistPullback A m hm hA)) v hT hT' a

/-- Transport invertibility of a natural number along a ring homomorphism.
Source: Milne Section 16 (blueprint: lem-per-geometric-affine-space-acyclicity). -/
abbrev geometricAffineUnitMap {R S : Type u} [CommRing R] [CommRing S]
    (m : ℕ) (φ : R →+* S) (h : IsUnit (m : R)) : IsUnit (m : S) :=
  (map_natCast φ m) ▸ h.map φ

/-- The canonical constants map from the twist's sections over Spec k to H⁰ of affine
space. It uses section pullback, the normalized signed twist pullback comparison, and
resolution augmentation; there is no root or basis choice.
Source: Milne Section 16, Example 16.3 and the twist paragraph
(blueprint: lem-per-geometric-affine-space-acyclicity). -/
def geometricAffineConstantsMap (k : Type u) [Field k] (ℓ n r : ℕ)
    (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (t : ℤ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n))).obj
        (geometricAffineTwist ℓ n (Spec (.of k)) t) ⟶
      geometricAffineTwistCohomology ℓ n (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))) t 0 :=
  Etale.globalSectionsUpperStarMap
      (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n))
      (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k)) ↘ Spec (.of k))
      (geometricAffineTwist ℓ n (Spec (.of k)) t) ≫
    (Sheaf.Γ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))).smallEtaleTopology
      (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n))).map
        (geometricAffineTwistPullback (geometricAffineCoefficient.{u} ℓ n) (ℓ ^ n)
          (pow_pos hℓ.pos n) (geometricAffineAnnihilation ℓ n)
          (Spec (.of k)) (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k)))
          (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k)) ↘ Spec (.of k))
          (geometricAffineUnitMap (ℓ ^ n) (Scheme.ΓSpecIso (.of k)).inv.hom
            ((Nat.cast_pow (α := k) ℓ n).symm ▸ hℓk.pow n))
          (geometricAffineUnitMap (ℓ ^ n)
            ((Scheme.ΓSpecIso (.of k)).inv ≫
              (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k)) ↘ Spec (.of k)).appTop).hom
            ((Nat.cast_pow (α := k) ℓ n).symm ▸ hℓk.pow n))
          t).hom ≫
    (Functor.rightDerivedZeroIsoSelf
      (Sheaf.Γ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))).smallEtaleTopology
        (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n)))).inv.app
          (geometricAffineTwist ℓ n (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))) t) ≫
    (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (Sheaf.Γ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))).smallEtaleTopology
        (ModuleCat.{u + 1} (geometricAffineCoefficient.{u} ℓ n)))
      (geometricAffineTwist ℓ n (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))) t) 0).inv

/-- Geometric affine space has only degree-zero ordinary finite-twist cohomology, and
its degree-zero isomorphism is the canonical pullback of constant sections.
Source: Milne Section 16, Example 16.3, twist paragraph, and Section 22
(blueprint: lem-per-geometric-affine-space-acyclicity).

Proof:
1. Put m = ℓ^n. By lem-sc-primitive-root choose a primitive m-th root in k. Its powers
   split z^m-1 with pairwise unit differences, identifying the constant cyclic sheaf
   with μ_m on every k-scheme by clopen partitions. Signed tensor powers and dual bases
   trivialize all twists, compatibly with lem-asd-etale-finite-twist-pullback. The basis
   is auxiliary and is absent from the constants map.
2. Negative cohomology vanishes because sheaves have resolutions starting at zero
   (def-weil-pbc-sites-and-cohomology). The canonical module/abelian derived direct-image
   comparison (lem-weil-pbc-module-abelian-derived-direct-image-comparison), together with
   the point-topos equivalence (lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant),
   identifies the two coefficient interpretations, preserving constants. For r=0 use
   def-sbc-affine-space and lem-sf-separably-closed-torsion-cd: the constants map is identity
   under the canonical affine-zero-space identification, and positive cohomology vanishes.
3. Apply thm-pur-kummer-affine-line to N=n and the free rank-one coefficient module.
   Its degree-zero map becomes the constants map under step 1, and higher groups vanish.
   By lem-weil-pbc-unbounded-derived-iso-cohomology the derived constants map is invertible.
4. Induct using A^j × A¹ = A^(j+1), given on polynomial generators. The factors are finite
   type. Apply thm-kun-0f1p over the separably closed field k with invertible modulus m.
   lem-kun-pullback-constant identifies the external coefficient and lem-kun-tensor-unit
   removes the tensor unit. The functor def-kun-derived-tensor preserves the two constants
   isomorphisms, so their composite with Künneth is invertible.
5. In def-kun-kunneth-map the two pulled-back counits and coefficient multiplication
   send a ⊗ b to the constant ab by the adjunction triangle identity. Hence this composite
   is the specified constants map. Equivalently maps from the free module Λ[0] are
   determined by H⁰. Induction gives all the asserted vanishing. Transport through the
   pullback-compatible trivializations of step 1 to every signed twist. The resulting
   degree-zero map remains actual pullback, independently of the auxiliary primitive root.
-/
theorem geometricAffineSpaceAcyclicity (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (hn : 1 ≤ n)
    (r : ℕ) (t : ℤ) :
    IsIso (geometricAffineConstantsMap k ℓ n r hℓ hℓk t) ∧
      ∀ q : ℤ, q ≠ 0 → IsZero
        (geometricAffineTwistCohomology ℓ n
          (AffineSpace (ULift.{u} (Fin r)) (Spec (.of k))) t q) := by
  sorry

end AlgebraicGeometry
