/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.AlgebraicGeometry.TorusEulerCharacterData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.EquivariantCoherentProperPushforward
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.SmoothSectionRegularImmersion
import Sheaf.AlgebraicGeometry.EquivariantRegularSelfIntersection

/-! # Integral coherent fixed-point formula for a split torus

Source: Milne, Algebraic Groups (2017), Section 22d, proof of Theorem 22.50,
p.480, and Example 22.36, pp.473--474. The integral supporting statement is
agent-supplied, as recorded in the DAG.
(blueprint: lem-sfb-torus-coherent-fixed-point-formula)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.TorusEulerCharacter

open EquivariantCoherent EquivariantCoherent.ProperPushforwardData
open TrivialTorusCoherent (Character CharacterRing)

open Classical in
/-- The coherent fixed-point formula in the localization of the integer character ring.
The finite coproduct condition allows no fixed points. The universal fixedness test
includes all algebra extensions, and no characteristic hypothesis is imposed.

Source: Milne, Algebraic Groups (2017), Section 22d, proof of Theorem 22.50,
p.480; Example 22.36, pp.473--474, integral supporting statement in the DAG.
(blueprint: lem-sfb-torus-coherent-fixed-point-formula).

Proof:
1. Projectivity gives properness (lem-pc-projective-proper). Apply
   lem-sfb-equivariant-coherent-proper-pushforward to the structure morphism.
   This gives canonical finite-dimensional rational H-cohomology, eventually zero,
   with its restriction to T and the alternating pushforward class.
2. Apply lem-sfb-split-torus-representation-weight-decomposition. Group-like elements
   in a Laurent Hopf algebra are Laurent monomials, so the weights are exactly the
   group-scheme characters. Equivariant exact sequences are exact on each weight.
   Integer dimensions therefore identify R(T) with Z[X], multiplicatively. Over the
   finite union of fixed points the coherent group is the tuple of character rings.
3. A dual-number tangent vector is fixed precisely when it is tangent to the
   scheme-theoretic fixed subscheme. That subscheme is a finite union of reduced
   points, whose tangent spaces vanish. Hence tangent and cotangent have no zero weight.
4. Each rational point is a section of the smooth structure map. By
   lem-sfb-smooth-section-regular-immersion its inclusion is regular near the point.
   The conormal is m/m² with the dual derivative action. Exterior powers of a weight
   basis give the product of 1-e^χ, with multiplicity. Every factor is inverted in
   the stated localization; in dimension zero the product is 1.
5. By lem-sfb-torus-coherent-concentration lift [E] to the localized coherent group
   of the fixed subscheme. Apply lem-sfb-equivariant-regular-self-intersection.
   In each component the lift is ch(E_p) divided by the cotangent Euler product.
   For the empty fixed subscheme this is the empty tuple and [E] is zero locally.
6. Push forward to Spec F. Composition of proper pushforwards makes this the sum
   of the component characters. Its other description is the alternating sum of
   cohomology characters from step 1, giving the formula. All dimensions and
   Grothendieck groups are integral; no coefficient is reduced modulo char F.
-/
theorem torus_coherent_fixed_point_formula
    (F : Type u) [Field F] [IsAlgClosed F]
    (H : ProperPushforwardData.Group F) (T : ClosedSubgroup F H) (r : ℕ)
    (hsplit : Nonempty (Grp.mk T.group.scheme ≅ MultiplicativeType.splitTorus F r))
    (Z : Space F H) [Smooth Z.scheme.hom] [IsProjective Z.scheme.hom]
    (n : ℕ) (P : Over (Spec (.of F))) (i : P ⟶ Z.scheme)
    [IsClosedImmersion i.left]
    (p : Fin n → ((point F T.group).scheme ⟶ P))
    (hP : Nonempty (IsColimit (Cofan.mk P p)))
    (hfixed : ∀ (A : CommAlgCat.{u} F)
      (z : (algSpec (.of F)).obj (op A) ⟶ Z.scheme),
      (∃ x : (algSpec (.of F)).obj (op A) ⟶ P, x ≫ i = z) ↔
        ∀ (B : CommAlgCat.{u} F) (f : A ⟶ B)
          (t : (algSpec (.of F)).obj (op B) ⟶ T.group.scheme),
          (t ≫ T.map) • ((algSpec (.of F)).map f.op ≫ z) =
            (algSpec (.of F)).map f.op ≫ z)
    (D : ActionGroupoidModel H.scheme Z.scheme) (E : Coherent D)
    (hE : SheafOfModules.IsLocallyFree (R := Z.scheme.left.ringCatSheaf) (underlying E)) :
    (∀ V : Representation F T.group.scheme,
      DirectSum.IsInternal (weightSpace (Grp.mk T.group.scheme) V) ∧
        {χ : Character (Grp.mk T.group.scheme) |
          weightSpace (Grp.mk T.group.scheme) V χ ≠ ⊥}.Finite) ∧
    ∃ (R : RestrictedSpace F T Z)
      (DT : ActionGroupoidModel T.group.scheme (R.space F).scheme)
      (ET : Coherent DT)
      (V : ℕ → Representation F H.scheme)
      (W : ℕ → Representation F T.group.scheme)
      (B N : Fin n → Representation F T.group.scheme) (b : ℕ),
      IsRestriction F R E DT ET ∧
      (∀ q : ℕ, IsCohomologyRepresentation H Z E q (V q) ∧
        IsRestrictedRepresentation T (V q) (W q)) ∧
      (∀ q : ℕ, b < q → Subsingleton (V q).space) ∧
      (∀ j : Fin n, IsFixedFibrePair T.group (R.space F) ET (p j ≫ i) (B j) (N j)) ∧
      (∀ j : Fin n, weightSpace (Grp.mk T.group.scheme) (N j) 0 = ⊥) ∧
      (∑ q ∈ Finset.range (b + 1), (-1 : ℤ) ^ q •
        algebraMap (CharacterRing (Grp.mk T.group.scheme))
          (LocalizedRing (Grp.mk T.group.scheme))
          (formalCharacter (Grp.mk T.group.scheme) (W q))) =
        ∑ j : Fin n,
          algebraMap (CharacterRing (Grp.mk T.group.scheme))
              (LocalizedRing (Grp.mk T.group.scheme))
              (formalCharacter (Grp.mk T.group.scheme) (B j)) *
            Ring.inverse (algebraMap (CharacterRing (Grp.mk T.group.scheme))
              (LocalizedRing (Grp.mk T.group.scheme))
              (eulerFactor (Grp.mk T.group.scheme) (N j))) := by
  sorry

end AlgebraicGeometry.TorusEulerCharacter
