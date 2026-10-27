/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion
import Sheaf.AlgebraicGeometry.FppfLocalRepresentationsFullyFaithful

/-! # Invertible multiplication on semiabelian algebraic spaces

Source: Milne, Algebraic Groups (2017), Section 8.21, p.152, and Theorem 12.9(b),
pp.233--234; Stacks, Tags 0BFG, 0BFH, 03RP, 00UC, 02W5 and 0BLZ.
(blueprint: lem-sfb-semiabelian-invertible-multiplication)

The commutative group law is a group-valued functor, identified with the space's
functor of points. The kernel and local-surjectivity hypotheses are on fppf sheaves,
without assuming that the middle group is a scheme. Multiplication is the actual
pointwise power map, transported through the specified identification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.AlgebraicSpace

/-- Multiplication by `n` on a presheaf of commutative groups, in multiplicative notation.
The components are `x ↦ x ^ n`; restriction commutes with them because it is a group
homomorphism. Source: Milne, Algebraic Groups, Section 8.21 and Theorem 12.9(b)
(blueprint: lem-sfb-semiabelian-invertible-multiplication). -/
def commutativeGroupPresheafMultiplication {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ CommGrpCat.{u}) (n : ℕ) :
    F ⋙ forget CommGrpCat ⟶ F ⋙ forget CommGrpCat where
  app T := ↾fun x ↦ x ^ n
  naturality {T U} f := by
    ext x
    exact ((F.map f).hom.map_pow x n).symm

/-- Invertible positive multiplication on a semiabelian group algebraic space is
representable, finite, étale and surjective, on every scheme test.

Source: Milne, Algebraic Groups, Section 8.21, p.152, Theorem 12.9(b), pp.233--234;
Stacks, Tags 0BFG, 0BFH, 03RP, 00UC, 02W5, 0BLZ.
(blueprint: lem-sfb-semiabelian-invertible-multiplication).

Proof:
1. For units u_j in a k-algebra B, successively adjoin roots z_j of z_j^n-u_j.
   The monic-quotient basis (lem-weil-pbc-monic-quotient-free) makes each extension
   finite free. Each z_j is a unit and n is a unit, so the derivative is a unit.
   The standard étale calculation (lem-weil-pbc-standard-etale-monic-derivative)
   and finite/étale composition make the resulting root scheme finite étale.
   Roots in algebraically closed residue fields prove surjectivity. For rank zero
   this is Spec B itself.
2. By lem-sc-isogeny-facts and lem-sc-mult-n-etale-kernel, multiplication on A is
   finite étale surjective. For a scheme U and y in G(U), form
   W = U ×_[q(y),A,n] A. Finite and étale base change and
   lem-trf-fppf-covering-base-change make W → U finite étale surjective.
3. The sheaf V = U ×_[y,G,n] G maps to W. Fppf local surjectivity of q lifts the
   universal section a of A(W) to sections g_i of G on an affine fppf cover W_i.
   The kernel square identifies y - n g_i with a tuple of units d_i in the torus.
4. Translation t ↦ g_i + t, with inverse x ↦ x - g_i, identifies V ×_W W_i
   with the simultaneous root functor t_j^n = d_ij, on all test schemes.
   Step 1 therefore represents it by a finite étale surjective W_i-scheme.
5. Lem-trf-fppf-local-representations-fully-faithful supplies the unique overlap
   isomorphisms, satisfying the cocycle condition since they identify the same
   sections of V. Lem-sfb-finite-etale-fppf-descent descends them to a finite étale
   W-scheme P representing V. Every point of W lifts through some W_i and its
   surjective root scheme, so P → W is surjective.
6. Compose P → W → U. Finite and étale composition give the asserted properties,
   and the composite is surjective. The representing isomorphism preserves the
   projection to U, so this proves exactly the claim for every U and y, including
   empty U and the zero-dimensional abelian quotient. -/
theorem semiabelian_invertible_multiplication
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : AlgebraicSpace (Spec (.of k)))
    (F : (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u})
    (e : F ⋙ forget CommGrpCat ≅ G.obj.obj)
    (hsmooth : MapIsLocally (@Smooth) (groupSpaceProjection G))
    (hsep : MapIsSeparated (groupSpaceProjection G))
    (hfinite : MapIsFiniteType (groupSpaceProjection G))
    (t : ℕ) (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A.X]
    (i : yonedaGrp.obj (MultiplicativeType.splitTorus k t) ⟶
      F ⋙ forget₂ CommGrpCat GrpCat)
    (q : F ⋙ forget₂ CommGrpCat GrpCat ⟶ yonedaGrp.obj A)
    (hkernel : IsPullback (Functor.whiskerRight i (forget GrpCat))
      (yoneda.map (toUnit (MultiplicativeType.splitTorus k t).X))
      (Functor.whiskerRight q (forget GrpCat)) (yoneda.map η[A.X]))
    (hlift : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (Functor.whiskerRight q (forget GrpCat)))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    IsRepresentableWith (fun _ _ p ↦ IsFinite p.left ∧ Etale p.left ∧ Surjective p.left)
      (e.inv ≫ commutativeGroupPresheafMultiplication F n ≫ e.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
