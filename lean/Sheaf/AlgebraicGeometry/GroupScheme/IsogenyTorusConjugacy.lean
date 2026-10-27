/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations

/-! # Uniqueness of reductive isogenies up to torus conjugation

Source: Milne, Algebraic Groups (2017), Proposition 23.7, printed p.486,
and Theorem 23.25, printed pp.492--493
(blueprint: lem-sfb-isogeny-torus-conjugacy).

Conjugation is written using the group of scheme morphisms into the target.
Thus the conclusion is scheme-theoretic, including over nonreduced test algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Two surjective reductive group homomorphisms with finite scheme-theoretic kernels
and identical pullbacks of torus characters differ by conjugation by a target torus
point. No separability or reducedness of either kernel is required.

Source: Milne, Proposition 23.7, p.486, and Theorem 23.25, pp.492--493
(blueprint: lem-sfb-isogeny-torus-conjugacy).

Proof plan:
1. By lem-sfb-affine-homomorphism-flat-image factor each map through its closed
   image by a faithfully flat map. By sbc-lem-smooth-geometrically-reduced the
   smooth target is reduced. Surjectivity puts the closed-image ideal in every
   prime, hence it is zero. Both original maps are therefore faithfully flat.
2. Coordinate characters of a splitting of T₀ separate maps, so aT = bT.
   By lem-sfb-isogeny-root-power-laws their common character pullback is injective
   with finite cokernel. If two root correspondences give u(β) = qα and
   u(β') = q'α, injectivity gives q'β = qβ'. The reduced root system and torsion-free
   character lattice of lem-sfb-reductive-borel-pair-structure give β = β' and q = q'.
3. Choose a simple-root base and root parametrizations. The root-power-laws give
   nonzero constants cα, dα for a and b. The corresponding target characters are
   integrally independent: pull back a relation and use independence of the source
   simple roots and positivity of qα. By lem-sfb-independent-torus-character-values
   choose t in T₀(F) with β(t) = dα/cα for every source simple root.
4. Put a' = Int(t) ∘ a. Conjugation preserves surjectivity and the finite kernel,
   and fixes the target torus. By lem-sfb-reductive-root-subgroup-parametrizations,
   a'(xα(z)) = yβ(β(t)cα z^qα) = yβ(dα z^qα) = b(xα(z)) over every test algebra.
5. Apply lem-sfb-isogeny-simple-root-rigidity: a' and b agree on the torus and
   on all simple root subgroups, hence as scheme morphisms. For an empty root set
   take t = 1; the same rigidity statement applies. No kernel is assumed reduced.
The final formula uses postcomposition by Int(t), as in the display in Milne 23.7. -/
theorem isogeny_torus_conjugacy {F : Type u} [Field F] [IsAlgClosed F]
    (G₁ G₀ T₁ T₀ : Grp (Over (Spec (.of F))))
    (hG₁ : ReductiveTorusCentralizer.IsReductive G₁)
    (hG₀ : ReductiveTorusCentralizer.IsReductive G₀)
    (i₁ : T₁ ⟶ G₁) (i₀ : T₀ ⟶ G₀)
    (hT₁ : ReductiveTorusCentralizer.IsMaximalTorus i₁)
    (hT₀ : ReductiveTorusCentralizer.IsMaximalTorus i₀)
    (hsplit₁ : ∃ r : ℕ, Nonempty (T₁ ≅ MultiplicativeType.splitTorus F r))
    (hsplit₀ : ∃ r : ℕ, Nonempty (T₀ ≅ MultiplicativeType.splitTorus F r))
    (a b : G₁ ⟶ G₀)
    (ha : Surjective a.hom.hom.left) (hb : Surjective b.hom.hom.left)
    (haker : IsFinite (GrpObj.ker a.hom.hom).hom)
    (hbker : IsFinite (GrpObj.ker b.hom.hom).hom)
    (aT bT : T₁ ⟶ T₀) (haT : i₁ ≫ a = aT ≫ i₀) (hbT : i₁ ≫ b = bT ≫ i₀)
    (hchars : ∀ χ : T₀ ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      aT ≫ χ = bT ≫ χ) :
    ∃ t : 𝟙_ (Over (Spec (.of F))) ⟶ T₀.X,
      b.hom.hom = (toUnit G₁.X ≫ t ≫ i₀.hom.hom) * a.hom.hom *
        (toUnit G₁.X ≫ t ≫ i₀.hom.hom)⁻¹ := by
  sorry

end AlgebraicGeometry
