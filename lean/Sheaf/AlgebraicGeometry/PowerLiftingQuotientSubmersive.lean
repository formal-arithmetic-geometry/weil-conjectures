/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.AffineActionStackPresentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.FlatAffineActionStackPresentation
import Sheaf.AlgebraicGeometry.AdequateModuliUniversallySubmersive

/-! # Power lifting and universal submersiveness of invariant quotients

Source: Alper, arXiv:1005.2398v3, Lemma 9.2.5(3), Theorems 9.1.4 and 5.3.1(3)
(blueprint: lem-sfb-power-lifting-quotient-submersive).

Rational actions use the existing scheme-action encoding: on affine schemes the
unit and associativity diagrams are dual to the counit and coassociativity laws.
With right coactions, inversion converts the dual right action to a left action;
this preserves invariants and equivariant maps. Equivariance is stated on the
scheme morphism whose underlying map is exactly Spec f. No smoothness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.SchemeAction

/-- Power lifting for all equivariant algebra surjections makes every affine base change
of the invariant quotient a surjection detecting open sets. The map is the prime-spectrum
map of l ↦ 1 tensor l, so its source is precisely Spec(E tensor_(E^H) L).
The existential in the equivariance hypothesis pins the morphism to Spec f;
`IsModHom` is the full equality of action morphisms, not a condition on k-points.
Source: Alper, arXiv:1005.2398v3, Lemma 9.2.5(3), Theorems 9.1.4 and 5.3.1(3)
(blueprint: lem-sfb-power-lifting-quotient-submersive).

Proof:
1. For R = E^H, use lem-sfb-flat-affine-action-stack-presentation to form the qcqs
algebraic stack X = [Spec E/H], its universally open surjective atlas and its qcqs
map phi to Spec R. Their composite is Spec of the invariant inclusion.
2. By lem-sfb-flat-affine-action-algebra-descent, any quasi-coherent algebra
surjection on X is a surjection D to D' of equivariant E-algebras, with global
sections identified naturally and multiplicatively with D^H and (D')^H. Forget to
k-algebras and apply the power-lifting hypothesis. Naturality and injectivity of
the sections/invariants identification give a section lifting the required power.
For the structure algebra the actual global-functions map is the identity of R.
3. Apply lem-sfb-global-power-lifting-adequacy to obtain an adequate moduli map.
Its criterion supplies lifts on every affine etale base change, including algebras
which are not pulled back from X. No arbitrary-base-change formula for invariants
is used.
4. Apply lem-sfb-adequate-moduli-universally-submersive to T = Spec L. The base
change of phi is surjective and detects open sets, without flatness of L over R.
5. The affine-spectrum and fibre-product universal properties identify the base
change of Spec E with Spec(E tensor_R L), and its projection with l ↦ 1 tensor l.
6. Its map to X times_(Spec R) T is a base change of the open surjective atlas.
Composing gives surjectivity. If the composite inverse image of V is open, its
image under this open surjection is the inverse image of V under the base change
of phi, hence open. Step 4 makes V open. The converse follows by continuity. -/
theorem power_lifting_quotient_submersive (k : Type u) [Field k]
    (H : Over (Spec (CommRingCat.of k))) [GrpObj H]
    [IsAffineHom H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (hlift : ∀ (D D' : Type u) [CommRing D] [CommRing D'] [Algebra k D] [Algebra k D']
      [ModObj H (affineActionScheme k D)] [ModObj H (affineActionScheme k D')]
      (f : D →ₐ[k] D'), Function.Surjective f →
      (∃ s : affineActionScheme k D' ⟶ affineActionScheme k D,
        s.left = Spec.map (CommRingCat.ofHom f.toRingHom) ∧
          Nonempty (IsModHom H s)) →
      ∀ b : affineInvariants k D' H,
        ∃ (n : ℕ) (_ : 0 < n) (a : affineInvariants k D H), f a = (b : D') ^ n)
    (E : Type u) [CommRing E] [Algebra k E] [Algebra.FiniteType k E]
    [ModObj H (affineActionScheme k E)] (L : Type v) [CommRing L]
    [Algebra (affineInvariants k E H) L] :
    Function.Surjective (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := affineInvariants k E H)
        (A := E) (B := L)).toRingHom) ∧
    ∀ V : Set (PrimeSpectrum L), IsOpen V ↔
      IsOpen (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight (R := affineInvariants k E H)
          (A := E) (B := L)).toRingHom ⁻¹' V) := by
  sorry

end AlgebraicGeometry.SchemeAction
