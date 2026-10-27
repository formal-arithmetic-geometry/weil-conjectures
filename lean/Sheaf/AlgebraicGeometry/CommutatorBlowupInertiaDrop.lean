/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.SchemeActionFixedIdeal
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.BlowupUniversal

/-! # Commutator-fixed blowups strictly decrease nonabelian inertia

Source: ILO, Travaux de Gabber, VI Proposition 4.8, printed p.79, and
VIII 2.2.4(i), 4.2.13, printed p.122
(blueprint: lem-per-commutator-blowup-inertia-drop).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Blowing up the commutator fixed scheme decreases the specified nonabelian inertia.
The equality `hI` pins the center to its actual equalizer-ideal construction. Inertia
being proper is expressed by an element of H failing to fix the geometric point.
Geometric points above x may have an arbitrary algebraically closed extension field,
with the structural map `s` recording the comparison to x's geometric field.

Source: ILO VI Proposition 4.8 and VIII 2.2.4(i), 4.2.13
(blueprint: lem-per-commutator-blowup-inertia-drop).

Proof:
1. Let Z be the fixed scheme, J its ideal in the local ring A at x, and m the maximal
ideal. Equalizer equations give J = (u(a)-a : u in [H,H], a in A). Conjugation preserves
[H,H], hence H preserves Z and its ideal. Inertia acts trivially on A/m. Use the kernel
ideal and geometric residue field interfaces of def-sbc-closed-immersion-ideal-sheaf,
def-weil-geometric-point and def-weil-residue-field.
2. Principalization (thm-nagata-blowup-principalizes-center) makes the extended ideal L
invertible. The blowup universal property (thm-nagata-blowup-universal-property) lifts
each H-automorphism uniquely; uniqueness supplies the action laws and equivariance.
3. On E = J/mJ, average over K = [H,H]. Tameness makes |K| invertible. The average of
each generator u(a)-a vanishes by the permutation v maps to vu of K. Thus the averaging
operator is zero, also after extension of the residue field. Any K-equivariant quotient
with trivial K-action must therefore be zero.
4. If H fixed a point upstairs, L's fibre there would be a one-dimensional H-module.
The extended ideal construction (def-nagata-extended-ideal) gives an equivariant
surjection E tensor Omega onto this fibre. Its H-action is a character, trivial on K,
contradicting step 3 and its nonzero rank-one fibre (def-nagata-invertible-ideal).
5. For p from W, invertibility of its extended ideal gives a unique factor r by the same
blowup universal property. The two composites with each H-element lift the same map,
so uniqueness makes r equivariant. Normality and maximal domination are retained as
stated, though this ordinary-blowup factorization does not need them.
6. Equivariance sends the stabilizer of each geometric point of W into that of its image
in the blowup. The latter is proper by step 4, so the former is proper. Empty fibres
make the corresponding assertions vacuous.
-/
theorem commutatorFixed_blowup_inertia_drop
    (X : Scheme.{u}) [IsNoetherian X] [X.IsSeparated] (hregular : IsRegularScheme X)
    (G : Type v) [Group G] [Finite G] (a : G →* Aut X)
    (htame : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      IsUnit (Nat.card {g : G // t ≫ (a g).hom = t} : Ω))
    (hfree : ∃ U : X.Opens, Dense (U : Set X) ∧
      (∀ (g : G) (x : X), (a g).hom x ∈ U ↔ x ∈ U) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) (g : G),
        t default ∈ U → t ≫ (a g).hom = t → g = 1)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ x ≫ (a g).hom = x)
    (hnonabelian : ∃ g h : H, g * h ≠ h * g)
    (I : X.IdealSheafData) (hI : I = schemeActionFixedIdeal a ⁅H, H⁆) :
    ∃ b : H →* Aut I.blowup,
      (∀ h : H, (b h).hom ≫ I.blowupMap = I.blowupMap ≫ (a h).hom) ∧
      (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
        (s : Spec (.of Ω') ⟶ Spec (.of Ω)) (y : Spec (.of Ω') ⟶ I.blowup),
        y ≫ I.blowupMap = s ≫ x → ∃ h : H, y ≫ (b h).hom ≠ y) ∧
      ∀ (W : Scheme.{u}) (c : H →* Aut W) (p : W ⟶ X),
        (∀ w : W, IsDomain (W.presheaf.stalk w) ∧
          IsIntegrallyClosed (W.presheaf.stalk w)) →
        Set.MapsTo p (genericPoints W) (genericPoints X) →
        (∀ h : H, (c h).hom ≫ p = p ≫ (a h).hom) →
        (I.comap p).IsInvertible →
        (∃! r : W ⟶ I.blowup, r ≫ I.blowupMap = p) ∧
        (∀ r : W ⟶ I.blowup, r ≫ I.blowupMap = p →
          ∀ h : H, (c h).hom ≫ r = r ≫ (b h).hom) ∧
        ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
          (s : Spec (.of Ω') ⟶ Spec (.of Ω)) (w : Spec (.of Ω') ⟶ W),
          w ≫ p = s ≫ x → ∃ h : H, w ≫ (c h).hom ≠ w := by
  sorry

end AlgebraicGeometry
