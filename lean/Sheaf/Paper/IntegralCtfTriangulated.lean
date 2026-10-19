/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.IntegralConstructibleTriangulated
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import all Sheaf.Paper.FiniteCtfTriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.IntegralDerivedReduction

/-!
# Integral constructible complexes with uniformly finite Tor amplitude

Source: Stacks Project, Cohomology on Sites, Tag 08G2, part (2), applied to each
reduction; Weil blueprint, integral-stage paragraph of `def-weil-finite-tor-amplitude`
(blueprint: lem-weil-integral-ctf-triangulated).
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The property `P` in the integral triangulation lemma: bounded constructibility and
one ordered Tor interval valid simultaneously for every positive reduction exponent.
The index `n : ℕ` denotes exponent `n + 1`, as in `integralDerivedReduction`.
Source: Weil blueprint, integral-stage paragraph of `def-weil-finite-tor-amplitude`;
Stacks Project, Tag 08FZ (blueprint: lem-weil-integral-ctf-triangulated). -/
noncomputable def integralCtfProperty
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (completedIntegralDerivedCategory l E Y D hl) :=
  boundedConstructibleDerivedCompleteIntegral D l hl E Y ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((integralDerivedReduction l E Y D hl n).obj K) a b

-- The existing signature names an index used only by instance inference.
set_option linter.unusedVariables false in
/-- The integral finite-Tor property is isomorphism invariant and cuts out a full
triangulated subcategory: zero belongs, every integer shift preserves it in both
directions, and it is closed under middle vertices of distinguished triangles.
Source: Stacks Project, Tag 08G2 (2); Weil blueprint, integral-stage paragraph of
`def-weil-finite-tor-amplitude` (blueprint: lem-weil-integral-ctf-triangulated).

Proof plan (the node's six steps):
1. For each $j\geq1$ write $R_j(K)=K\otimes^L_{\mathcal O_E}A_{E,j}$. By the derived-reduction
definition this is change of rings along $\pi_j:\widehat{\mathcal O}_{E,Y}\to(A_{E,j})_Y$. Apply
the exact derived-change-of-rings functor to this morphism of sheaves of commutative rings on the
same site. Thus $R_j$ preserves distinguished triangles, zero objects and isomorphisms, and has
the shift comparison $R_j(K[m])\cong R_j(K)[m]$. If $K\in D^b_c(Y,\mathcal O_E)$, every $R_j(K)$
is bounded constructible by the integral-category definition. All finite-stage applications below
are consequently on the small pro-etale site, with coefficient ring $A_{E,j}$. Uses:
def-weil-integral-derived-reduction, lem-pur-derived-change-of-rings,
def-weil-derived-complete-integral-detailed.
2. Isomorphism invariance: if $K\cong L$ and $P(K)$ holds, the integral constructible
triangulated-subcategory lemma gives $L\in D^b_c(Y,\mathcal O_E)$. For every $j$ the reduction
isomorphism $R_j(K)\cong R_j(L)$ induces, after derived tensor with any degree-zero
$A_{E,j}$-module sheaf $N$, isomorphisms on cohomology. The same reasoning applies to any
isomorphism between two objects of $D(Y_{\mathrm{proet}},A_{E,j})$, so Tor amplitude in a
specified interval is invariant under such an isomorphism. Therefore the same uniform interval
$[a,b]$ works for $L$. For the zero object, the integral subcategory contains zero, and $R_j(0)$
is zero. Derived tensor of zero with any $N$ is computed by the zero K-flat complex and is zero,
so $[0,0]$ works simultaneously for all $j$. Uses: lem-weil-integral-constructible-triangulated,
def-weil-proetale-tor-amplitude, def-weil-derived-tensor.
3. Let $P(K)$ have uniform Tor interval $[a,b]$, and fix $m\in\mathbf Z$. The integral
constructible subcategory contains $K[m]$. For each $j\geq1$, specialize
[lem-weil-finite-ctf-triangulated] with the same prime $\ell$, extension $E$, valuation ring and
uniformizer, scheme $Y$, and $n=j$. Its coefficient ring is exactly $A_{E,j}$; the finite-stage
statement explicitly binds these coefficient data to the coefficient-extension definition. Every
$R_j(K)$ is bounded constructible by step 1 and has Tor amplitude in $[a,b]$ by $P(K)$, so the
explicit shift clause of the finite-stage triangulated lemma gives Tor amplitude $[a-m,b-m]$ for
$R_j(K)[m]$. The comparison in step 1 and isomorphism invariance in step 2 give the same interval
for $R_j(K[m])$, independently of $j$. Thus $P(K[m])$. Conversely apply this implication with $-m$
to $K[m]$ and use $(K[m])[-m]\cong K$ and step 2. Uses:
lem-weil-integral-constructible-triangulated, lem-weil-finite-ctf-triangulated.
4. Let $K\to L\to M\to K[1]$ be distinguished, with $P(K)$ and $P(M)$. Choose their uniform Tor
intervals $[a_K,b_K]$ and $[a_M,b_M]$ and put $a=\min(a_K,a_M)$ and $b=\max(b_K,b_M)$. Then $a\leq
b$. For every $j$ and every degree-zero $A_{E,j}$-module sheaf $N$, an integer outside $[a,b]$ is
outside each original interval, so the defining tensor cohomology vanishes for both $R_j(K)$ and
$R_j(M)$. Both therefore have Tor amplitude in the common interval $[a,b]$, which is independent
of $j$. Uses: def-weil-proetale-tor-amplitude.
5. The integral constructible triangulated-subcategory lemma gives $L\in D^b_c(Y,\mathcal O_E)$.
For each $j$, step 1 gives the distinguished triangle $R_j(K)\to R_j(L)\to R_j(M)\to R_j(K)[1]$.
Its outside vertices are bounded constructible and have the common Tor interval of step 4. Apply
the explicit extension clause of the finite-stage triangulated lemma, with the same $\ell,E,Y$ and
$n=j\geq1$, in $D(Y_{\mathrm{proet}},A_{E,j})$: $R_j(L)$ has Tor amplitude in $[a,b]$. Since
neither endpoint of this interval depends on $j$, this proves $P(L)$. Uses:
lem-weil-integral-constructible-triangulated, lem-weil-finite-ctf-triangulated.
6. Take the full subcategory on the objects satisfying $P$. Step 2 supplies isomorphism closure
and zero; step 3 supplies closure under every integer shift (in both directions); steps 4-5 supply
extension closure in distinguished triangles. These are precisely the conditions in the definition
of a full triangulated subcategory, so this subcategory has the asserted triangulation inherited
from the ambient derived category. Uses: def-weil-triangulated-subcategory.
-/
theorem integral_ctf_isTriangulated
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u})
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ObjectProperty.IsClosedUnderIsomorphisms.{u + 2, u + 2} (integralCtfProperty D l hl E Y) ∧
    @ObjectProperty.IsTriangulated.{u + 2, u + 2}
      (completedIntegralDerivedCategory l E Y D hl)
      inferInstance inferInstance inferInstance inferInstance
      (fun (n : ℤ) ↦ inferInstance) inferInstance
      (integralCtfProperty D l hl E Y) :=
  open CategoryTheory.Limits in
  by
    let C := completedIntegralDerivedCategory l E Y D hl
    let P := boundedConstructibleDerivedCompleteIntegral D l hl E Y
    let R := integralDerivedReduction l E Y D hl
    let Q : ObjectProperty C := fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((R n).obj K) a b
    obtain ⟨hPi, hPt⟩ := boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y
    have : P.IsClosedUnderIsomorphisms := hPi
    have : P.IsTriangulated := hPt
    -- Reuse the proved K-flat tensor comparison from the finite-stage argument.
    have hzero (A : Type u) [CommRing A] (K : proEtaleDerivedCategory Y A)
        (hK : IsZero K) : HasProEtaleTorAmplitude Y A K 0 0 := by
      refine ⟨le_rfl, ?_⟩
      intro L N hL f hf hN M i _hi
      obtain ⟨F, c, htri, hcomp⟩ := tensor_functor Y A M
      obtain ⟨e⟩ := hL
      obtain ⟨q⟩ := hcomp L N f hf hN
      have hz := F.map_isZero (hK.of_iso e)
      exact ((DerivedCategory.homologyFunctor (torModules Y A) i).map_isZero hz).of_iso
        ((DerivedCategory.homologyFunctor (torModules Y A) i).mapIso q.symm)
    have : Q.IsClosedUnderIsomorphisms := ⟨by
      intro K L e hK
      obtain ⟨a, b, hab, hK⟩ := hK
      exact ⟨a, b, hab, fun n ↦ amplitude_iso Y _ ((R n).mapIso e) a b (hK n)⟩⟩
    have : Q.ContainsZero := by
      obtain ⟨Z, hZ, _⟩ := P.exists_prop_of_containsZero
      refine ⟨Z, hZ, 0, 0, le_rfl, ?_⟩
      intro n
      obtain ⟨c, htri⟩ := integralDerivedReduction_exact l E Y D hl n
      exact hzero _ _ ((R n).map_isZero hZ)
    have : Q.IsStableUnderShift ℤ := ⟨fun m ↦ ⟨by
      intro K hK
      obtain ⟨a, b, hab, hK⟩ := hK
      refine ⟨a - m, b - m, by omega, ?_⟩
      intro n
      obtain ⟨c, htri⟩ := integralDerivedReduction_exact l E Y D hl n
      exact amplitude_iso Y _ (((R n).commShiftIso m).app K).symm _ _
        ((finite_ctf_isTriangulated l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y).2.2.1
          ((R n).obj K) a b m (hK n))⟩⟩
    have : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
      intro T hT h₁ h₃
      obtain ⟨a, b, hab, h₁⟩ := h₁
      obtain ⟨c, e, _hce, h₃⟩ := h₃
      refine ⟨min a c, max b e, ?_, ?_⟩
      · exact (min_le_left _ _).trans (hab.trans (le_max_left _ _))
      · intro n
        obtain ⟨s, htri⟩ := integralDerivedReduction_exact l E Y D hl n
        exact (finite_ctf_isTriangulated l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y).2.2.2
          ((R n).mapTriangle.obj T) _ _ ((R n).map_distinguished T hT)
          (amplitude_mono Y _ (h₁ n) (min_le_left _ _) (le_max_left _ _))
          (amplitude_mono Y _ (h₃ n) (min_le_right _ _) (le_max_right _ _)))
    have : Q.IsTriangulated := { }
    exact ⟨inferInstanceAs (P ⊓ Q).IsClosedUnderIsomorphisms,
      inferInstanceAs (P ⊓ Q).IsTriangulated⟩

end WeilConjectures
