/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingSmoothAscent

/-! # Finite étale lifting of formal monoid coefficients

Source: Stacks Project, Tags 09ZL/04GK, 07NF, 031B and 00MA; the explicit
finite-basis formal-monoid calculation used with ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift).

The coefficient map is constructed on every ideal-power quotient and then on
compatible families. No unspecified map or chosen formal series object is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AdicCompletion

/-- The completion map induced by a ring map, with the extended defining ideal.
At level `n` it is the quotient map induced by the original ring map.
Source: the defining inverse limits, Stacks Tag 0317, and the finite-basis
calculation in ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
noncomputable def mapRingHomAlong {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    (a : Ideal R) (φ : R →+* T) :
    AdicCompletion a R →+* AdicCompletion (Ideal.map φ a) T := by
  let b := Ideal.map φ a
  let hpow (n : ℕ) : a ^ n ≤ (b ^ n).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  let g (n : ℕ) : AdicCompletion a R →+* T ⧸ b ^ n :=
    (Ideal.quotientMap (b ^ n) φ (hpow n)).comp (evalₐ a n).toRingHom
  have hg {i j : ℕ} (hij : i ≤ j) :
      (Ideal.Quotient.factorPow b hij).comp (g j) = g i := by
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ a j x)
    have hi : evalₐ a i x = Ideal.Quotient.mk (a ^ i) r := by
      have hv : x.val j = Submodule.Quotient.mk r := by
        have h := factor_evalₐ_eq_eval a (n := j) x (by simp)
        rw [← hr] at h
        exact h.symm
      have hvi := x.property hij
      rw [hv] at hvi
      have h := factor_eval_eq_evalₐ a (n := i) x (by simp)
      rw [show eval a R i x = Submodule.Quotient.mk r from hvi.symm] at h
      exact h.symm
    simp [g, ← hr, hi]
  exact liftRingHom b g (fun hij ↦ hg hij)

end AdicCompletion

namespace AddMonoidAlgebra

/-- Coefficient extension on completed monoid rings, induced by `E → D` on each
coefficient and fixing every monomial. The target uses the extended defining ideal;
when `m_D = m_E D` this is precisely `(m_D, [s] : s ≠ 0)`.
Source: finite-basis calculation in ILO VI 2.3 and Stacks Tag 00MA
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
noncomputable def formalCoefficientMap (E : Type u) [CommRing E]
    (S : Type v) [AddCommMonoid S] (a : Ideal (AddMonoidAlgebra E S))
    (D : Type w) [CommRing D] [Algebra E D] :
    AdicCompletion a (AddMonoidAlgebra E S) →+*
      AdicCompletion (Ideal.map (mapRingHom S (algebraMap E D)) a)
        (AddMonoidAlgebra D S) :=
  AdicCompletion.mapRingHomAlong a (mapRingHom S (algebraMap E D))

/-- The coefficient-extended hypersurface `D[[S]]/(f)`, where the equation is
sent by the constructed coefficient map.
Source: ILO VI 2.3, finite-basis quotient calculation
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
abbrev CoefficientHypersurface (E : Type u) [CommRing E]
    (S : Type v) [AddCommMonoid S] (a : Ideal (AddMonoidAlgebra E S))
    (f : AdicCompletion a (AddMonoidAlgebra E S))
    (D : Type w) [CommRing D] [Algebra E D] :=
  AdicCompletion (Ideal.map (mapRingHom S (algebraMap E D)) a)
    (AddMonoidAlgebra D S) ⧸ Ideal.span {formalCoefficientMap E S a D f}

/-- Quotient adic topology on `D[[S]]/(f)`. The completed ring has the topology
of the extended ideal; under the conclusion's maximal-ideal equality, this is its
maximal-ideal topology, and the quotient has the induced quotient adic topology.
Source: Stacks Tag 05GG and ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
noncomputable abbrev coefficientHypersurfaceTopology (E : Type u) [CommRing E]
    (S : Type v) [AddCommMonoid S] (a : Ideal (AddMonoidAlgebra E S))
    (f : AdicCompletion a (AddMonoidAlgebra E S))
    (D : Type w) [CommRing D] [Algebra E D] :
    TopologicalSpace (CoefficientHypersurface E S a f D) :=
  TopologicalSpace.coinduced
    (Ideal.Quotient.mk (Ideal.span {formalCoefficientMap E S a D f}))
    (Ideal.map (algebraMap (AddMonoidAlgebra D S) _)
      (Ideal.map (mapRingHom S (algebraMap E D)) a)).adicTopology

/-- Finite étale local factors lift by extension of the complete regular local
coefficient ring. The equality `ha` fixes the formal monoid completion ideal;
`hf` is membership in its extension, the maximal ideal of the completed ring.
The equation on all `h` expresses exactly `A₀`-algebra compatibility.
Source: Stacks Tags 09ZL/04GK, 07NF, 031B, 00MA and ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift).

Proof plan:
1. Put $k=E/\mathfrak n$, $R=E[S]$ and $\mathfrak b=(\mathfrak n,[s]:s\ne0)\subset R$. Sharpness
implies that a sum of nonzero monoid elements cannot be zero, so sending every nonzero monomial to
zero defines the augmentation $R\to E$. Thus $R/\mathfrak b=k$. Choose finitely many nonzero
generators of $S$; their monomials, together with generators of $\mathfrak n$, generate $\mathfrak
b$. Also $R$ is a quotient of a polynomial ring in finitely many variables over $E$, hence is
Noetherian by finite-type permanence. Its completion $H$ is Noetherian by completion permanence.
The completion-mod-ideal theorem gives that $H$ is complete for $\mathfrak bH$ and that
$H/\mathfrak bH=k$. Dependencies: lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-adic-completion-mod-ideal.

2. Every $z\in\mathfrak bH$ is topologically nilpotent, so the compatible partial sums
$1+z+\cdots+z^{q-1}$ define an inverse of $1-z$ in the complete ring $H$. If $h$ has nonzero image
in the field $H/\mathfrak bH=k$, choose $v$ with $hv\equiv1\pmod{\mathfrak bH}$; the preceding
inverse makes $h$ a unit. Therefore $H$ is nonzero local with maximal ideal $\mathfrak bH$ and
residue field $k$. Since $f$ is in this maximal ideal, $(f)$ is proper. The complete-local
quotient theorem makes $A_0=H/(f)$ a nonzero complete Noetherian local ring with maximal ideal
$\mathfrak m_0=\mathfrak bH/(f)$ and residue field $k$. Completeness makes both $(E,\mathfrak n)$
and $(A_0,\mathfrak m_0)$ henselian pairs, hence henselian local rings. Dependencies:
lem-weil-pbc-complete-local-quotient, lem-weil-pbc-complete-pair-henselian.

3. Let $\mathfrak q$ be the maximal ideal of $K$. Since $K$ is finite over $A_0$, the
finite-algebra integrality theorem and contraction of maximal ideals under integral maps give
$\mathfrak q\cap A_0=\mathfrak m_0$. Apply the etale prime-ideal theorem at $\mathfrak q$. As
localization of a local ring at its maximal ideal is the ring itself, it yields $\mathfrak
q=\mathfrak m_0K$. The etale residue-field theorem gives that $L=K/\mathfrak q=\kappa(K)$ is
finite separable over $k$. Thus $L$ is a nonzero finite etale $k$-algebra by the
finite-separable-extension theorem. Dependencies: lem-weil-pbc-finite-algebra-is-integral,
lem-weil-pbc-integral-maximal-contracts-maximal, lem-weil-pbc-etale-prime-generates-maximal,
lem-weil-pbc-etale-algebra-residue-field-separable, lem-weil-pbc-finite-separable-extension-etale.

4. Apply essential surjectivity of the henselian finite-etale equivalence to $E$ and the finite
etale $k$-algebra $L$. It supplies a finite etale $E$-algebra $D$ with a fixed $k$-algebra
isomorphism $D/\mathfrak nD\cong L$. This makes $D$ nonzero. The finite-algebra integrality
theorem shows that every maximal ideal of $D$ contracts to the unique maximal ideal $\mathfrak n$
of $E$. Consequently every maximal ideal of $D$ contains $\mathfrak nD$; since the quotient is a
field, $\mathfrak nD$ is the unique maximal ideal. Thus $D$ is local and $\mathfrak m_D=\mathfrak
nD$, with residue field identified with $L$. A finite module algebra is finite type: a finite set
of module generators also generates the algebra. Finite-type permanence makes $D$ Noetherian. The
finite-module completeness theorem over the complete Noetherian ring $E$ makes $D$ complete for
$\mathfrak nD=\mathfrak m_D$. Dependencies: lem-weil-pbc-henselian-finite-etale-equivalence,
lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-integral-maximal-contracts-maximal,
lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-finite-module-complete-over-complete-noetherian.

5. The regular-local localization theorem makes $E$ a regular ring. The affine etale comparison
identifies $E\to D$ with a finitely presented ring map having $H_1(L_{D/E})=0$ and
$\Omega_{D/E}=0$. The zero module is finite projective (a direct summand of the rank-zero free
module), so the definition of a smooth ring map makes $E\to D$ smooth. Regularity ascends along
smooth ring maps. Therefore $D$ is regular, and its localization at its unique maximal ideal,
which is $D$ itself, is a regular local ring. Dependencies:
lem-weil-pbc-regular-local-localization, lem-weil-pbc-etale-ring-map-iff-etale-affine,
def-weil-pbc-smooth-ring-map, lem-weil-pbc-regular-ring-smooth-ascent.

6. The etale-flatness theorem makes $D$ flat over $E$. Since it is finite and $E$ is local, the
finite-flat-local theorem makes $D$ free over $E$. Its basis can be taken finite: the union of the
finite supports of any finite generating set contains every basis vector. Fix such a basis
$d_1,\ldots,d_r$; $r>0$ because $D\ne0$. Dependencies: lem-weil-pbc-etale-algebra-flat,
lem-weil-pbc-finite-flat-local-free.

7. Put $R_D=D[S]$ and $\mathfrak b_D=(\mathfrak m_D,[s]:s\ne0)$. Since $\mathfrak m_D=\mathfrak
nD$, one has $\mathfrak b_D=\mathfrak bR_D$. The chosen basis gives $R_D=\bigoplus_{i=1}^r d_iR$
and, for every $q\ge1$, $\mathfrak b_D^q=\bigoplus_{i=1}^r d_i\mathfrak b^q$: expand elements in
the basis and multiply by the generators of the extended ideal. Hence $R_D/\mathfrak
b_D^q=\bigoplus_i d_i(R/\mathfrak b^q)$. A compatible sequence in this finite direct sum is
exactly $r$ compatible coordinate sequences. Taking the defining inverse limits therefore
identifies $D[[S]]$ with $\bigoplus_i d_iH$. The resulting map $\Phi:D\otimes_E H\to D[[S]]$ sends
$d\otimes h$ to the product of the constant coefficient $d$ and the image of $h$. It is bijective
by the displayed basis calculation and multiplicative because it is induced by the commuting
coefficient and monoid maps at every quotient level. Thus $\Phi$ is a ring isomorphism. In
particular the image of $h\in H$ is its coefficientwise image. This calculation also works when
$S=\{0\}$. Dependencies: def-weil-pbc-adic-completion.

8. Under $\Phi$, multiplication by the coefficientwise image of $f$ acts as multiplication by $f$
in each of the $r$ coordinates $H$. Thus quotienting gives an $A_0$-algebra isomorphism
$C:=D\otimes_E A_0\cong D[[S]]/(f)$: both modules are $\bigoplus_i d_i(H/(f))$, and their ring
operations are induced by the same coefficient products in $D$ and multiplication in $H$.
Explicitly the map is $d\otimes\bar h\mapsto\overline{\Phi(d\otimes h)}$, independent of the
chosen lift $h$ since two lifts differ by a multiple of $f$. The inverse is given coordinatewise
in the basis. Dependencies: .

9. The base-change theorem makes $C=D\otimes_E A_0$ etale over $A_0$, and its displayed
$r$-element basis makes it finite. Reducing this basis presentation modulo $\mathfrak m_0$, or
just sending $d\otimes a$ to $\bar a\,\bar d$, gives $C/\mathfrak m_0C\cong D\otimes_E
k=D/\mathfrak nD\cong L$. Step 3 identifies $K/\mathfrak m_0K$ with the same $L$, compatibly as
$k$-algebras. Full faithfulness of the henselian finite-etale equivalence for $A_0$ lifts this
residue-algebra isomorphism to an $A_0$-algebra isomorphism $C\cong K$: lift the map and its
inverse, and use faithfulness to see that their composites are identities. Composing its inverse
with Step 8 gives the required $K\cong D[[S]]/(f)$. Dependencies:
lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-henselian-finite-etale-equivalence.

10. The topology on $D[[S]]$ is its $\mathfrak b_DD[[S]]$-adic topology by completion-mod-ideal,
since $\mathfrak m_D$ and $S$ are finitely generated and hence so is $\mathfrak b_D$. Its quotient
by that ideal is $D/\mathfrak m_D=L$; the geometric-series argument of Step 2 shows that this
ideal is the unique maximal ideal. The image of $f$ belongs to it. Thus on $D[[S]]/(f)$ the
quotient adic topology is the maximal-ideal topology, because its defining ideal is the image of
$\mathfrak b_DD[[S]]$. The algebra isomorphism from Step 9 identifies maximal ideals and all their
powers. It and its inverse are therefore continuous for the maximal-ideal topologies, including
the finite-algebra topology on $K$, whose defining ideal is $\mathfrak m_0K=\mathfrak q$.
Dependencies: lem-weil-pbc-adic-completion-mod-ideal.

11. Finally $E\to D$ is a local flat homomorphism: it is flat by Step 6 and $\mathfrak
m_D=\mathfrak nD$ by Step 4. The flat-local theorem makes it faithfully flat. Apply faithful-flat
ideal contraction to $\mathfrak n^2$. If $x\in\mathfrak n\setminus\mathfrak n^2$ had image in
$\mathfrak m_D^2=(\mathfrak nD)^2=\mathfrak n^2D$, contraction would give $x\in\mathfrak n^2$, a
contradiction. Its image is already in $\mathfrak m_D$, proving the final assertion. When
$\mathfrak n=0$ the assertion is vacuous. None of these arguments requires $f\ne0$. Dependencies:
lem-weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-ideal-contraction.
-/
theorem finiteEtale_formalMonoid_coefficientLift
    (E : Type u) [CommRing E] [IsRegularLocalRing E]
    [IsAdicComplete (IsLocalRing.maximalIdeal E) E]
    (S : Type v) [AddCommMonoid S]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative S))
    (hsharp : ∀ s : S, IsUnit (Multiplicative.ofAdd s) → s = 0)
    (a : Ideal (AddMonoidAlgebra E S))
    (ha : a = Ideal.map (algebraMap E (AddMonoidAlgebra E S))
        (IsLocalRing.maximalIdeal E) ⊔
      Ideal.span {b | ∃ s : S, s ≠ 0 ∧ b = single s (1 : E)})
    (f : AdicCompletion a (AddMonoidAlgebra E S))
    (hf : f ∈ Ideal.map (algebraMap (AddMonoidAlgebra E S) _) a)
    (K : Type w) [CommRing K] [IsLocalRing K]
    [Algebra (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K]
    [Module.Finite (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K]
    [Algebra.Etale (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K] :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : IsRegularLocalRing D) (_ : Algebra E D),
      Module.Finite E D ∧ Algebra.Etale E D ∧
      IsAdicComplete (IsLocalRing.maximalIdeal D) D ∧
      Nonempty (IsLocalRing.ResidueField D ≃+* IsLocalRing.ResidueField K) ∧
      IsLocalRing.maximalIdeal D = Ideal.map (algebraMap E D) (IsLocalRing.maximalIdeal E) ∧
      (∀ x : E, x ∈ IsLocalRing.maximalIdeal E →
        x ∉ (IsLocalRing.maximalIdeal E) ^ 2 →
        algebraMap E D x ∈ IsLocalRing.maximalIdeal D ∧
        algebraMap E D x ∉ (IsLocalRing.maximalIdeal D) ^ 2) ∧
      ∃ e : K ≃+* CoefficientHypersurface E S a f D,
        (∀ h : AdicCompletion a (AddMonoidAlgebra E S),
          e (algebraMap (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K
            (Ideal.Quotient.mk (Ideal.span {f}) h)) =
          Ideal.Quotient.mk (Ideal.span {formalCoefficientMap E S a D f})
            (formalCoefficientMap E S a D h)) ∧
        @Continuous K (CoefficientHypersurface E S a f D)
          (IsLocalRing.maximalIdeal K).adicTopology
          (coefficientHypersurfaceTopology E S a f D) e ∧
        @Continuous (CoefficientHypersurface E S a f D) K
          (coefficientHypersurfaceTopology E S a f D)
          (IsLocalRing.maximalIdeal K).adicTopology e.symm := by
  sorry

end AddMonoidAlgebra
