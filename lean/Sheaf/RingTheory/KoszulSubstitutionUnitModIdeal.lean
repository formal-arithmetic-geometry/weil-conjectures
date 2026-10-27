module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.AlgebraicGeometry.KoszulDifferential
import WeilConjectures.RingTheory.KoszulGeneratorHomotopy
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Koszul substitution with determinant invertible modulo the common ideal

Source: Stacks Project, More on Algebra, Tag 066A, proof, second paragraph;
Tag 0624 for functoriality and Tag 05RU for the derived category.
(blueprint: lem-sfb-koszul-substitution-unit-mod-ideal).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace ExteriorAlgebra

/-- Exterior powers of the specified substitution form a quasi-isomorphism of Koszul
complexes when its determinant is invertible modulo the common generated ideal.
Every component of `T` is prescribed, so the derived isomorphism is the image of
this very substitution, rather than an unspecified isomorphism of derived objects.
Source: Stacks Project, Tags 066A (proof, second paragraph), 0624, 0663 and 05RU.
(blueprint: lem-sfb-koszul-substitution-unit-mod-ideal).

Proof:
1. The exterior-algebra map of `t` descends from the tensor algebra, since it sends
   a square tensor to a square tensor. Its degree-q restriction is exteriorPower.map q t.
   The contraction formula of lem-weil-pbc-koszul-differential and `ht` show that these
   restrictions commute with differentials: the coefficient on each omitted wedge
   is alpha(t(v)) = beta(v). They therefore give T : K(b) -> K(a), with identity in
   degree zero.
2. By lem-k3-koszul-generator-homotopy, multiplication by each generator is dh+hd,
   with h given by wedging with its basis vector. Thus every generator kills homology;
   by linearity the common ideal I kills the homology of both complexes.
3. Invert the determinant delta. By lem-weil-pbc-exterior-power-free-basis, localizing
   a standard wedge gives the corresponding standard wedge over A[1/delta], and the
   contraction differentials agree. The adjugate identity gives an inverse matrix
   delta^(-1) adj(t). Its exterior powers invert every component of the localized T,
   including degree zero and the vanishing terms above r.
4. Apply lem-sc-p1-localization-short-exact to the cycles, boundaries and homology
   short exact sequences. It identifies localized homology with the homology of the
   localized complex, naturally in T: both maps send [z]/delta^n to [T(z)/delta^n].
   Therefore the localized homology maps of T are bijective.
5. Lift the inverse of delta modulo I to c in A. Since c*delta-1 lies in I and I
   annihilates either homology module N, c*delta acts as identity on N. The localization
   map N -> N[1/delta] has inverse x/delta^n -> c^n*x. To check independence of a
   fraction representative, multiply delta^k*(delta^m*x-delta^n*y)=0 by c^(k+n+m).
   This gives c^n*x=c^m*y. These inverses commute with the homology maps of T, so
   the original homology maps are bijective as well. This proves QuasiIso T.
6. Extension by embeddingDownNat places degree q in degree -q and adds zero terms
   in positive cochain degrees. The same homology maps are isomorphisms. The derived
   localization Q inverts this extended T. Conversely its cohomology functors recover
   the homology maps, so invertibility of this Q(T) is equivalent to quasi-isomorphy.
   Empty tuples, the zero ring and the unit ideal require no additional hypothesis. -/
theorem koszul_substitution_unit_mod_ideal
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (r : ℕ) (a b : Fin r → A) (I : Ideal A)
    (ha : Ideal.span (Set.range a) = I) (hb : Ideal.span (Set.range b) = I)
    (t : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (ht : (Finsupp.linearCombination A a).comp t = Finsupp.linearCombination A b)
    (hδ : IsUnit (Ideal.Quotient.mk I
      (Matrix.det (fun i j : Fin r ↦ t (Finsupp.single j 1) i)))) :
    ∃ T : koszulComplex A r b ⟶ koszulComplex A r a,
      (∀ q : ℕ, (T.f q).hom = exteriorPower.map q t) ∧
      QuasiIso T ∧
      IsIso (DerivedCategory.Q.map
        (HomologicalComplex.extendMap T ComplexShape.embeddingDownNat)) := by
  sorry

end ExteriorAlgebra
