module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.FieldTheory.Perfect
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Central additive series over a perfect field

Source: Milne, Algebraic Groups (2017), Corollary 16.24, p.331, first assertion,
with Corollaries 16.22 and 16.23
(blueprint: lem-sfb-perfect-unipotent-additive-series).

Both the successive quotients and the ambient quotients are represented fppf
quotients. Their comparison maps record the inclusion of each additive quotient
in its ambient quotient. Centrality is tested on every scheme over the field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine unipotent group over a perfect field has a central
normal series with additive successive quotients, including the zero-length
series for the trivial group.

Source: Milne, Algebraic Groups (2017), Corollary 16.24, p.331, first assertion
(blueprint: lem-sfb-perfect-unipotent-additive-series).

Proof plan:
1. By def-sc-gm-ga, sbc-lem-affine-space-smooth and
   lem-sbc-smooth-fixed-dimension-over-field, G_a has dimension one. Affine groups
   are separated by lem-weil-pbc-affine-source-morphism-separated. Apply
   lem-sfb-homogeneous-quotient-krull-dimension with the trivial subgroup to obtain
   finite nonnegative dimension. Induct strongly on dimension. For V = 1 take m = 0.
2. For nontrivial V, lem-sfb-unipotent-central-additive-subgroup gives a smooth
   connected central N isomorphic to G_a. PerfectField gives the required
   p-th roots in positive characteristic. The identity section and
   lem-sbc-connected-rational-point-geometrically-connected make V geometrically
   connected. Apply lem-sfb-affine-normal-quotient-geometry to obtain the smooth,
   geometrically connected affine finite-type fppf quotient Q = V/N.
3. After algebraic closure, lem-sfb-unipotent-normal-quotient-image applied to the
   quotient map gives unipotence of Q. The matrix criterion and field-extension
   detection in lem-sfb-unipotent-to-multiplicative-trivial descend it to k.
   The kernel and fppf local lifts give the homogeneous-quotient hypotheses, so
   lem-sfb-homogeneous-quotient-krull-dimension gives dim V = 1 + dim Q. In
   dimension zero this is a contradiction; otherwise apply induction to Q.
4. Pull back its series Q_i along V → Q using the inverse-image and quotient
   clauses of lem-sfb-affine-normal-quotient-geometry. The terms are smooth,
   connected, closed and normal in V. The first is V and the last is N.
   Successive quotients and ambient quotients identify with those of Q. Append
   the trivial subgroup; the last successive quotient is N, hence G_a.
5. Transfer centrality on all sections through the quotient identifications.
   The final centrality condition is that of N in V. All identities hold after
   every base change. If Q = 1 its series has length zero and this construction
   gives V = N ⊇ 1. The trivial ambient group uses the initial zero-length case. -/
theorem perfect_unipotent_additive_series
    {k : Type u} [Field k] [PerfectField k]
    (U : Grp (Over (Spec (.of k))))
    (haff : IsAffine U.X.left)
    (hft : LocallyOfFiniteType U.X.hom) (hqc : QuasiCompact U.X.hom)
    (hsm : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left)
    (hunip : SolvableGroupStructure.IsUnipotent U) :
    ∃ (m : ℕ) (S : Fin (m + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (m + 1), S j ⟶ U),
      (∀ j : Fin (m + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsNormalSubgroupScheme (i j).hom.hom ∧
        Smooth (S j).X.hom ∧ ConnectedSpace (S j).X.left) ∧
      IsIso (i 0) ∧ Nonempty (S (Fin.last m) ≅ Grp.trivial _) ∧
      (Nonempty (U ≅ Grp.trivial _) → m = 0) ∧
      ∀ j : Fin m, ∃ (a : S j.succ ⟶ S j.castSucc)
        (q : S j.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k))
        (Q : Grp (Over (Spec (.of k)))) (p : U ⟶ Q)
        (b : Grp.mk (StandardGroupSchemes.additive k) ⟶ Q),
        a ≫ i j.castSucc = i j.succ ∧
        IsFppfGroupQuotient a q ∧ IsFppfGroupQuotient (i j.succ) p ∧
        q ≫ b = i j.castSucc ≫ p ∧
        ∀ (T : Over (Spec (.of k)))
          (x : T ⟶ StandardGroupSchemes.additive k) (y : T ⟶ Q.X),
          (x ≫ b.hom.hom) * y = y * (x ≫ b.hom.hom) := by
  sorry

end AlgebraicGeometry
