module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.AlgebraicGeometry.Group.Smooth
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # The derived subgroup of a smooth connected affine group

Source: Milne, Algebraic Groups (2017), Propositions 6.18 and 6.20(b),
Corollary 6.19(b),(d),(e), printed pp.129--130
(blueprint: lem-sfb-smooth-connected-derived-subgroup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine group of finite type over an algebraically closed field has a
smallest closed subgroup containing its commutator morphism. It is normal, smooth, connected,
affine and of finite type; its rational points are the abstract commutator subgroup, and every
homomorphism to a commutative affine group is trivial on it.
Source: Milne, Propositions 6.18 and 6.20(b), Corollary 6.19(b),(d),(e), pp.129--130
(blueprint: lem-sfb-smooth-connected-derived-subgroup).

Proof:
1. Apply `lem-sfb-pointed-word-kernel-stabilization` to the commutator map with r = 2.
   Its inverse is obtained by exchanging the two inputs. The word kernels stabilize at a
   prime ideal I_N, and every positive power of H is geometrically integral.
2. Apply `lem-sfb-affine-pointed-map-generated-subgroup` to obtain the smallest closed
   subgroup D = Spec(F[H]/I_N). It is affine of finite type, geometrically reduced and
   geometrically connected. By `lem-sfb-geometrically-reduced-group-smooth` it is smooth.
   The induced word map H^(2N) to D is dense with injective coordinate pullback.
3. By `lem-wf-affine-constructible-open`, the word image contains a nonempty open U of D.
   By `lem-wf-affine-nullstellensatz-vanishing`(1), every F-point of U lifts to H^(2N),
   and every nonempty open of D has an F-point, using a nonempty principal affine open.
4. The abstract commutator subgroup K is contained in D(F). For d in D(F), irreducibility
   makes U intersect dU. Choose u = dv in this intersection with u,v in U(F). Both are
   products of commutators, so d = uv⁻¹ belongs to K. Hence D(F) = K, which is invariant
   under conjugation by H(F).
5. The conjugation map H × D to H takes F-points into D(F). Its source is reduced by
   `lem-wf-affine-product-reduced`. The vanishing principle
   `lem-wf-affine-nullstellensatz-vanishing`(3) factors it through D. On all F-algebras
   this gives normality in the sense of `def-sc-group-scheme-subgroup`.
6. A homomorphism to a commutative affine group kills every commutator word. Injectivity
   of the stabilized word pullback forces its restriction to D to equal the identity-valued
   map: apply it to the difference of the two pullbacks of each coordinate function.
   Affine maps are determined by their coordinate maps (`def-weil-affine-spectrum`).
   No finite-type or reducedness hypothesis on the commutative target is needed. -/
theorem exists_smooth_connected_derived_subgroup {F : Type u} [Field F] [IsAlgClosed F]
    (H : Grp (Over (Spec (.of F)))) [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] :
    ∃ (D : Grp (Over (Spec (.of F)))) (i : D ⟶ H),
      IsDerivedGroupScheme i.hom.hom ∧
      IsNormalSubgroupScheme i.hom.hom ∧ Smooth D.X.hom ∧ ConnectedSpace D.X.left ∧
      IsAffine D.X.left ∧ LocallyOfFiniteType D.X.hom ∧ QuasiCompact D.X.hom ∧
      (IsMonHom.monoidHom i.hom.hom (𝟙_ (Over (Spec (.of F))))).range =
        commutator (𝟙_ (Over (Spec (.of F))) ⟶ H.X) ∧
      (∀ (C : Grp (Over (Spec (.of F)))) [IsCommMonObj C.X] [IsAffine C.X.left]
        (f : H ⟶ C), i.hom.hom ≫ f.hom.hom = 1) := by
  sorry

end AlgebraicGeometry
