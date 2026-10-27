module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Sheaf.AlgebraicGeometry.StandardGroupSchemes

/-! # Commutative extensions of groups of multiplicative type

Source: Milne, Algebraic Groups (2017), Corollary 12.22, printed p.239
(blueprint: lem-sfb-commutative-multiplicative-type-extension).

Over the algebraically closed base, multiplicative type is expressed by an isomorphism
of group schemes to the recorded group-algebra spectrum D_F(M), with M finitely generated.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A commutative extension of groups of multiplicative type is of multiplicative type.
The quotient is specified by faithful flatness of its actual coordinate-ring map, and
its kernel is the scheme-theoretic fibre over the identity. In particular, infinitesimal
kernels and disconnected groups are allowed.

Source: Milne, Algebraic Groups (2017), Corollary 12.22, printed p.239
(blueprint: lem-sfb-commutative-multiplicative-type-extension).

Proof plan:
1. Apply lem-sfb-multiplicative-additive-vanishing-criterion to N = ker q and Q.
   Their given diagonalizable presentations imply that every homomorphism from either
   group to the additive group is zero. These are scheme morphisms, so the assertion
   includes points over nonreduced test algebras.
2. Given u : E → G_a, its restriction to N is zero by step 1. Apply
   lem-sfb-faithfully-flat-group-quotient-universal to q, u and the additive group of
   def-sc-gm-ga. Faithful flatness of q's coordinate map gives a unique v : Q → G_a
   with u = v ∘ q. By step 1, v is zero, hence u is zero.
3. The affine finite-type group E is commutative by hypothesis. Step 2 supplies the
   remaining hypothesis of lem-sfb-multiplicative-additive-vanishing-criterion, whose
   converse yields E ≅ D_F(M) for a finitely generated abelian group M. Neither input
   requires smoothness or connectedness. -/
theorem commutative_multiplicativeType_extension
    {F : Type u} [Field F] [IsAlgClosed F]
    (E Q : Over (Spec (.of F))) [GrpObj E] [GrpObj Q]
    [IsAffine E.left] [IsAffine Q.left]
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (q : E ⟶ Q) [IsMonHom q]
    (hq : q.left.appTop.hom.FaithfullyFlat)
    (hN : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk (GrpObj.ker q) ≅ diagonalizableGroup F M))
    (hQ : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk Q ≅ diagonalizableGroup F M))
    [IsCommMonObj E] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk E ≅ diagonalizableGroup F M) := by
  sorry

end AlgebraicGeometry
