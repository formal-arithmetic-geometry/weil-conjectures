/-
Copyright (c) 2026 NI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NI
-/
module

public import Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Finiteness.Descent
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Composition of multiplicative isogenies

Source: Milne, Algebraic Groups (2017), Definition 18.1 and Proposition 18.2, printed p.387;
Corollaries 12.22, 12.37--12.38 and 12.41, with the Chapter 12 erratum
(blueprint: lem-sfb-multiplicative-isogeny-composition).
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The composite of multiplicative isogenies of smooth connected affine algebraic groups
is a multiplicative isogeny, and its kernel is central on every test scheme.

Source: Milne, Algebraic Groups (2017), Proposition 18.2, printed p.387, Corollary 12.22,
printed p.239, and Corollary 12.41, printed p.244, with its central-subgroup erratum
(blueprint: lem-sfb-multiplicative-isogeny-composition).

Proof plan:
1. Put N = ker f, Q = ker g and K = ker (f ≫ g). The kernel-subgroup result
   (lem-sc-kernel-subgroup) gives their group structures and closed inclusions. On every
   algebra, K consists of x with f(x) in Q, and the induced q : K → Q has kernel N.
   Conjugation by H0 preserves both K and N; the kernels are affine and of finite type.
2. The affine fibre-product formula (lem-weil-pbc-fibre-product-affine-spectra) gives
   F[K] = F[Q] ⊗_{F[H1]} F[H0]. Faithfully flat base change
   (lem-weil-pbc-faithfully-flat-base-change) makes q faithfully flat.
3. Apply lem-sfb-connected-action-multiplicative-type-rigidity to conjugation by H0 on N.
   Since H0 is smooth connected and N is multiplicative, N is central in H0 and hence in K.
   This includes nonreduced N such as μ_p.
4. Apply lem-sfb-multiplicative-extension-action-rigidity to the H0-action on K and the
   quotient q : K → Q. Its required centrality of N in K is Step 3. Thus K is central in H0.
5. In particular K is commutative. Apply lem-sfb-commutative-multiplicative-type-extension
   to q to obtain multiplicative type of K.
6. The torsor identity N × K ≅ K ×_Q K sends (n,x) to (nx,x), with inverse
   (y,x) ↦ (yx⁻¹,x). On coordinate algebras it identifies D ⊗_B D with D ⊗_F P,
   where B = F[Q], D = F[K], P = F[N]. A finite F-basis of P gives finite generation over D.
   Faithfully flat finite-module descent (lem-weil-pbc-faithfully-flat-descent-finite-module)
   makes D finite over B. Since B is finite over F, D is finite over F.
7. Tensor associativity identifies extension of scalars along the composite with the
   composite of the two extension functors. Exactness and detection of zero modules pass
   to that composite, proving faithful flatness. These are all asserted clauses. -/
theorem multiplicativeIsogeny_comp {F : Type u} [Field F] [IsAlgClosed F]
    (H0 H1 H2 : Over (Spec (.of F))) [GrpObj H0] [GrpObj H1] [GrpObj H2]
    [IsAffine H0.left] [IsAffine H1.left] [IsAffine H2.left]
    [Smooth H0.hom] [Smooth H1.hom] [Smooth H2.hom]
    [ConnectedSpace H0.left] [ConnectedSpace H1.left] [ConnectedSpace H2.left]
    [LocallyOfFiniteType H0.hom] [LocallyOfFiniteType H1.hom]
    [LocallyOfFiniteType H2.hom] [QuasiCompact H0.hom] [QuasiCompact H1.hom]
    [QuasiCompact H2.hom]
    (f : H0 ⟶ H1) (g : H1 ⟶ H2) [IsMonHom f] [IsMonHom g]
    (hf : f.left.appTop.hom.FaithfullyFlat) (hg : g.left.appTop.hom.FaithfullyFlat)
    [IsFinite (GrpObj.ker f).hom] [IsFinite (GrpObj.ker g).hom]
    (hN : IsFiniteDiagonalizableGroupScheme (GrpObj.ker f))
    (hQ : IsFiniteDiagonalizableGroupScheme (GrpObj.ker g)) :
    (f ≫ g).left.appTop.hom.FaithfullyFlat ∧
      IsFinite (GrpObj.ker (f ≫ g)).hom ∧
      IsFiniteDiagonalizableGroupScheme (GrpObj.ker (f ≫ g)) ∧
      ∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker (f ≫ g)) (h : T ⟶ H0),
        (x ≫ GrpObj.kerι (f ≫ g)) * h = h * (x ≫ GrpObj.kerι (f ≫ g)) := by
  sorry

end AlgebraicGeometry
