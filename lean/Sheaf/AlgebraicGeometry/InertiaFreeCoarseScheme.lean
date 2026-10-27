/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.DMGeometricInertiaTrivial
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # An inertia-free DM stack equals its coarse scheme

Source: Stacks Project, Tag 04SZ, proposition-algebraic-stack-no-automorphisms;
Tag 05B5 and Morphisms of Stacks, Tag 06FM and the finite-type sections
(blueprint: lem-sfb-inertia-free-coarse-scheme).

The coarse morphism itself is an equivalence. Automorphisms are tested on all
schemes, including nonreduced schemes. The final conditional conclusion retains
both local finite type and quasi-compactness over an arbitrary scheme base.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- An inertia-free Deligne--Mumford stack is represented by its specified coarse
scheme, and smoothness and finite type pass to that scheme.
Source: Stacks Project, Tag 04SZ, proposition-algebraic-stack-no-automorphisms;
Tag 05B5; stacks-morphisms.tex, Tag 06FM and section-finite-type.
(blueprint: lem-sfb-inertia-free-coarse-scheme).

Proof:
1. Apply lem-sfb-dm-geometric-inertia-trivial to obtain an algebraic space E/S
   and an equivalence e : F ≃ h_E over Sch/S. Its hypotheses are exactly hF and
   hgeom, with no reducedness restriction on arbitrary test schemes.
2. By the coarse universal property of def-sfb-stable-pointed-moduli-groupoids,
   there is a map a : C → E with a c isomorphic to e. Choose an inverse d to e
   and put b = c d : E → C. These are actual algebraic-space maps by
   def-trf-algebraic-space. The equality a b = id follows from e d ≅ id and
   discreteness of h_E. Also (b a)c ≅ b e ≅ c. Coarse uniqueness with target
   the scheme space of def-trf-scheme-algebraic-space gives b a = id. Hence b
   is an isomorphism and c ≅ b e is an equivalence over Sch/S.
3. In every fibre, full faithfulness and essential surjectivity identify F(T)
   with the discrete groupoid h_C(T). This gives IsRepresentedByScheme and
   makes every endomorphism in the groupoid equal to the identity, including
   for nonreduced T (def-sfb-stable-pointed-moduli-groupoids).
4. If F is smooth, choose a smooth surjective atlas V → F with V → S smooth.
   Through c it becomes a smooth surjective scheme map q : V → C: the
   2-fibre products are the ordinary scheme fibre products under c. By
   lem-sfb-stack-chartwise-smooth-etale-calculus, q is flat and locally of
   finite presentation. Apply lem-sbc-smooth-flat-surjective-source-descent
   to q and C → S, whose composite is V → S. Thus C → S is smooth.
5. Apply lem-sfb-stack-finite-type-calculus to the represented structural map.
   Its scheme base changes under c are precisely those of C → S. The
   chartwise local-finite-type condition gives LocallyOfFiniteType C.hom;
   quasi-compactness is retained in the affine scheme tests, giving
   QuasiCompact C.hom. Their conjunction is finite type as in
   def-weil-finite-type-morphism. -/
theorem inertia_free_coarse_scheme {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsDeligneMumfordModuliStack F)
    (C : Over S) (c : BasedFunctor F (discreteModuli (yoneda.obj C)))
    (hc : IsCoarseModuliScheme F C c)
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ S)
      (x : Functor.Fiber F.p (Over.mk a)) (α : x ⟶ x), α = 𝟙 x) :
    c.toFunctor.IsEquivalence ∧ IsRepresentedByScheme F C ∧
      (∀ (T : Over S) (x : Functor.Fiber F.p T) (α : x ⟶ x), α = 𝟙 x) ∧
      (IsSmoothModuliStack F →
        IsLocallyFiniteTypeModuliMap (moduliBaseStructure F) →
        IsQuasiCompactModuliMap (moduliBaseStructure F) →
        Smooth C.hom ∧ LocallyOfFiniteType C.hom ∧ QuasiCompact C.hom) := by
  sorry

end AlgebraicGeometry
