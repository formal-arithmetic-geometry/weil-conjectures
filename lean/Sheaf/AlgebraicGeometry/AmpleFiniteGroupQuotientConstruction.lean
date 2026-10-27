/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Constructing a finite quotient from absolute ampleness

Source: Rydh, arXiv:0708.3333v2, Theorem 4.4 and Proposition 4.7; Stacks
Project, Groupoids Tag 03JE, Algebra Tag 00IS, Schemes Tags 01JA--01JC.
(blueprint: lem-per-ample-finite-group-quotient-construction)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Construct the finite categorical geometric quotient from an ample source.
This is the invariant-affine construction alone: no ampleness or quasi-projectivity
of the quotient, and no projectivity or integrality assertion, is included.

Source: Rydh, arXiv:0708.3333v2, Theorem 4.4 and Proposition 4.7;
Stacks Project, Groupoids 03JE, Algebra 00IS, Schemes 01JA--01JC.
(blueprint: lem-per-ample-finite-group-quotient-construction).

Proof:
1. Each orbit is finite. The ample finite-principal-affine theorem encloses it in
   an affine open inside any specified invariant open. Apply invariant affine
   shrinking to the action groupoid, whose arrows are the disjoint union of H
   copies of V. Its source and target are finite locally free: on the components
   they are identities and automorphisms. Thus invariant affine opens cover V and
   refine every invariant open, including inverse images of base affine opens.
2. On each invariant W=Spec A form C=A^H. The monic polynomial product_h(T-h(a))
   shows each a integral over C. Over an affine T=Spec R of B with W⊆p^-1(T),
   the affine-pairs finite-type criterion makes A finite type over R. The same
   generators generate over C, so integral finite generation makes A finite as
   a C-module. Artin--Tate over the Noetherian R makes C finite type over R.
3. The affine-groupoid orbit-fibres theorem gives surjectivity and orbit fibres
   for Spec A→Spec C, including over each algebraically closed field. A point
   of the geometric pullback is a rational point: its residue field is algebraic
   over the algebraically closed field because this morphism is finite. Thus
   the theorem on field-valued points gives transitivity on the actual pullback
   carrier, using the maps induced by each a_h and the pullback universal property.
   The integral spectrum map is closed, hence a topological quotient.
4. For f∈C prove C_f=(A_f)^H. Injectivity follows from the zero-fraction criterion.
   For a fixed fraction a/f^r, choose for each h an exponent killing h(a)-a.
   Their maximum works for every h, so f^n*a∈C represents the same fraction.
   This argument includes zero divisors, nilpotent f and zero rings. These
   identifications commute with restriction and identify the invariant sheaf
   with O_Spec(C) on the distinguished-open basis and hence on all opens.
5. On the topological orbit space |V|/H put the sheaf of invariant sections.
   The images of invariant affine opens are open, with inverse image exactly W.
   Steps 3--4 identify the restrictions with Spec C. The identifications on
   overlaps are the identity on the common invariant sheaf, so the cocycle
   condition holds. Glue these charts to Q and the local ring maps to q.
   Finiteness is local on the target, hence q is finite and surjective, with
   the orbit topology, orbit fibres and sectionwise invariant-sheaf formula.
6. An invariant morphism V→Z factors continuously through the orbit topology.
   On every open of Z its pullback on sections is fixed and therefore factors
   uniquely through the invariant sheaf. The resulting ringed-space map is
   local: for a point of Q choose a point above it; the image of a nonunit
   germ in O_Z is a nonunit upstairs, so cannot be a unit downstairs. This
   gives the unique scheme morphism Q→Z. Apply it to p to obtain r and q r=p.
7. The affine charts in Step 2 cover each r^-1(T), proving r locally of finite
   type. For any invariant open U, its image W in Q is open and q^-1(W)=U.
   Restrict the action and the same invariant sheaf. Step 1 gives its affine
   charts even when U is not quasi-compact. The same arguments prove the
   admissible finite quotient and categorical assertions for q_U:U→W.
No arbitrary quotient object is defined by choosing a witness: the construction
in this proof is the orbit space with its explicitly specified invariant sheaf. -/
theorem exists_finiteGroup_quotient_of_ample
    (B V : Scheme.{u}) [IsNoetherian B] [IsNoetherian V]
    (p : V ⟶ B) [LocallyOfFiniteType p]
    (L : V.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple V L)
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V)
    (ha : ∀ h : H, (a h).hom ≫ p = p) :
    ∃ (Q : Scheme.{u}) (r : Q ⟶ B) (q : V ⟶ Q),
      q ≫ r = p ∧ IsAdmissibleFiniteSchemeQuotient a q ∧ Surjective q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Q),
        Nonempty ↥(pullback (C := Scheme.{u}) q t) ∧
        ∀ x y : ↥(pullback (C := Scheme.{u}) q t),
          ∃ (h : H) (l : pullback q t ⟶ pullback q t),
            l ≫ pullback.fst q t = pullback.fst q t ≫ (a h).hom ∧
            l ≫ pullback.snd q t = pullback.snd q t ∧ l x = y) ∧
      (∀ (Z : Scheme.{u}) (f : V ⟶ Z), (∀ h : H, (a h).hom ≫ f = f) →
        ∃! g : Q ⟶ Z, q ≫ g = f) ∧
      LocallyOfFiniteType r ∧
      ∀ U : V.Opens, (∀ h : H, (a h).hom ⁻¹ᵁ U = U) →
        ∃ (W : Q.Opens) (aU : H →* Aut U.toScheme) (qU : U.toScheme ⟶ W.toScheme),
          q ⁻¹ᵁ W = U ∧
          (∀ h : H, (aU h).hom ≫ U.ι = U.ι ≫ (a h).hom) ∧
          qU ≫ W.ι = U.ι ≫ q ∧ IsAdmissibleFiniteSchemeQuotient aU qU ∧
          ∀ (Z : Scheme.{u}) (f : U.toScheme ⟶ Z),
            (∀ h : H, (aU h).hom ≫ f = f) →
              ∃! g : W.toScheme ⟶ Z, qU ≫ g = f := by sorry

end AlgebraicGeometry
