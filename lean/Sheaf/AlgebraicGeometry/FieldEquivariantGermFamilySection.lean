/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-! # Realizing equivariant families of geometric germs as sections

Source: Stacks Project, Tags 04JM and 03QW, direct invariant-section argument.
(blueprint: lem-exc-field-equivariant-germ-family-section).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 04JM, direct proof of lemma-global-sections-point,
and Tag 03QW, section-galois-action-stalks.
(blueprint: lem-exc-field-equivariant-germ-family-section).

Proof: Let A be the subfield of Omega consisting of elements algebraic over K.
Every pointed etale neighbourhood factors through A, since its residue field is
finite separable over K. Factoring the lifts identifies the two stalk colimits and
their germ maps. Every automorphism of Ks extends to A and then to Omega: fix a
transcendence basis of Omega over A and extend through the algebraic extension.
The germ formula therefore determines rho on every stalk element and identifies it
with the action in fieldSections_stalkInvariants, transported from A to Omega.
An etale K-scheme is the disjoint union of its open singleton components, each the
spectrum of a finite separable field. Choose a lift on one component, embedding its
residue field as an intermediate field L of Ks. The covariance of f makes its value
at that lift invariant under the subgroup fixing L. The invariant-section bijection
of fieldSections_stalkInvariants gives a section on the component with that germ.
The Galois group acts transitively on the component's lifts. Covariance of f and the
canonical germ formula show that this section has germ f(x) at every lift x of the
component, independently of the first lift chosen. The sheaf axiom for the covering
by these disjoint components glues the sections, with no overlap constraints except
on the empty scheme, whose section set is a singleton. The glued section has the
prescribed germs. This includes the empty X, by its empty covering. -/
theorem field_equivariant_germ_family_section
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (X : (Spec (.of K)).Etale) (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X,
          p.toPresheafFiber X x F.obj z = f x := by sorry

end AlgebraicGeometry.Scheme
