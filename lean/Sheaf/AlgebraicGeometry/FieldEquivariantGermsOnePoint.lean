/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-! # Realizing equivariant germs on a one-point etale scheme

Source: Stacks Project, Tags 04JM and 03QW.
(blueprint: lem-exc-field-equivariant-germs-one-point).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 04JM, direct proof of lemma-global-sections-point,
and Tag 03QW, section-galois-action-stalks.
(blueprint: lem-exc-field-equivariant-germs-one-point).

Proof: A nonempty one-point etale K-scheme is the spectrum of a finite separable
extension of K: apply etale_fibre_discrete_separable_points to its fibre over the
unique point of Spec K, identify that fibre with the original scheme, and use its
unique open singleton. Choose a lift and embed its residue field as a finite
intermediate field L of Ks. Let A be the subfield of Omega algebraic over K.
It is algebraically closed: a root in Omega of a polynomial over A is algebraic
also over K, hence lies in A. Every geometric lift on an etale K-scheme factors
uniquely through Spec A, because its residue field is finite separable over K.
These factorizations identify the pointed-neighbourhood categories, stalk colimits,
and germ maps for A and Omega. Every K-automorphism of Ks extends to A, then to
Omega: fix a transcendence basis over A and extend across the algebraic closure
of the resulting rational-function field. Every stalk element has a representative,
so the assumed germ formula identifies rho with the canonical Galois action from
fieldSections_stalkInvariants, under this stalk identification.
For g fixing L choose such an extension; it fixes the chosen lift. Covariance
of f says its value there is invariant under L.fixingSubgroup. The surjectivity
of the invariant-section bijection gives a section with that germ. Every other
lift corresponds to an embedding L into Ks, which extends to a K-automorphism
of Ks and then to Omega. Apply covariance of f and the germ formula to show
that the same section has the prescribed germ at every lift. Transport the
section back across the one-point scheme isomorphism. No gluing over distinct
components is asserted or used in this lemma. -/
theorem field_equivariant_germ_family_section_onePoint
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X,
          p.toPresheafFiber X x F.obj z = f x := by sorry

end AlgebraicGeometry.Scheme
