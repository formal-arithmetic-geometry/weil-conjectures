module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.Galois.GaloisClosure

import Sheaf.AlgebraicGeometry.Sites.FiniteGaloisSectionsDescent
import Sheaf.FieldTheory.GaloisAutomorphismExtension

/-!
# Descent of an invariant finite Galois germ representative

Source: Stacks Project, Tag 04JM, direct proof of Lemma 59.56.5.
(blueprint: lem-exc-field-invariant-germ-representative-identification).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- Source: Stacks Project, Tag 04JM, invariance and finite Galois descent.
(blueprint: lem-exc-field-invariant-germ-representative-identification).

Proof: Since E/K is finite Galois and contains L, E/L is finite Galois. Every
L-automorphism q of E extends to a K-automorphism g of Ks fixing L, and then to a
K-automorphism τ of Ω. The compatibility of the canonical lifts identifies the germ
of q's pullback of z with the action of g on the germ of z, by haction and naturality
of the stalk injections. The hypothesis hz makes these germs equal. The supplied
injectivity hinj therefore makes q's pullback of z equal to z.
Restrict F to the small etale site of Spec L using composition with Spec L to Spec K.
Etale covers are preserved by this functor, so this restriction is a sheaf. Apply
finiteGaloisSectionsDescent to this sheaf and E/L, using the invariance just proved,
to obtain a section w over Spec L whose pullback to Spec E is z. The chosen canonical
y maps to x because the embeddings of L into E into Ks into Ω agree. Naturality of
the stalk injections then identifies the germ of w at x with the germ of z at y.
The case E=L is the identity cover and the argument gives w=z. -/
theorem exists_fieldSection_of_finiteGalois_invariant_representative
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (action : MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F))
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      action.smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
        (pointSmallEtale s).toPresheafFiber X x' F.obj z)
    (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : (pointSmallEtale s).fiber.obj (etaleSpec K L))
    (hx : x.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype)))
    (E : FiniteGaloisIntermediateField K Ks) (hLE : L ≤ E.toIntermediateField)
    (y : (pointSmallEtale s).fiber.obj (etaleSpec K E))
    (hy : y.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)))
    (z : F.obj.obj (op (etaleSpec K E)))
    (hinj : Function.Injective
      ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj))
    (hz : ∀ g ∈ L.fixingSubgroup,
      action.smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) :
    ∃ w : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj w =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z := by
  sorry

end AlgebraicGeometry.Scheme
