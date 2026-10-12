/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.Sites.FiniteGaloisSectionsDescent
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# A section representing an invariant geometric germ

Source: Stacks Project, Tag 04JM, direct proof, applied over a finite separable field.
(blueprint: lem-exc-field-invariant-germ-representative).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- Source: Stacks Project, [Tag 04JM](https://stacks.math.columbia.edu/tag/04JM),
the direct proof of Lemma 59.56.5, applied after restricting the sheaf to `Spec L`.
(blueprint: lem-exc-field-invariant-germ-representative).

An invariant germ has a section representative at the specified finite separable field.
The action is supplied as an argument and characterized on germs; this theorem neither
constructs an action nor asserts injectivity, naturality, or independence of embeddings.

Proof:
1. Restrict `F` to the small etale site of `Spec L` by etale composition. The stalk has
   the same pointed neighbourhoods cofinally, with the lift through `Spec L` specified by `x`.
2. Represent `m` in an etale neighbourhood, shrink to the component containing the lift,
   and identify it with a finite separable field by the etale fibre theorem. Embed that
   field in `Ks` using the chosen lift. Take the normal closure inside `Ks` of its
   compositum with `L`, using `FiniteGaloisIntermediateField.adjoin` on the images of
   finite bases. This is finite Galois over `K`, hence over `L`. Its inclusions preserve
   the chosen lifts. Pull the representative back to `Spec E`.
3. The germ map from `Spec E` is injective: equality of germs holds in a common pointed
   refinement; its map to the one-point `Spec E` is an etale surjection, hence a cover,
   and the separated sheaf condition makes restriction injective.
4. Every `L`-automorphism of `E` extends to an element of `L.fixingSubgroup`. Its pullback
   on the representative has the same germ by `haction` and `hm`, so injectivity makes
   the representative invariant under `Gal(E/L)`.
5. Finite Galois sections descent supplies a section over `Spec L`. Naturality of the
   colimit injections shows that its germ at `x` is `m`.

The case `L = K` is the source's global-sections argument. For separably closed `K`,
the finite separable fields are trivial and the assertion reduces to the terminal germ. -/
theorem exists_fieldSection_of_invariant_germ
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
    (m : (pointSmallEtale s).sheafFiber.obj F)
    (hm : ∀ g ∈ L.fixingSubgroup, action.smul g m = m) :
    ∃ z : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj z = m := by sorry

end AlgebraicGeometry.Scheme
