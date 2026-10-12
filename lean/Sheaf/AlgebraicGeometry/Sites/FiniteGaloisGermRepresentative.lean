module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.Galois.GaloisClosure

import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-!
# Finite Galois representatives of geometric germs

Source: Stacks Project, Tag 04JM, direct proof of Lemma 59.56.5.
(blueprint: lem-exc-field-invariant-germ-representative-construction).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- Source: Stacks Project, Tag 04JM, the finite Galois neighbourhood step.
(blueprint: lem-exc-field-invariant-germ-representative-construction).

Proof: Joint surjectivity of the stalk injections represents m in a pointed etale
neighbourhood X. The component of X containing the geometric lift is an open singleton,
isomorphic over K to the spectrum of a finite separable extension P/K, by the etale
fibre theorem over a field. The lift embeds P into Ω. Every element in its image is
separable over K, so lies in the image of Ks; thus this embedding factors through Ks.
Take a finite K-basis of P and a finite K-basis of L, viewed in Ks. The finite Galois
intermediate field obtained by adjoining all their conjugates contains both fields.
The inclusion P into this field E gives a pointed map Spec E to X. Pull back the section
along this map. Naturality of the stalk injections preserves its germ m. The canonical
embedding E into Ks into Ω supplies y and its specified underlying morphism.
No invariance or descent is used here; the construction works for every germ. -/
theorem exists_finiteGalois_germ_representative
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (L : IntermediateField K Ks) [FiniteDimensional K L]
    (m : (pointSmallEtale s).sheafFiber.obj F) :
    ∃ E : FiniteGaloisIntermediateField K Ks,
      L ≤ E.toIntermediateField ∧
      ∃ y : (pointSmallEtale s).fiber.obj (etaleSpec K E),
        y.left = Spec.map
          (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)) ∧
        ∃ z : F.obj.obj (op (etaleSpec K E)),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z = m := by
  sorry

end AlgebraicGeometry.Scheme
