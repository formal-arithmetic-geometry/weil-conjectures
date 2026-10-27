/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.AlgebraicGeometry.NilpotentBaseChangeIdempotents
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import WeilConjectures.Algebra.FiniteTypeLiftNilpotent
import Sheaf.RingTheory.SyntomicAlgebraSurjectionLift

/-!
# Lifting marked affine local complete intersection deformations

Source: Stacks Project, Examples of Deformation Problems, Tags 0DZH and 0DYX,
Example `example-schemes`; Formal Deformation Theory, `definition-CLambda`
(blueprint: lem-sfb-affine-lci-artinian-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

/-- A marked flat deformation of an affine lci lifts across an Artinian coefficient
surjection. Source: Stacks Project, Examples of Deformation Problems, Tags 0DZH and
0DYX; Formal Deformation Theory, `definition-CLambda`
(blueprint: lem-sfb-affine-lci-artinian-lift).

The special fibre of the lift is taken along the composite Spec k → Spec A → Spec A'.
The residue compatibility hypothesis identifies this with the specified residue map
of A'. The last equation uses the canonical pasting isomorphism and pullback map,
so that the A-isomorphism reduces to the specified marking, including its actual map.
No dimension, smoothness, nonemptiness, or coefficient-field embedding is required.

Proof: by lem-weil-pbc-artinian-local-noetherian-nilpotent, A is Noetherian and its
maximal ideal is nilpotent. The base change of Y to its residue field is a thickening
by clause (1) of lem-weil-pbc-base-change-nilpotent-thickening-idempotents. Its source
is affine by the given marking, so lem-weil-pbc-thickening-affine-scheme makes Y affine.
Write Y = Spec Q. By lem-weil-pbc-flat-ring-map-iff-flat-affine, Q is flat over A.
The affine fibre-product formula lem-weil-pbc-fibre-product-affine-spectra identifies
Q tensor_A k with P. The mutually inverse maps q tensor a ↦ aq and q ↦ q tensor 1
identify this tensor product with Q/mQ. Thus Q/mQ is finite type, and
lem-weil-pbc-finite-type-lift-nilpotent makes Q finite type over A. The Noetherian
finite-presentation lemma lem-weil-pbc-finite-type-noetherian-finite-presentation
makes Q finitely presented. Nilpotence puts m in every prime of A, so m is its only
prime; its fibre P is lci. Apply lem-sfb-syntomic-algebra-surjection-lift to A' → A
and Q. It gives a syntomic Q' and a compatible isomorphism Q'/ker(π)Q' ≅ Q.
Set Y' = Spec Q'; it is flat and affine. The affine fibre-product formula and the
quotient-tensor identification give the A-isomorphism α. Define ι' by reducing α
and composing with ι. The pullback universal property gives exactly the pasting
isomorphism and map in the last equation. For P = 0, Y is empty because a thickening
preserves the underlying space; the empty lift gives the same construction. -/
theorem exists_affine_lci_artinian_lift
    (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ] [IsLocalRing Λ]
    (k : Type u) [Field k] [Algebra Λ k]
    (eΛ : IsLocalRing.ResidueField Λ ≃ₐ[Λ] k)
    (A' A : Type u) [CommRing A'] [CommRing A]
    [IsArtinianRing A'] [IsLocalRing A'] [IsArtinianRing A] [IsLocalRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (eA' : IsLocalRing.ResidueField A' ≃ₐ[Λ] k)
    (eA : IsLocalRing.ResidueField A ≃ₐ[Λ] k)
    (π : A' →ₐ[Λ] A) [IsLocalHom π.toRingHom] (hπ : Function.Surjective π)
    (hπk : (eA.toRingHom.comp (IsLocalRing.residue A)).comp π.toRingHom =
      eA'.toRingHom.comp (IsLocalRing.residue A'))
    (P : Type u) [CommRing P] [Algebra k P] [Algebra.FiniteType k P]
    (hP : Algebra.IsLocalCompleteIntersection k P)
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) [Flat f]
    (ι : pullback f (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A)))) ≅
      Spec (.of P))
    (hι : ι.hom ≫ Spec.map (ofHom (algebraMap k P)) =
      pullback.snd f (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))))) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (.of A')),
      Flat f' ∧ IsAffine Y' ∧
      ∃ (α : pullback f' (Spec.map (ofHom π.toRingHom)) ≅ Y)
        (hα : α.hom ≫ f = pullback.snd f' (Spec.map (ofHom π.toRingHom)))
        (ι' : pullback f'
          (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))) ≫
            Spec.map (ofHom π.toRingHom)) ≅ Spec (.of P)),
        ι'.hom ≫ Spec.map (ofHom (algebraMap k P)) =
          pullback.snd f'
            (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))) ≫
              Spec.map (ofHom π.toRingHom)) ∧
        (pullbackLeftPullbackSndIso f' (Spec.map (ofHom π.toRingHom))
          (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))))).inv ≫
          pullback.map (pullback.snd f' (Spec.map (ofHom π.toRingHom)))
            (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A)))) f
            (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))))
            α.hom (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans hα.symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ ι.hom = ι'.hom := by
  sorry

end AlgebraicGeometry
