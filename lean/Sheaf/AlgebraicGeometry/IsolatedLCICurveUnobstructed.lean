module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Mathlib.RingTheory.HopkinsLevitzki
import Sheaf.TraceFormula.LciAffineOpenLocality
import Sheaf.AlgebraicGeometry.AffineLciArtinianLift

/-! # Unobstructed deformations of curves with isolated lci singularities

Source: Stacks Project, Examples of Deformation Problems, Tag 0DZQ,
`lemma-curve-isolated-lci`, `example-schemes`, and `section-general`.
(blueprint: lem-sfb-isolated-lci-curve-unobstructed).

Unobstructedness is written as its lifting property for marked flat deformations.
The residue-field maps encode the coefficient category, including mixed characteristic.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

/-- A separated finite-type lci scheme of dimension at most one, smooth away from
finitely many points, has unobstructed deformations over every Noetherian local
coefficient ring with the specified residue field.
Source: Stacks Project, Examples of Deformation Problems, Tag 0DZQ,
`lemma-curve-isolated-lci`, `example-schemes`, and `section-general`.
(blueprint: lem-sfb-isolated-lci-curve-unobstructed).

The lci condition is an affine open cover by finitely generated lci algebras.
The special fibre of the lift uses Spec k → Spec A → Spec A'; `hπk` identifies this
composite with the specified residue map for A'. The final equation uses the canonical
pullback-pasting isomorphism and reduction of α, and is exactly compatibility of markings.

Proof:
1. Form the union W of the smooth source opens using
   lem-weil-pbc-smooth-local-on-source and
   lem-weil-pbc-smooth-restrict-open-subschemes. Its complement P is closed and finite.
   By lem-sc-lft-over-field-jacobson-space, closed points are dense in P; finiteness
   makes their union closed, so all points of P are closed, also when P is empty.
2. Apply lem-sfb-isolated-curve-two-affine-cover to obtain X = U ∪ V with P contained
   in V, affine U, V and U ∩ V, and smooth U and U ∩ V. Apply
   lem-trf-lci-affine-open-locality to V to obtain its finitely generated lci algebra.
3. Fix the coefficient surjection and marked deformation Y. By
   lem-weil-pbc-artinian-local-noetherian-nilpotent, the maximal ideal of A is nilpotent.
   On affine charts the special fibre is Spec(B/mB) → Spec B; every prime contains mB
   and the quotient bijection respects basic opens, so this is a homeomorphism.
   These identifications glue. Restrict Y to the open corresponding to V. The pullback
   universal property identifies its special fibre with V; restriction preserves flatness.
4. Apply lem-sfb-affine-lci-artinian-lift to this restricted deformation, giving a flat
   affine lift Z over A' and a compatible A-isomorphism from its reduction to Y_V.
5. Apply lem-sfb-smooth-open-coefficient-lift with U, V and this prescribed lift Z.
   The smoothness of U and U ∩ V gives a global flat lift Y' and A-isomorphism α,
   agreeing with Z over V. This works for the specified coefficient rings in every
   characteristic, without properness or connectedness assumptions.
6. Define the marking ι' by reducing α and composing with ι. Pullback pasting gives
   exactly the last equality below. This proves the required lifting property for every
   surjection and every deformation; empty opens also give the empty-scheme case. -/
theorem isolated_lci_curve_unobstructed
    (k : Type u) [Field k] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (hlci : ∃ (I : Type u) (C : I → CommRingCat.{u})
      (aC : ∀ i, Algebra k (C i)) (ftC : ∀ i, Algebra.FiniteType k (C i))
      (φ : ∀ i, Spec (C i) ⟶ X),
      (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ s =
          Spec.map (ofHom (@algebraMap k (C i) _ _ (aC i)))) ∧
        (∀ x : X, ∃ i, ∃ y : Spec (C i), φ i y = x) ∧
        (∀ i, @Algebra.IsLocalCompleteIntersection k (C i) _ _ (aC i) (ftC i)))
    (hsmooth : ∃ P : Set X, P.Finite ∧
      ∀ x ∉ P, ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ s))
    (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ] [IsLocalRing Λ]
    [Algebra Λ k] (eΛ : IsLocalRing.ResidueField Λ ≃ₐ[Λ] k)
    (A' A : Type u) [CommRing A'] [CommRing A]
    [IsArtinianRing A'] [IsLocalRing A'] [IsArtinianRing A] [IsLocalRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (eA' : IsLocalRing.ResidueField A' ≃ₐ[Λ] k)
    (eA : IsLocalRing.ResidueField A ≃ₐ[Λ] k)
    (π : A' →ₐ[Λ] A) [IsLocalHom π.toRingHom] (hπ : Function.Surjective π)
    (hπk : (eA.toRingHom.comp (IsLocalRing.residue A)).comp π.toRingHom =
      eA'.toRingHom.comp (IsLocalRing.residue A'))
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) [Flat f]
    (ι : pullback f (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A)))) ≅ X)
    (hι : ι.hom ≫ s =
      pullback.snd f (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))))) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (.of A')),
      Flat f' ∧
      ∃ (α : pullback f' (Spec.map (ofHom π.toRingHom)) ≅ Y)
        (hα : α.hom ≫ f = pullback.snd f' (Spec.map (ofHom π.toRingHom)))
        (ι' : pullback f'
          (Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A))) ≫
            Spec.map (ofHom π.toRingHom)) ≅ X),
        ι'.hom ≫ s =
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
