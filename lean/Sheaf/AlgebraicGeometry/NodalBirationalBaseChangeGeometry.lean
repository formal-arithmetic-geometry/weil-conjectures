/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection
import Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.BirationalGenericIsomorphismOpen
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Geometry of a marked nodal curve after birational base change

Source: ILO, Travaux de Gabber, Expose X, Lemma 2.2 proof, printed p.149;
Stacks Project, Tags 02V6 and 0C5B
(blueprint: lem-sfb-nodal-birational-base-change-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Birational base modification preserves the full geometry of a marked nodal curve.
The finite coproduct isomorphism records the marking as a scheme, including when `n = 0`.
Birationality is a dense-open isomorphism commuting with the given morphism; for integral
schemes this also identifies their function fields. The action conclusion specifies the
diagonal action by both projection equations, which uniquely determine it. Field actions
are allowed to be nontrivial, with the inverse in the contravariant Spec convention.

Source: ILO, Travaux de Gabber, Expose X, Lemma 2.2 proof, printed p.149;
Stacks Project, Tags 02V6 and 0C5B
(blueprint: lem-sfb-nodal-birational-base-change-geometry).

Proof (the nine steps of the node):
1. Apply lem-sfb-projective-bundle-base-change to f along t and to t along f. Apply
   lem-trf-projective-bundle-proper to both projections. Finite-type composition and finite
   type over a Noetherian base give finite type and Noetherianity of all four schemes;
   Spec F is Noetherian because a field has only the ideals zero and one.
2. Flatness and finite presentation survive base change. Pullback associativity identifies
   each geometric fibre of g with the corresponding geometric fibre of f, over the same
   algebraically closed field. Nonemptiness, connectedness, reducedness, dimension and the
   completed nodal local-ring condition therefore survive.
3. The dense-open isomorphism for t identifies the generic residue fields. Associativity
   identifies the two generic fibres over this field, giving smoothness and geometric
   integrality. Smooth base change gives smoothness off the inverse image of D.
4. Flat locally finitely presented morphisms are open. The image of every nonempty source
   open meets every dense base open. Hence inverse images of dense opens are dense, and
   the image of the generic fibre is dense, for both f and g.
5. On nonempty affine charts over a domain A, flatness makes B torsion-free, so B injects
   into B tensor Frac(A). The mutually inverse fraction maps identify this tensor product
   with the localization of B at the nonzero elements of A. The affine fibre formula
   identifies its spectrum with a nonempty affine open of the integral generic fibre.
   Thus B is a domain and the total space is reduced.
6. Any two nonempty total-space opens meet the integral generic fibre by step 4, and their
   inverse images there intersect. Thus each total space is nonempty and irreducible;
   together with step 5 this proves integrality of T and W.
7. Apply lem-sfb-birational-generic-isomorphism-open to t to obtain a dense base open over
   which t is an isomorphism. Base change and step 4 give a dense-open isomorphism for q,
   identifying function fields. Surjectivity of q follows by surjective base change.
8. Pull each section s back as (t followed by s, identity). The pullback equations give
   the section identity. Closed-immersion base change and disjointness show that their
   coproduct is exactly M_0. Smooth base change gives the smooth-locus assertion. This
   argument includes the empty coproduct.
9. For j in J use the universal property to define the automorphism of W whose projections
   are q followed by j_T and g followed by j_S0. Equivariance of f and t makes the pair
   compatible. Uniqueness proves the identity and multiplication laws and the inverse
   formula. These projection equations give equivariance and invariance of the pulled-back
   marking and boundary, including empty markings and boundary and nontrivial field actions.
-/
theorem nodal_birational_base_change_geometry
    (F : Type u) [Field F] {S T S₀ M : Scheme.{u}}
    (p : S ⟶ Spec (.of F)) [IsIntegral S]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (f : T ⟶ S) (hf : IsProjectiveBundle f) [Flat f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hnodal : HasNodalGeometricFibres f) [GeometricallyReduced f]
    (hgeneric : ∃ η : S, IsGenericPoint η Set.univ ∧
      Smooth (f.fiberToSpecResidueField η) ∧
      GeometricallyIntegral (f.fiberToSpecResidueField η))
    (D : Closeds S)
    (hsmooth : Smooth (f ∣_ (⟨(D : Set S)ᶜ, D.isClosed.isOpen_compl⟩ : S.Opens)))
    (i : M ⟶ T) [IsClosedImmersion i] (n : ℕ) (s : Fin n → (S ⟶ T))
    (hs : ∀ j : Fin n, s j ≫ f = 𝟙 S)
    (eM : (∐ fun _ : Fin n ↦ S) ≅ M)
    (hM : ∀ j : Fin n, Sigma.ι (fun _ : Fin n ↦ S) j ≫ eM.hom ≫ i = s j)
    (hmark : ∀ j : Fin n, Set.range (s j) ⊆ (f.smoothLocus : Set T))
    (t : S₀ ⟶ S) (ht : IsProjectiveBundle t) [Surjective t] [IsIntegral S₀]
    [Smooth (t ≫ p)]
    (hbirational : ∃ (U : S.Opens) (V : S₀.Opens) (e : V.toScheme ≅ U.toScheme),
      Dense (U : Set S) ∧ Dense (V : Set S₀) ∧ e.hom ≫ U.ι = V.ι ≫ t) :
    IsNoetherian S ∧ IsNoetherian S₀ ∧ IsNoetherian T ∧
    IsNoetherian (pullback (C := Scheme.{u}) f t) ∧
    (LocallyOfFiniteType p ∧ QuasiCompact p) ∧
    (LocallyOfFiniteType (t ≫ p) ∧ QuasiCompact (t ≫ p)) ∧
    (LocallyOfFiniteType (f ≫ p) ∧ QuasiCompact (f ≫ p)) ∧
    (LocallyOfFiniteType (pullback.snd f t ≫ t ≫ p) ∧
      QuasiCompact (pullback.snd f t ≫ t ≫ p)) ∧
    IsIntegral T ∧ IsIntegral (pullback (C := Scheme.{u}) f t) ∧
    IsProjectiveBundle (pullback.snd f t) ∧ IsProper (pullback.snd f t) ∧
    IsProjectiveBundle (pullback.fst f t) ∧ IsProper (pullback.fst f t) ∧
    Flat (pullback.snd f t) ∧ LocallyOfFinitePresentation (pullback.snd f t) ∧
    QuasiCompact (pullback.snd f t) ∧ QuasiSeparated (pullback.snd f t) ∧
    HasNodalGeometricFibres (pullback.snd f t) ∧ GeometricallyReduced (pullback.snd f t) ∧
    Smooth (pullback.snd f t ∣_ (⟨(t ⁻¹' (D : Set S))ᶜ,
      (D.isClosed.preimage t.continuous).isOpen_compl⟩ : S₀.Opens)) ∧
    (∃ η₀ : S₀, IsGenericPoint η₀ Set.univ ∧
      Smooth ((pullback.snd f t).fiberToSpecResidueField η₀) ∧
      GeometricallyIntegral ((pullback.snd f t).fiberToSpecResidueField η₀)) ∧
    IsClosedImmersion (pullback.snd i (pullback.fst f t)) ∧
    (∃ e₀ : (∐ fun _ : Fin n ↦ S₀) ≅ pullback i (pullback.fst f t),
      ∀ j : Fin n, Sigma.ι (fun _ : Fin n ↦ S₀) j ≫ e₀.hom ≫
        pullback.snd i (pullback.fst f t) = f.baseChangeSection (s j) (hs j) t) ∧
    (∀ j : Fin n, f.baseChangeSection (s j) (hs j) t ≫ pullback.snd f t = 𝟙 S₀) ∧
    Pairwise (fun j k : Fin n ↦ Disjoint
      (Set.range (f.baseChangeSection (s j) (hs j) t))
      (Set.range (f.baseChangeSection (s k) (hs k) t))) ∧
    (∀ j : Fin n, Set.range (f.baseChangeSection (s j) (hs j) t) ⊆
      ((pullback.snd f t).smoothLocus : Set (pullback (C := Scheme.{u}) f t))) ∧
    (∀ U : S.Opens, Dense (U : Set S) → Dense (f ⁻¹' (U : Set S))) ∧
    (∀ U : S₀.Opens, Dense (U : Set S₀) →
      Dense ((pullback.snd f t) ⁻¹' (U : Set S₀))) ∧
    (∃ (U : T.Opens) (V : (pullback (C := Scheme.{u}) f t).Opens) (e : V.toScheme ≅ U.toScheme),
      Dense (U : Set T) ∧ Dense (V : Set (pullback (C := Scheme.{u}) f t)) ∧
        e.hom ≫ U.ι = V.ι ≫ pullback.fst f t) ∧
    Surjective (pullback.fst f t) ∧
    (∀ (J : Type v) [Group J] [Finite J] (aF : J →* (F ≃+* F))
      (aS : J →* Aut S) (aT : J →* Aut T) (a₀ : J →* Aut S₀),
      (∀ j : J, (aS j).hom ≫ p =
        p ≫ Spec.map (CommRingCat.ofHom (aF j⁻¹).toRingHom)) →
      (∀ j : J, (aT j).hom ≫ f = f ≫ (aS j).hom) →
      (∀ j : J, (a₀ j).hom ≫ t = t ≫ (aS j).hom) →
      (∀ j : J, (aS j).hom '' (D : Set S) = (D : Set S)) →
      (∀ j : J, (aT j).hom '' Set.range i = Set.range i) →
      ∃ aW : J →* Aut (pullback (C := Scheme.{u}) f t),
        (∀ j : J, (aW j).hom ≫ pullback.snd f t =
          pullback.snd f t ≫ (a₀ j).hom) ∧
        (∀ j : J, (aW j).hom ≫ pullback.fst f t =
          pullback.fst f t ≫ (aT j).hom) ∧
        (∀ j : J, (aW j).hom '' Set.range (pullback.snd i (pullback.fst f t)) =
          Set.range (pullback.snd i (pullback.fst f t))) ∧
        ∀ j : J, (aW j).hom ''
          (Set.range (pullback.snd i (pullback.fst f t)) ∪
            (pullback.snd f t) ⁻¹' (t ⁻¹' (D : Set S))) =
          Set.range (pullback.snd i (pullback.fst f t)) ∪
            (pullback.snd f t) ⁻¹' (t ⁻¹' (D : Set S))) := by
  sorry

end AlgebraicGeometry
