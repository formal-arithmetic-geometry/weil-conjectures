/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernNormalization
import WeilConjectures.WeilSheaf.Projective.ProjectiveChernTensorFactorization

/-! # Top cohomology of a single normalized Chern adjunct

Source: current blueprint, projective-line cohomology and diagonal-tower-trace (1).
(blueprint: lem-pur-v5-projective-chern-adjunct-top).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Limits

private theorem map_chern_component_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]
    {V U K : C} (v : V ⟶ K) (b : U ⟶ K) [IsIso (biprod.desc v b)]
    (hV : IsZero (F.obj V)) : IsIso (F.map b) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have he : (isoZeroBiprod (Y := F.obj U) hV).hom ≫
      (F.mapBiprod V U).inv ≫ F.map (biprod.desc v b) = F.map b := by
    rw [isoZeroBiprod_hom, Functor.mapBiprod_inv, biprod.inr_desc_assoc,
      ← F.map_comp, biprod.inr_desc]
  rw [← he]
  infer_instance

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] in
private theorem projectiveChernBaseEncoding_reflects_homology
    {A B : WeilComplex k₀ l X} (f : A ⟶ B) (n : ℤ)
    (hf : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((projectiveChernBaseEncoding X).map f))) :
    IsIso ((homologySheaf n).map f) := by
  let E := projectiveChernBaseSheafEncoding (k₀ := k₀) (l := l) X
  have hE : IsIso (E.map ((DerivedCategory.homologyFunctor _ n).map f.hom)) :=
    (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso n) f.hom).2 hf
  have h : IsIso ((DerivedCategory.homologyFunctor _ n).map f.hom) :=
    isIso_of_reflects_iso _ E
  let : IsIso ((WeilSheaf.objectProperty k₀ l X).ι.map
      ((homologySheaf n).map f)) := h
  let : (WeilSheaf.objectProperty k₀ l X).ι.ReflectsIsomorphisms :=
    (Functor.FullyFaithful.ofFullyFaithful _).reflectsIsomorphisms
  exact isIso_of_reflects_iso ((homologySheaf n).map f)
    (WeilSheaf.objectProperty k₀ l X).ι

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] in
private theorem projectiveChernBaseEncoding_single_homology_zero (M : WeilSheaf k₀ l X) :
    IsZero ((DerivedCategory.homologyFunctor _ (2 : ℤ)).obj
      ((projectiveChernBaseEncoding X).obj (WeilSheaf.toComplex.obj M))) := by
  let E := projectiveChernBaseSheafEncoding (k₀ := k₀) (l := l) X
  apply E.isZero_homologyFunctor_mapDerivedCategory_obj
  exact (isZero_homologySheaf_obj_iff 2 _).1
    (isZero_homologySheaf_singleComplex (by decide) M)

/-- A single normalized tensor-Chern arrow has an adjunct invertible on H2.
There is no naturality, shift compatibility or existence assertion in this lemma.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-p1-cohomology/thm-amb-p1-decomposition.proof.md, coefficient calculation and
projection formula; sk-prop-diagonal-tower-trace.proof.md (1); top-class steps 4--7.
(blueprint: lem-pur-v5-projective-chern-adjunct-top).

Proof: forget equivariance, use the specified encoding, and restrict to an affine open
V of X. Derived forgetting compares the actual right adjoint and its unit with ordinary
module direct image and its unit. Exact open restriction compares these functors and
the tensor construction. In the strict integral tower the unit and positive Cartier
class of infinity give the projective-line isomorphism. Apply Rlim to this whole arrow;
the completed-coefficient criterion lifts it uniquely to completed Z_l coefficients,
since both coefficient lines and the proper direct image are derived complete. Invert
ell and extend through the finite-subextension colimit. The proper scalar comparison
preserves the unit and the Cartier component, so this is the corresponding ordinary
condensed coefficient isomorphism. Tensor with the underlying constructible sheaf and
use the proper projection formula. Its top component is precisely the adjunct of tensor
with projectiveChernPositiveClass. The degree-two cohomology of the unshifted summand
vanishes, so that component induces an isomorphism on H2.

The endpoint isomorphisms allowed by ProjectiveChernNormalized do not change this result.
For the source, after the canonical coefficient-unit comparison, their difference is
an automorphism of a pulled-back sheaf shifted by minus two. For the target, after Tate
evaluation and shift addition, their difference is an automorphism of a pulled-back
sheaf. Pullback on ordinary sheaves is fully faithful for the projective-line projection:
the H0 adjunction unit is invertible, by the degree-zero projective-line calculation.
Thus these two automorphisms descend from V. Naturality of the adjunction unit shows
that the new adjunct differs from the canonical one by invertible precomposition and
invertible pushforward of postcomposition. Its H2 map is therefore also invertible.
This uses the degree-zero sheaf Hom identification, not an assertion that derived
pullback is fully faithful. Finally affine restriction detects cohomological
isomorphisms, and exact conservative forgetting reflects the native H2 isomorphism.
The zero sheaf and empty base satisfy the same argument. -/
theorem projectiveChern_adjunct_top_isIso
    (C : ProEtale.NativeCartier.Construction k₀ l) (M : WeilSheaf k₀ l X)
    (a : (upperStar (ProjectiveLine X ↘ X)).obj
        ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
          (WeilSheaf.toComplex.obj M)) ⟶
      (upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M))
    (ha : ProjectiveChernNormalized X C M a) :
    IsIso ((homologySheaf 2).map
      ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
        (ProjectiveLine X ↘ X)).homEquiv _ _ a)) := by
  obtain ⟨v, hv⟩ := projectiveChern_coefficient_splitting X C
  obtain ⟨s, t, z, ha'⟩ := projectiveChern_tensor_factorization X C M a ha
  let H := DerivedCategory.homologyFunctor
    (ProEtale.NativeCartier.Modules l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) 2
  let F := projectiveChernTensorTransport X M ⋙ H
  have hz : IsZero (F.obj ((projectiveChernCoefficientLine (l := l) X)⟦(2 : ℤ)⟧)) :=
    (projectiveChernBaseEncoding_single_homology_zero X M).of_iso (H.mapIso z)
  have : IsIso (F.map (projectiveChernCoefficientAdjunct X C)) :=
    map_chern_component_isIso F v (projectiveChernCoefficientAdjunct X C) hz
  apply projectiveChernBaseEncoding_reflects_homology X
  change IsIso (H.map ((projectiveChernBaseEncoding X).map _))
  rw [ha', H.map_comp, H.map_comp]
  have hmid : IsIso (H.map ((projectiveChernTensorTransport X M).map
      (projectiveChernCoefficientAdjunct X C))) :=
    ‹IsIso (F.map (projectiveChernCoefficientAdjunct X C))›
  exact IsIso.comp_isIso' (inferInstance : IsIso (H.map s.hom))
    (IsIso.comp_isIso' hmid (inferInstance : IsIso (H.map t.hom)))

end AlgebraicGeometry.WeilComplex
