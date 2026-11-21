/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.Algebra.Homology.AffineBaseChangeCohomologyModel
import Mathlib.RingTheory.LocalProperties.Exactness

/-! # The affine single-complex base-change criterion


The affine case of the single-complex criterion, stated with the objects of the
qcqs statement `singleComplexBaseChangeQcqsInduction`: a cartesian square of the
spectra S = Spec R, X = Spec A, S' = Spec R', X' = Spec A', objects K, K' of the
quasi-coherent derived categories (which correspond to complexes M, N of A- and
A'-modules under the affine equivalence), a derived morphism L(g')^*K -> K', the
stalkwise condition `SingleComplexBaseChange.StalkCondition`, and the derived
base-change comparison map followed by Rf'_* of the given morphism.

## References

* Stacks Project, Tag 0DJ8
* Stacks Project, Tag 0DJ9
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a cartesian square of affine schemes X = Spec A, S = Spec R, S' = Spec R',
X' = Spec A', objects K, K' of the quasi-coherent derived categories and a morphism
φ : L(g')^*K -> K', if the stalk maps
H^i(K_x ⊗^L_{O_{S,s}} O_{S',s'}) ⊗ O_{X',x'} -> H^i(K'_{x'}) are isomorphisms for all
x' and i, then the comparison Lg^*Rf_*K -> Rf'_*L(g')^*K -> Rf'_*K' is an isomorphism. -/
theorem singleComplexAffineBaseChangeCore
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (K' : schemeDerivedCategory (Spec (.of A')))
    (hK' : schemeDerivedQCohProperty (Spec (.of A')) K')
    (φ : (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition (Spec.map (CommRingCat.ofHom φf))
      (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
      (Spec.map (CommRingCat.ofHom φg')) sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K ≫
      (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map φ) := by
  obtain ⟨c⟩ := SingleComplexBaseChange.nonempty_coordinates
    (Spec.map (CommRingCat.ofHom φg')) K K' φ
  apply (_root_.DerivedCategory.isIso_iff _ _).mpr
  intro i
  obtain ⟨U, V, a, eU, eV, hcomm, hlocal⟩ :=
    exists_affineBaseChangeCohomologyModel R A R' A' φf φg φg' φf' sq K hK K' hK' φ c i
  have ha : IsIso a := by
    apply (ConcreteCategory.isIso_iff_bijective a).mpr
    apply bijective_of_localized_maximal a.hom
    intro J hJ
    let p : PrimeSpectrum A' := ⟨J, inferInstance⟩
    obtain ⟨lU, lV, hl⟩ := hlocal p
    have ht := (ConcreteCategory.isIso_iff_bijective _).mp (h_stalk c p i)
    have hb : Function.Bijective
        (fun x ↦ lV (LocalizedModule.map J.primeCompl a.hom x)) := by
      have heq : (fun x ↦ lV (LocalizedModule.map J.primeCompl a.hom x)) =
          (fun x ↦ SingleComplexBaseChange.stalkComparison
            (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
            (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
            sq c p i (lU x)) := funext hl
      rw [heq]
      exact ht.comp lU.bijective
    refine ⟨fun x y h ↦ hb.injective (congrArg lV h), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hb.surjective (lV y)
    exact ⟨x, lV.injective hx⟩
  have he : IsIso (eU.hom ≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i).map
        (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
          (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
          (Spec.map (CommRingCat.ofHom φg')) sq.w K ≫
          (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map φ)) := by
    rw [hcomm]
    infer_instance
  exact (isIso_comp_left_iff eU.hom _).mp he

end AlgebraicGeometry
