module

public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Data.Int.Interval

/-! # Bounded realization with a supplied flat K-flat right factor

Source: Stacks Project, sites-cohomology.tex, Tag 06YU, definition-derived-tor and
its preceding one-sided construction; homology.tex, Tag 012Z; Mathlib's
`DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`.
(blueprint: lem-sf-bounded-one-sided-tensor-realization)

The tensor functors and two-sided representative comparison are precisely the
published ringed-site descent data. The total tensor is the signed direct-sum
cochain total, with differential d_B tensor 1 + (-1)^j 1 tensor d_P on (j,h).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c m a w

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

/-- A bounded derived input and a supplied bounded flat K-flat right factor have a
bounded signed total realization. The natural comparison `cR` is normalized by
`representativeIso` on every flat-term K-flat left factor. For every bounded
representative `K` and every representing isomorphism `e`, the displayed isomorphism
is exactly tensoring `e` with the identity followed by `cR` inverse at `K`.
No flatness, K-flatness or Tor-amplitude condition is imposed on `B` or `K`.

Source: Stacks Project, sites-cohomology.tex, construction preceding Tag 06YU;
homology.tex, Tag 012Z; Mathlib, DerivedCategory/TStructure.lean,
`exists_iso_Q_obj_of_isGE_of_isLE`.
(blueprint: lem-sf-bounded-one-sided-tensor-realization)

Proof:
1. Apply lem-sfb-bounded-representative in the abelian category of module sheaves,
   using the assumed cohomology bounds. This gives a complex supported in [r,s]
   and an isomorphism from B to its localization.
2. Apply the right-factor clause of lem-weil-pbc-kflat-fixed-tensor-triangulated
   to the supplied flat-term K-flat P and the specified site tensor descent.
   It gives cR already normalized by the specified two-sided comparison.
   Compose with the image of any representing e under right derived tensor.
   This works for every representative, with no condition of flatness on it.
3. By def-pc-tensor-complex-sheaves the total has direct-sum terms indexed by
   j+h=d and differential d_K tensor 1 + (-1)^j 1 tensor d_P. A tensor summand
   is zero if either factor is zero, by def-pur-sheaf-tensor-product. Only pairs
   in [r,s] times [u,v] can remain, a finite set. Outside [r+u,s+v] no pair
   remains; the coproduct universal property makes the total term zero.
4. A zero degree-d term has zero degree-d cohomology. Cohomology factors through
   Q by def-weil-abstract-derived-category. Transfer vanishing along the comparison
   and use def-weil-pbc-bounded-derived-subcategories to obtain D^b and D^+.
   Only weak endpoint inequalities are used: equal endpoints, zero inputs and the
   zero ring are included, and neither endpoint is required to be nonzero.
-/
theorem bounded_one_sided_tensor_realization
    {C : Type c} [Category.{m} C] [EssentiallySmall.{a} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{a})
    [HasDerivedCategory.{w} (Modules R)]
    (r s u v : ℤ) (hrs : r ≤ s) (huv : u ≤ v)
    (B : DerivedCategory (Modules R))
    (hB : ∀ j : ℤ, j < r ∨ s < j →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) j).obj B))
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (hPf : ∀ h : ℤ, IsFlatOnSite (J := J) (R := R) (P.X h))
    (hPs : ∀ h : ℤ, h < u ∨ v < h → IsZero (P.X h)) :
    (∃ K : CochainComplex (Modules R) ℤ,
      (∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j)) ∧
      Nonempty (B ≅ DerivedCategory.Q.obj K)) ∧
    (∃ cR : (totalTensor R).flip.obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (derivedTensor R).flip.obj (DerivedCategory.Q.obj P),
      (∀ (V : CochainComplex (Modules R) ℤ)
        (hV : CochainComplex.IsKFlatIndependentCoefficients V)
        (hVf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := R) (V.X j)),
        cR.app V = representativeIso R V P hV hP hVf hPf) ∧
      (∀ (K : CochainComplex (Modules R) ℤ)
        (_hK : ∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j))
        (e : B ≅ DerivedCategory.Q.obj K),
        (∃ i : ((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).obj B ≅
              DerivedCategory.Q.obj (((totalTensor R).obj K).obj P),
            i = ((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).mapIso e ≪≫
              (cR.app K).symm) ∧
        (∀ d : ℤ, d < r + u ∨ s + v < d →
          IsZero ((((totalTensor R).obj K).obj P).X d)) ∧
        (∀ d : ℤ, Set.Finite {p : ℤ × ℤ | p.1 + p.2 = d ∧
          ¬ IsZero (((ordinaryTensor R).obj (K.X p.1)).obj (P.X p.2))}))) ∧
    (∀ d : ℤ, d < r + u ∨ s + v < d →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) d).obj
        (((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).obj B))) ∧
    DerivedCategory.TStructure.t.bounded
      (((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).obj B) ∧
    DerivedCategory.TStructure.t.plus
      (((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).obj B) := by
  classical
  have hbounds : r + u ≤ s + v := add_le_add hrs huv
  have : B.IsGE r := (DerivedCategory.isGE_iff B r).2
    (fun j hj ↦ hB j (Or.inl hj))
  have : B.IsLE s := (DerivedCategory.isLE_iff B s).2
    (fun j hj ↦ hB j (Or.inr hj))
  obtain ⟨K₀, hK₀ge, hK₀le, ⟨e₀⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE B r s
  have hK₀ : ∀ j : ℤ, j < r ∨ s < j → IsZero (K₀.X j) := by
    intro j hj
    rcases hj with hj | hj
    · exact K₀.isZero_of_isStrictlyGE r j hj
    · exact K₀.isZero_of_isStrictlyLE s j hj
  obtain ⟨_, hfixed⟩ := kFlat_fixed_tensor_triangulated R
  obtain ⟨cR, _, hcR⟩ := (hfixed P hP hPf).2.2.2.2.1
  have hz (K : CochainComplex (Modules R) ℤ)
      (hK : ∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j))
      (j h : ℤ) (hout : j < r ∨ s < j ∨ h < u ∨ v < h) :
      IsZero (((ordinaryTensor R).obj (K.X j)).obj (P.X h)) := by
    have := tensorAdditive R
    have := tensorObjAdditive R (K.X j)
    rcases hout with hj | hj | hh | hh
    · exact ((ordinaryTensor R).flip.obj (P.X h)).map_isZero (hK j (Or.inl hj))
    · exact ((ordinaryTensor R).flip.obj (P.X h)).map_isZero (hK j (Or.inr hj))
    · exact ((ordinaryTensor R).obj (K.X j)).map_isZero (hPs h (Or.inl hh))
    · exact ((ordinaryTensor R).obj (K.X j)).map_isZero (hPs h (Or.inr hh))
  have hsupp (K : CochainComplex (Modules R) ℤ)
      (hK : ∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j))
      (d : ℤ) (hd : d < r + u ∨ s + v < d) :
      IsZero ((((totalTensor R).obj K).obj P).X d) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro j h heq
    have heq' : j + h = d := heq
    exact (hz K hK j h (by omega)).eq_of_src _ _
  have hfin (K : CochainComplex (Modules R) ℤ)
      (hK : ∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j)) (d : ℤ) :
      Set.Finite {p : ℤ × ℤ | p.1 + p.2 = d ∧
        ¬ IsZero (((ordinaryTensor R).obj (K.X p.1)).obj (P.X p.2))} := by
    apply (Set.finite_Icc (r, u) (s, v)).subset
    intro p hp
    have ho : ¬ (p.1 < r ∨ s < p.1 ∨ p.2 < u ∨ v < p.2) :=
      fun ho ↦ hp.2 (hz K hK p.1 p.2 ho)
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  let i₀ := ((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).mapIso e₀ ≪≫
    (cR.app K₀).symm
  have hH (d : ℤ) (hd : d < r + u ∨ s + v < d) :
      IsZero ((DerivedCategory.homologyFunctor (Modules R) d).obj
        (((derivedTensor R).flip.obj (DerivedCategory.Q.obj P)).obj B)) := by
    have ht := hsupp K₀ hK₀ d hd
    have hh := ShortComplex.isZero_homology_of_isZero_X₂
      ((((totalTensor R).obj K₀).obj P).sc d) ht
    exact hh.of_iso (((DerivedCategory.homologyFunctor (Modules R) d).mapIso i₀) ≪≫
      (DerivedCategory.homologyFunctorFactors (Modules R) d).app _)
  have hge := (DerivedCategory.isGE_iff _ (r + u)).2
    (fun d hd ↦ hH d (Or.inl hd))
  have hle := (DerivedCategory.isLE_iff _ (s + v)).2
    (fun d hd ↦ hH d (Or.inr hd))
  refine ⟨⟨K₀, hK₀, ⟨e₀⟩⟩, ⟨cR, hcR, ?_⟩, hH,
    ⟨⟨r + u, hge⟩, ⟨s + v, hle⟩⟩, ⟨r + u, hge⟩⟩
  intro K hK e
  exact ⟨⟨_, rfl⟩, hsupp K hK, hfin K hK⟩

end SheafOfModules
