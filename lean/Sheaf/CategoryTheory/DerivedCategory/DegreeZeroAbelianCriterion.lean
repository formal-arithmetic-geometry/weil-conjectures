module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The degree-zero category of a cohomology-stable derived subcategory

Source: blueprint main-20261015, `sec-six-functors-basics`,
`sk-lem-int-integral-heart-triangulated.proof.md`, paragraph (2)
(blueprint: lem-sfb-derived-degree-zero-abelian-criterion).

The full subcategory in the abelian category is the existing Mathlib object property
`T.inverseImage (singleFunctor A 0)`. The restricted single functor is its canonical
`ObjectProperty.lift`. No auxiliary notion or choice of a cone is introduced.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- The degree-zero objects of a strictly full, cohomology-stable triangulated subcategory
form an abelian subcategory with ambient kernels, cokernels, finite biproducts and extensions.
The cone identifications commute with the connecting and cohomology maps, and hence are the
canonical identifications relative to the given distinguished triangle.

Source: blueprint main-20261015, `sk-lem-int-integral-heart-triangulated.proof.md`,
paragraph (2) (blueprint: lem-sfb-derived-degree-zero-abelian-criterion).

Proof plan:
1. Functoriality and strict fullness give isomorphism closure of the inverse-image property.
   The single complex of zero is zero, giving its zero object.
2. The single functor is fully faithful by lem-weil-pbc-derived-single-fully-faithful.
   Fullness of both subcategories gives full faithfulness of its restriction. Single-complex
   cohomology and lem-sf-derived-concentrated-single identify the essential image: a complex
   with cohomology only in degree zero is isomorphic to the single of its zeroth cohomology,
   which belongs to the subcategory by the cohomology-closure hypothesis.
3. Rotate the specified cone triangle. Shift and extension closure of T imply that its cone
   belongs to T (def-weil-triangulated-category, def-weil-triangulated-subcategory).
4. By lem-sf-derived-homology-long-exact the triangle gives the exact sequence
   0 -> H^{-1}(D) -> M -> N -> H^0(D) -> 0. The first and last maps are a kernel and a
   cokernel, respectively, so their universal properties give the displayed isomorphisms
   and equations. Cohomology closure and strict fullness place all ambient kernels and
   cokernels in the inverse-image property (def-weil-pbc-exact-sequence).
5. A short exact sequence in A yields a short exact sequence of single complexes, hence a
   distinguished triangle by lem-weil-pbc-complex-ses-triangle. Extension closure of T gives
   extension closure of the inverse-image property.
6. Apply extension closure to the split short exact sequence of a binary biproduct. Together
   with zero and isomorphism closure this gives every finite ambient biproduct, equivalently
   finite product (def-sp-abelian, def-weil-pbc-exact-sequence).
7. Apply lem-weil-pbc-abelian-full-subcategory-exact to the zero, kernel, cokernel and finite
   product closures. It gives abelianness with inherited addition and ambient kernels and
   cokernels. No boundedness or pre-existing t-structure on T is used. -/
theorem degreeZero_abelian_criterion
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : ObjectProperty (DerivedCategory A))
    [T.IsTriangulated] [T.IsClosedUnderIsomorphisms]
    (hcohomology : ∀ (K : DerivedCategory A), T K → ∀ q : ℤ,
      T ((singleFunctor A 0).obj ((homologyFunctor A q).obj K))) :
    (T.lift ((T.inverseImage (singleFunctor A 0)).ι ⋙ singleFunctor A 0)
      (fun M => M.property)).Full ∧
    (T.lift ((T.inverseImage (singleFunctor A 0)).ι ⋙ singleFunctor A 0)
      (fun M => M.property)).Faithful ∧
    (∀ K : T.FullSubcategory,
      (∃ M : (T.inverseImage (singleFunctor A 0)).FullSubcategory,
        Nonempty ((singleFunctor A 0).obj M.obj ≅ K.obj)) ↔
      ∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor A q).obj K.obj)) ∧
    (∀ (M N : (T.inverseImage (singleFunctor A 0)).FullSubcategory)
      (f : M ⟶ N) (D : DerivedCategory A)
      (g : (singleFunctor A 0).obj N.obj ⟶ D)
      (h : D ⟶ ((singleFunctor A 0).obj M.obj)⟦(1 : ℤ)⟧),
      Triangle.mk ((singleFunctor A 0).map f.hom) g h ∈ distTriang (DerivedCategory A) →
      ∃ (eK : kernel f.hom ≅ (homologyFunctor A (-1)).obj D)
        (eC : cokernel f.hom ≅ (homologyFunctor A 0).obj D),
        eK.hom ≫
            HomologySequence.δ (Triangle.mk ((singleFunctor A 0).map f.hom) g h) (-1) 0 ≫
            (singleFunctorCompHomologyFunctorIso A 0).hom.app M.obj = kernel.ι f.hom ∧
        (singleFunctorCompHomologyFunctorIso A 0).inv.app N.obj ≫
            (homologyFunctor A 0).map g = cokernel.π f.hom ≫ eC.hom ∧
        (T.inverseImage (singleFunctor A 0)) (kernel f.hom) ∧
        (T.inverseImage (singleFunctor A 0)) (cokernel f.hom)) ∧
    (T.inverseImage (singleFunctor A 0)).ContainsZero ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderFiniteProducts ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderKernels ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderCokernels ∧
    (∃ hB : Abelian (T.inverseImage (singleFunctor A 0)).FullSubcategory,
      hB.toPreadditive =
        Preadditive.fullSubcategory (T.inverseImage (singleFunctor A 0)) ∧
      (∀ (M N : (T.inverseImage (singleFunctor A 0)).FullSubcategory) (f : M ⟶ N),
        PreservesLimit (parallelPair f 0) (T.inverseImage (singleFunctor A 0)).ι) ∧
      (∀ (M N : (T.inverseImage (singleFunctor A 0)).FullSubcategory) (f : M ⟶ N),
        PreservesColimit (parallelPair f 0) (T.inverseImage (singleFunctor A 0)).ι)) ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderExtensions := by
  let B := T.inverseImage (singleFunctor A 0)
  have hcone : ∀ (M N : B.FullSubcategory) (f : M ⟶ N) (D : DerivedCategory A)
      (g : (singleFunctor A 0).obj N.obj ⟶ D)
      (h : D ⟶ ((singleFunctor A 0).obj M.obj)⟦(1 : ℤ)⟧),
      Triangle.mk ((singleFunctor A 0).map f.hom) g h ∈ distTriang (DerivedCategory A) →
      ∃ (eK : kernel f.hom ≅ (homologyFunctor A (-1)).obj D)
        (eC : cokernel f.hom ≅ (homologyFunctor A 0).obj D),
        eK.hom ≫
            HomologySequence.δ (Triangle.mk ((singleFunctor A 0).map f.hom) g h) (-1) 0 ≫
            (singleFunctorCompHomologyFunctorIso A 0).hom.app M.obj = kernel.ι f.hom ∧
        (singleFunctorCompHomologyFunctorIso A 0).inv.app N.obj ≫
            (homologyFunctor A 0).map g = cokernel.π f.hom ≫ eC.hom ∧
        B (kernel f.hom) ∧ B (cokernel f.hom) := by
    intro M N f D g h hΔ
    let Δ := Triangle.mk ((singleFunctor A 0).map f.hom) g h
    let eM := (singleFunctorCompHomologyFunctorIso A 0).app M.obj
    let eN := (singleFunctorCompHomologyFunctorIso A 0).app N.obj
    have hnat : (homologyFunctor A 0).map Δ.mor₁ ≫ eN.hom = eM.hom ≫ f.hom :=
      (singleFunctorCompHomologyFunctorIso A 0).hom.naturality f.hom
    have hneg : IsZero ((homologyFunctor A (-1)).obj Δ.obj₂) :=
      isZero_of_isGE ((singleFunctor A 0).obj N.obj) 0 (-1) (by lia)
    have hpos : IsZero ((homologyFunctor A 1).obj Δ.obj₁) :=
      isZero_of_isLE ((singleFunctor A 0).obj M.obj) 0 1 (by lia)
    have : Mono (HomologySequence.δ Δ (-1) 0) :=
      (HomologySequence.exact₃ Δ hΔ (-1) 0).mono_g (hneg.eq_zero_of_src _)
    have : Epi ((homologyFunctor A 0).map Δ.mor₂) :=
      (HomologySequence.exact₃ Δ hΔ 0 1).epi_f (hpos.eq_zero_of_tgt _)
    let k := HomologySequence.δ Δ (-1) 0 ≫ eM.hom
    let c := eN.inv ≫ (homologyFunctor A 0).map Δ.mor₂
    have hk : k ≫ f.hom = 0 := by
      dsimp [k]
      rw [Category.assoc, ← hnat, ← Category.assoc, HomologySequence.δ_comp Δ hΔ (-1) 0]
      simp
    have hc : f.hom ≫ c = 0 := by
      dsimp [c]
      rw [← cancel_epi eM.hom, ← Category.assoc, ← hnat]
      simp [← Functor.map_comp, comp_distTriang_mor_zero₁₂ Δ hΔ]
    let SK := ShortComplex.mk k f.hom hk
    let SC := ShortComplex.mk f.hom c hc
    have hSK : SK.Exact := by
      refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₁ Δ hΔ (-1) 0)
      exact ShortComplex.isoMk (Iso.refl _) eM eN (by simp [SK, k]) hnat.symm
    have hSC : SC.Exact := by
      refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₂ Δ hΔ 0)
      refine ShortComplex.isoMk eM eN (Iso.refl _) hnat.symm ?_
      simp [SC, c]
    have : Mono SK.f := by dsimp [SK, k]; infer_instance
    have : Epi SC.g := by dsimp [SC, c]; infer_instance
    let eK := (kernelIsKernel f.hom).conePointUniqueUpToIso hSK.fIsKernel
    let eC := (cokernelIsCokernel f.hom).coconePointUniqueUpToIso hSC.gIsCokernel
    have hD : T D := T.ext_of_isTriangulatedClosed₃ Δ hΔ M.property N.property
    refine ⟨eK, eC, ?_, ?_, ?_, ?_⟩
    · exact (kernelIsKernel f.hom).conePointUniqueUpToIso_hom_comp
        hSK.fIsKernel WalkingParallelPair.zero
    · exact ((cokernelIsCokernel f.hom).comp_coconePointUniqueUpToIso_hom
        hSC.gIsCokernel WalkingParallelPair.one).symm
    · exact T.prop_of_iso ((singleFunctor A 0).mapIso eK).symm
        (hcohomology D hD (-1))
    · exact T.prop_of_iso ((singleFunctor A 0).mapIso eC).symm
        (hcohomology D hD 0)
  have : B.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦
    T.ext_of_isTriangulatedClosed₂ _ hS.singleTriangle_distinguished h₁ h₃⟩
  have : B.IsClosedUnderBinaryProducts := by
    constructor
    rintro X ⟨p⟩
    refine B.prop_of_iso ?_ (B.prop_biprod
      (p.prop_diag_obj ⟨.left⟩) (p.prop_diag_obj ⟨.right⟩))
    exact biprod.isoProd _ _ ≪≫ HasLimit.isoOfNatIso (diagramIsoPair p.diag).symm ≪≫
      (limit.isLimit _).conePointUniqueUpToIso p.isLimit
  have : B.IsClosedUnderFiniteProducts := .mk'
  have : B.IsClosedUnderKernels := by
    constructor
    rintro _ ⟨f, k, hk, hX, hY⟩
    obtain ⟨D, g, h, hD⟩ := distinguished_cocone_triangle ((singleFunctor A 0).map f)
    obtain ⟨eK, eC, _, _, hK, _⟩ := hcone ⟨_, hX⟩ ⟨_, hY⟩ (B.homMk f) D g h hD
    exact B.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk) hK
  have : B.IsClosedUnderCokernels := by
    constructor
    rintro _ ⟨f, k, hk, hX, hY⟩
    obtain ⟨D, g, h, hD⟩ := distinguished_cocone_triangle ((singleFunctor A 0).map f)
    obtain ⟨eK, eC, _, _, _, hC⟩ := hcone ⟨_, hX⟩ ⟨_, hY⟩ (B.homMk f) D g h hD
    exact B.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk) hC
  refine ⟨inferInstance, inferInstance, ?_, hcone, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, inferInstance⟩
  · intro K
    constructor
    · rintro ⟨M, ⟨e⟩⟩ q hq
      apply IsZero.of_iso _ ((homologyFunctor A q).mapIso e).symm
      obtain hlt | hgt := lt_or_gt_of_ne hq
      · exact isZero_of_isGE _ 0 q hlt
      · exact isZero_of_isLE _ 0 q hgt
    · intro hK
      have : K.obj.IsGE 0 := (isGE_iff _ _).2 (fun i hi ↦ hK i (by lia))
      have : K.obj.IsLE 0 := (isLE_iff _ _).2 (fun i hi ↦ hK i (by lia))
      obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj 0
      exact ⟨⟨M, T.prop_of_iso e K.property⟩, ⟨e.symm⟩⟩
  · exact ⟨inferInstance, rfl, B.preservesKernels_ι, B.preservesCokernels_ι⟩

end DerivedCategory
