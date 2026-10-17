/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalagePageData
import Sheaf.CategoryTheory.FilteredComplexDecalagePageImage
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis

/-! # Normalized comparison of individual decalage pages

Source: Stacks Project, Tags 012K and 015X.
(blueprint: lem-sp-filtered-complex-decalage-page-iso).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original quotient page is the subobject of right-interval cohomology
specified by the spectral object's page embedding.
Source: Stacks Project, Tag 012K, cycle and boundary formulas; Tag 015X,
Remark 13.26.15, second filtration.
(blueprint: lem-sp-filtered-complex-decalage-page-iso).

Proof. Let c be the representative class map and m the monic spectral-page
embedding. The proved image equality identifies image(c) with the source of m;
composing the image projection with this identification gives an epimorphism b
with b followed by m equal to c. Let a be the epic original page quotient on
representatives. The proved representative-kernel equality gives ker(a)=ker(c),
and monicity of m gives ker(c)=ker(b). The cokernel universal property of an
epimorphism in an abelian category now descends b through a and a through b.
Their two composites are identities by cancellation with a and b. This defines
the required page isomorphism. Every normalized representative projection is
the same map, by cancellation with the graded-cycle inclusion, so the displayed
isomorphism satisfies the normalization for every such projection. Finally,
cancel a and m to prove uniqueness of any normalized isomorphism. -/
theorem filteredComplex_decalage_page_iso
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    ∃! e : filteredComplexPageObject U.obj U.filtration r (p, q) ≅
      ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
        r hr).X (p, q),
      FilteredComplexDecalagePageIsoProperty U p q r hr e := by
  let c := filteredComplexDecalageRepresentativeClass U p q r hr
  let m := filteredComplexDecalagePageEmbedding U p q r hr
  let α := Subobject.isoOfEqMk (imageSubobject c) m
    (filteredComplex_decalage_page_image U p q r hr)
  let b := factorThruImageSubobject c ≫ α.hom
  have hb : b ≫ m = c := by
    simp only [b, α, Category.assoc, Subobject.isoOfEqMk_hom,
      Subobject.ofLEMk_comp, imageSubobject_arrow_comp]
  obtain ⟨z, _, hze, _, hz, _⟩ :=
    U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
  have : Epi z := hze
  have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  have : Epi b := by dsimp [b]; infer_instance
  let a := z ≫ filteredComplexPageπ U.obj U.filtration r (p, q)
  have hk : kernelSubobject a = kernelSubobject b := by
    calc
      kernelSubobject a = kernelSubobject c :=
        filteredComplexDecalageRepresentative_kernels U p q r hr z hz
      _ = kernelSubobject (b ≫ m) := by congr 1; exact hb.symm
      _ = kernelSubobject b := kernelSubobject_comp_mono b m
  have hzero {X Y Y' : C} (f : X ⟶ Y) (g : X ⟶ Y')
      (h : kernelSubobject f ≤ kernelSubobject g) : kernel.ι f ≫ g = 0 := by
    calc
      kernel.ι f ≫ g = (kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow ≫ g := by
        simp
      _ = (kernelSubobjectIso f).inv ≫
          Subobject.ofLE (kernelSubobject f) (kernelSubobject g) h ≫
          (kernelSubobject g).arrow ≫ g := by
        simp only [← Category.assoc, Subobject.ofLE_arrow]
      _ = 0 := by simp only [kernelSubobject_arrow_comp, comp_zero]
  let u := Abelian.epiDesc a b (hzero a b hk.le)
  let v := Abelian.epiDesc b a (hzero b a hk.ge)
  have hu : a ≫ u = b := by simp [u]
  have hv : b ≫ v = a := by simp [v]
  let e : filteredComplexPageObject U.obj U.filtration r (p, q) ≅ _ :=
    { hom := u
      inv := v
      hom_inv_id := by
        apply (cancel_epi a).1
        simp [← Category.assoc, hu, hv]
      inv_hom_id := by
        apply (cancel_epi b).1
        simp [← Category.assoc, hu, hv] }
  have he : a ≫ e.hom = b := hu
  have hn : FilteredComplexDecalagePageIsoProperty U p q r hr e := by
    intro z' hz'
    have hzz : z' = z := (cancel_mono _).1 (hz'.trans hz.symm)
    subst z'
    change z ≫ filteredComplexPageπ U.obj U.filtration r (p, q) ≫ e.hom ≫ m = c
    simpa only [a, Category.assoc] using
      (congrArg (fun f ↦ f ≫ m) he).trans hb
  refine ⟨e, hn, ?_⟩
  intro e' he'
  exact filteredComplexDecalagePageIso_ext U p q r hr e' e he' hn

/-- The uniquely normalized isomorphism of individual page objects. -/
noncomputable def filteredComplexDecalagePageIso
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    filteredComplexPageObject U.obj U.filtration r (p, q) ≅
      ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
        r hr).X (p, q) :=
  (filteredComplex_decalage_page_iso U p q r hr).choose

/-- The chosen comparison sends each representative to its own interval class. -/
theorem filteredComplexDecalagePageIso_property
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    FilteredComplexDecalagePageIsoProperty U p q r hr
      (filteredComplexDecalagePageIso U p q r hr) :=
  (filteredComplex_decalage_page_iso U p q r hr).choose_spec.1

end CategoryTheory
