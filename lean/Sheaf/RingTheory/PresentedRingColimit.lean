/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Ring colimits specified by compatible maps

Source: Stacks 04AX, 090N, 01YW; the ring and affine-spectrum universal properties.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace Algebra.PresentedRingColimit
variable {I : Type u} [Preorder I]
variable (D : I → Type u) [∀ i, CommRing (D i)]
variable (tr : ∀ i j, i ≤ j → D i →+* D j)
variable (hid : ∀ i, tr i i le_rfl = RingHom.id _)
variable (hcomp : ∀ i j k (h : i ≤ j) (h' : j ≤ k),
  (tr j k h').comp (tr i j h) = tr i k (h.trans h'))

/-- The diagram associated with a coherent family of ring maps. -/
def diagram : I ⥤ CommRingCat.{u} where
  obj i := .of (D i)
  map h := CommRingCat.ofHom (tr _ _ (leOfHom h))
  map_id i := by exact congrArg CommRingCat.ofHom (hid i)
  map_comp f g := by
    exact congrArg CommRingCat.ofHom (hcomp _ _ _ (leOfHom f) (leOfHom g)).symm

variable (F : Type u) [CommRing F] (inc : ∀ i, D i →+* F)
variable (hinc : ∀ i j (h : i ≤ j), (inc j).comp (tr i j h) = inc i)

/-- The cocone given by the compatible inclusions. -/
def cocone : Cocone (diagram D tr hid hcomp) where
  pt := .of F
  ι := { app := fun i ↦ CommRingCat.ofHom (inc i)
         naturality := fun i j h ↦ by
           change CommRingCat.ofHom ((inc j).comp (tr i j (leOfHom h))) =
             CommRingCat.ofHom (inc i)
           exact congrArg CommRingCat.ofHom (hinc i j (leOfHom h)) }

variable (hcol : ∀ (Q : Type u) [CommRing Q] (a : ∀ i, D i →+* Q),
  (∀ i j (h : i ≤ j), (a j).comp (tr i j h) = a i) →
  ∃! g : F →+* Q, ∀ i, g.comp (inc i) = a i)

/-- A compatible-map universal property is a categorical colimit. -/
def isColimit : IsColimit (cocone D tr hid hcomp F inc hinc) := by
  apply IsColimit.ofExistsUnique
  intro c
  obtain ⟨g, hg, hgu⟩ := hcol c.pt (fun i ↦ (c.ι.app i).hom) (by
    intro i j h
    exact congrArg CommRingCat.Hom.hom (c.ι.naturality (homOfLE h)))
  refine ⟨CommRingCat.ofHom g, fun i ↦ ?_, fun k hk ↦ ?_⟩
  · exact congrArg CommRingCat.ofHom (hg i)
  · apply CommRingCat.hom_ext
    exact hgu k.hom (fun i ↦ congrArg CommRingCat.Hom.hom (hk i))

include hid hcomp hinc hcol in
/-- Filtered colimits of faithfully flat étale maps are faithfully flat and ind-étale. -/
theorem faithfullyFlat_indEtale [IsFiltered I]
    {R : Type u} [CommRing R] (base : ∀ i, R →+* D i) (full : R →+* F)
    (hb : ∀ i j (h : i ≤ j), (tr i j h).comp (base i) = base j)
    (hf : ∀ i, (inc i).comp (base i) = full)
    (hff : ∀ i, (base i).FaithfullyFlat) (het : ∀ i, (base i).Etale) :
    full.FaithfullyFlat ∧ full.IndEtale := by
  let B : (Functor.const I).obj (CommRingCat.of R) ⟶ diagram D tr hid hcomp :=
    { app := fun i ↦ CommRingCat.ofHom (base i)
      naturality := fun i j h ↦ by
        change CommRingCat.ofHom (base j) =
          CommRingCat.ofHom ((tr i j (leOfHom h)).comp (base i))
        exact (congrArg CommRingCat.ofHom (hb i j (leOfHom h))).symm }
  have hc := isColimit D tr hid hcomp F inc hinc hcol
  refine ⟨RingHom.FaithfullyFlat.of_isColimit (CommRingCat.ofHom full) I _
    (t := B) hc (fun i ↦ ⟨hff i, congrArg CommRingCat.ofHom (hf i)⟩), ?_⟩
  apply (RingHom.IndEtale.iff_exists (CommRingCat.ofHom full)).mpr
  exact ⟨I, inferInstance, inferInstance, diagram D tr hid hcomp, B,
    (cocone D tr hid hcomp F inc hinc).ι, hc,
    fun i ↦ ⟨het i, congrArg CommRingCat.ofHom (hf i)⟩⟩

include hid hcomp hinc hcol in
/-- Applying spectrum to the ring colimit gives its universal property for every scheme. -/
theorem scheme_existsUnique (Z : AlgebraicGeometry.Scheme.{u})
    (a : ∀ i, Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (D i)))
    (ha : ∀ i j (h : i ≤ j),
      a j ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (tr i j h)) = a i) :
    ∃! g : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of F),
      ∀ i, g ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (inc i)) = a i := by
  let c := cocone D tr hid hcomp F inc hinc
  have hc := isColimit D tr hid hcomp F inc hinc hcol
  have hl := isLimitOfPreserves AlgebraicGeometry.Scheme.Spec hc.op
  let s : Cone ((diagram D tr hid hcomp).op ⋙ AlgebraicGeometry.Scheme.Spec) :=
    { pt := Z
      π := { app := fun i ↦ a i.unop
             naturality := fun i j h ↦ by
               change a j.unop = a i.unop ≫ AlgebraicGeometry.Spec.map
                 (CommRingCat.ofHom (tr j.unop i.unop (leOfHom h.unop)))
               exact (ha j.unop i.unop (leOfHom h.unop)).symm } }
  obtain ⟨g, hg, hu⟩ := hl.existsUnique s
  refine ⟨g, fun i ↦ hg (op i), fun k hk ↦ hu k (fun i ↦ ?_)⟩
  exact hk i.unop

end Algebra.PresentedRingColimit
