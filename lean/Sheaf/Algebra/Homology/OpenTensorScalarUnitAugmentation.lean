/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Algebra.Homology.OpenTensorScalarUnitData
import Sheaf.Algebra.Homology.OpenTensorScalarUnitPairing
import Sheaf.Algebra.Homology.OpenTensorNormalizedComparison

/-! # Strict scalar-unit augmentation of the open total tensor

Source: Stacks Project, Tags 0E8I and 0GL1.
(blueprint: lem-sf-open-tensor-scalar-unit-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor SheafOfModules.SliceTensorGenerator
namespace SheafOfModules.OpenTensorAugmentation
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

private theorem pure_hom_ext
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{max c v r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (B : Sheaf K CommRingCat.{max c v r}) (M N H : Modules.{c, v, r} B)
    (a b : M ⊗ N ⟶ H)
    (h : ∀ W x y, a.val.app W (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} B M N W x y) =
      b.val.app W (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} B M N W x y)) : a = b := by
  let e := tensorObjIsoSheafification (R := B) M N
  apply (cancel_epi e.inv).mp
  apply (PresheafOfModules.sheafificationAdjunction
    (R := ring.{c, v, r} B) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  ext t
  change a.val.app W (e.inv.val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ring.{c, v, r} B).obj)).unit.app
        (M.val ⊗ N.val)).app W t)) =
    b.val.app W (e.inv.val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ring.{c, v, r} B).obj)).unit.app
        (M.val ⊗ N.val)).app W t))
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h W x y
  | add t u ht hu => simp only [map_add, ht, hu]

omit [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem unit_extensionSection
    (M : Modules.{max c v, v, r} (R.over V)) (W : Over V) (x : M.val.obj (op W)) :
    ((localizedSystemAdjunction.{c, v, r} R V).unit.app M).val.app (op W) x =
      extensionSection.{c, v, r} R V M W.left W.hom x := by
  exact (localizedSystemAdjunction_existsUnique.{c, v, r} R V).exists.choose_spec M (op W) x

omit [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem extension_map_section
    {M N : Modules.{max c v, v, r} (R.over V)} (a : M ⟶ N)
    (W : Over V) (x : M.val.obj (op W)) :
    ((localizedSystemExtension.{c, v, r} R V).map a).val.app (op W.left)
      (extensionSection.{c, v, r} R V M W.left W.hom x) =
      extensionSection.{c, v, r} R V N W.left W.hom (a.val.app (op W) x) := by
  have hn := congrArg (fun f ↦ f.val.app (op W) x)
    ((localizedSystemAdjunction.{c, v, r} R V).unit.naturality a)
  change ((localizedSystemAdjunction.{c, v, r} R V).unit.app N).val.app (op W)
      (a.val.app (op W) x) =
    ((localizedSystemExtension.{c, v, r} R V).map a).val.app (op W.left)
      (((localizedSystemAdjunction.{c, v, r} R V).unit.app M).val.app (op W) x) at hn
  simpa only [unit_extensionSection] using hn.symm

private theorem source_hom_ext
    (γ : source.{c, v, r} R V ≅ sliceSource.{c, v, r} R V ⋙
      ringedOpenExtensionOnComplexes.{c, v, r} R V)
    (hγ : ∀ (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
      (W : C) (f : W ⟶ V) (x : (Z.1.X p).val.obj (op (Over.mk f)))
      (y : (Z.2.X q).val.obj (op W)),
      ((γ.hom.app Z).f d).val.app (op W)
          (sourceSection.{c, v, r} R V Z p q d h W f x y) =
        extensionSection.{c, v, r} R V _ W f
          (sliceSourceSection.{c, v, r} R V Z p q d h (Over.mk f) x y))
    (Z : Inputs.{c, v, r} R V) (H : CochainComplex (Modules.{c, v, r} R) ℤ)
    (a b : (source.{c, v, r} R V).obj Z ⟶ H)
    (h : ∀ (p q d : ℤ) (hpq : p + q = d) (W : C) (f : W ⟶ V)
      (x : (Z.1.X p).val.obj (op (Over.mk f))) (y : (Z.2.X q).val.obj (op W)),
      (a.f d).val.app (op W) (sourceSection.{c, v, r} R V Z p q d hpq W f x y) =
        (b.f d).val.app (op W) (sourceSection.{c, v, r} R V Z p q d hpq W f x y)) :
    a = b := by
  apply HomologicalComplex.Hom.ext
  funext d
  let e := (HomologicalComplex.eval _ _ d).mapIso (γ.app Z)
  apply (cancel_epi e.inv).mp
  apply (localizedSystemAdjunction.{c, v, r} R V).homEquiv _ (H.X d) |>.injective
  let : (ringedOpenTensor.{max c v, v, r} (R.over V)).PreservesZeroMorphisms :=
    ringedOpenTensorZero.{max c v, v, r} (R.over V)
  let : ∀ M, ((ringedOpenTensor.{max c v, v, r} (R.over V)).obj M).PreservesZeroMorphisms :=
    ringedOpenTensorObjZero.{max c v, v, r} (R.over V)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply pure_hom_ext.{max c v, v, r} (R.over V) (Z.1.X p)
    (Z.2.X q |>.over V) ((H.X d).over V)
  intro W x y
  change (a.f d).val.app (op W.unop.left)
      ((γ.inv.app Z).f d |>.val.app (op W.unop.left) <|
        ((localizedSystemAdjunction.{c, v, r} R V).unit.app _).val.app W
          (sliceSourceSection.{c, v, r} R V Z p q d hpq W.unop x y)) =
    (b.f d).val.app (op W.unop.left)
      ((γ.inv.app Z).f d |>.val.app (op W.unop.left) <|
        ((localizedSystemAdjunction.{c, v, r} R V).unit.app _).val.app W
          (sliceSourceSection.{c, v, r} R V Z p q d hpq W.unop x y))
  rw [unit_extensionSection]
  have hi : ((γ.inv.app Z).f d).val.app (op W.unop.left)
      (extensionSection.{c, v, r} R V _ W.unop.left W.unop.hom
        (sliceSourceSection.{c, v, r} R V Z p q d hpq W.unop x y)) =
      sourceSection.{c, v, r} R V Z p q d hpq W.unop.left W.unop.hom x y := by
    erw [← hγ Z p q d hpq W.unop.left W.unop.hom x y]
    exact congrArg (fun f ↦ (f.f d).val.app (op W.unop.left)
      (sourceSection.{c, v, r} R V Z p q d hpq W.unop.left W.unop.hom x y))
        (γ.app Z).hom_inv_id
  rw [hi]
  exact h p q d hpq W.unop.left W.unop.hom x y

/-- Generator-normalized strict total tensors and their scalar-unit augmentations exist
for every unital commutative algebra tower and every pair of unbounded complexes.
Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Cohomology on Sites, Tag 0GL1; agent strict scalar-unit refinement
(blueprint: lem-sf-open-tensor-scalar-unit-augmentation).

Proof: choose the strict scalar-unit pairing and the normalized ordinary and
coefficient comparisons independently. To test equality of maps out of the source,
transport along gammaBase inverse and use the extension/restriction adjunction.
Maps from a total sum are determined on its homogeneous summands; maps from a
sheaf tensor are determined on the presheaf pure tensors by the sheafification
adjunction and tensor induction. The normalization of gammaBase and its inverse
identity turn these tests into the original extension generators.

On each such generator the upper route first inserts the two scalar units and
then applies gamma's formula. The lower route applies gammaBase's formula,
then functorial extension of cS; naturality of the extension adjunction unit
identifies this with extension of cS's generator formula. Thus the values agree.
Extensionality in the input complexes and the tower index proves the square.
The common value is the upper-route computation. Applying any localization
functor to the square gives its localized equality. -/
theorem augmentation_exists (A : AlgebraTowers.{c, v, r} R) :
    Nonempty (Augmentation.{c, v, r} R V A) := by
  obtain ⟨u⟩ := scalarUnits_exists.{c, v, r} R V A
  obtain ⟨g⟩ := normalizedComparison_exists.{c, v, r} R V A u.totals
  have hsquare : u.cT ≫ g.gamma.hom =
      lowerRoute.{c, v, r} R V u.totals g.gammaBase u.cS := by
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext Z
    apply source_hom_ext.{c, v, r} R V g.gammaBase g.base_generator Z
    intro p q d h W f x y
    change (((g.gamma.hom.app n).app Z).f d).val.app (op W)
        ((((u.cT.app n).app Z).f d).val.app (op W)
          (sourceSection.{c, v, r} R V Z p q d h W f x y)) = _
    rw [u.cT_generator, g.gamma_generator]
    change _ =
      (((ringedOpenExtensionOnComplexes.{c, v, r} R V).map
        ((u.cS.app n).app Z)).f d).val.app (op W)
          (((g.gammaBase.hom.app Z).f d).val.app (op W)
            (sourceSection.{c, v, r} R V Z p q d h W f x y))
    rw [g.base_generator]
    change _ =
      ((localizedSystemExtension.{c, v, r} R V).map
        (((u.cS.app n).app Z).f d)).val.app (op W) _
    erw [extension_map_section.{c, v, r} R V (((u.cS.app n).app Z).f d) (Over.mk f)
      (sliceSourceSection.{c, v, r} R V Z p q d h (Over.mk f) x y), u.cS_generator]
    rfl
  refine ⟨{ totals := u.totals
            gammaBase := g.gammaBase
            base_generator := g.base_generator
            gamma := g.gamma
            gamma_generator := g.gamma_generator
            cT := u.cT
            cT_generator := u.cT_generator
            cS := u.cS
            cS_generator := u.cS_generator
            square := hsquare
            common_value := ?_
            localized_square := ?_ }⟩
  · intro n Z p q d h W f x y
    change (((g.gamma.hom.app n).app Z).f d).val.app (op W)
      ((((u.cT.app n).app Z).f d).val.app (op W)
        (sourceSection.{c, v, r} R V Z p q d h W f x y)) = _
    rw [u.cT_generator, g.gamma_generator]
  · intro Z W
    rw [hsquare]

end SheafOfModules.OpenTensorAugmentation
