/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import all Sheaf.SecSmoothPurity.TensorPullbackSquare
import all Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! Scalar restriction and the ordinary ringed inverse-image square.
Source: Stacks Project, Tags 03D7, 03D8 and 0D6D.
(blueprint: lem-weil-pbc-ring-restriction-pullback-square) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients exchangeModuleComposition

section
variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW SW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aW : RW ⟶ SW) (aZ : RZ ⟶ SZ)
    (ckR : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (chR : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (ckS : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj SV ≅ SW)
    (chS : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj SW ≅ SZ)
    (hk : ckR.hom ≫ aW = (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map aV ≫ ckS.hom)
    (hh : chR.hom ≫ aZ = (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map aW ≫ chS.hom)

include hk hh in
private theorem restrictionComposite_comm :
    (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR).hom ≫ aZ =
      (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).map aV ≫
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS).hom := by
  simp only [proEtaleRingCompositeCoefficients, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [hh, ← Functor.map_comp_assoc, hk, Functor.map_comp]
  simp only [Category.assoc, Iso.app_hom]
  rw [← reassoc_of% ((proEtaleRingInverseImageComp h k).hom.naturality aV)]




private def restrictionRComp
    (T0 : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (T1 : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (T2 : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c1 : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj T0 ≅ T1)
    (c2 : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj T1 ≅ T2) :=
  conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction k T0 T1 c1).comp
      (proEtaleRingModuleAdjunction h T1 T2 c2))
    (proEtaleRingModuleAdjunction (h ≫ k) T0 T2
      (proEtaleRingCompositeCoefficients h k T0 T1 T2 c1 c2))
    (exchangeModuleComposition h k T0 T1 T2 c1 c2)

private theorem restrictionRComp_apply
    (T0 : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (T1 : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (T2 : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c1 : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj T0 ≅ T1)
    (c2 : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj T1 ≅ T2)
    (N : proEtaleRingModules Z T2) (U : V.ProEt)
    (m : ((proEtaleRingModuleDirectImage h T1 T2 c2 ⋙
      proEtaleRingModuleDirectImage k T0 T1 c1).obj N).val.obj (op U)) :
    ((restrictionRComp h k T0 T1 T2 c1 c2).hom.app N).val.app (op U) m =
      N.val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m :=
  by
    simpa only [restrictionRComp, exchangeModuleComposition] using
      (exchangeModuleComposition_existsUnique h k T0 T1 T2 c1 c2).choose_spec.1 N U m

private theorem restrictionDirect_apply
    {U T : Scheme.{u}} (f : U ⟶ T)
    (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (R' S' : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (a : R ⟶ S) (b : R' ⟶ S')
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R')
    (c' : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj S ≅ S')
    (hc : c.hom ≫ b = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a ≫ c'.hom)
    (N : proEtaleRingModules U S') (Y : T.ProEtᵒᵖ)
    (n : N.val.obj ((proEtaleBaseChange f).op.obj Y)) :
    ((proEtaleRingRestrictionDirectImage f R S R' S' a b c c' hc).hom.app N).val.app Y n = n :=
  (proEtaleRingRestrictionDirectImage_existsUnique f R S R' S' a b c c' hc).choose_spec.1 N Y n

private theorem restrictionComparison_comp
    (M : proEtaleRingModules V SV) :
    (exchangeModuleComposition h k RV RW RZ ckR chR).hom.app
        ((proEtaleRingRestrictScalars aV).obj M) ≫
      (proEtaleRingModulePullback h RW RZ chR).map
        ((proEtaleRingRestrictionPullbackInv k RV SV RW SW aV aW ckR ckS hk).app M) ≫
      (proEtaleRingRestrictionPullbackInv h RW SW RZ SZ aW aZ chR chS hh).app
        ((proEtaleRingModulePullback k SV SW ckS).obj M) =
    (proEtaleRingRestrictionPullbackInv (h ≫ k) RV SV RZ SZ aV aZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
        (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh)).app M ≫
      (proEtaleRingRestrictScalars aZ).map
        ((exchangeModuleComposition h k SV SW SZ ckS chS).hom.app M) := by
  let q := (TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv k RV SV RW SW aV aW ckR ckS hk)).vComp
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv h RW SW RZ SZ aW aZ chR chS hh))
  let r := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv (h ≫ k) RV SV RZ SZ aV aZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
      (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
      (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh))
  have hc : q.whiskerRight (exchangeModuleComposition h k RV RW RZ ckR chR).hom =
      r.whiskerLeft (exchangeModuleComposition h k SV SW SZ ckS chS).hom := by
    apply AlgebraicGeometry.ProEtale.mateSquare
      ((proEtaleRingModuleAdjunction k SV SW ckS).comp
        (proEtaleRingModuleAdjunction h SW SZ chS))
      (proEtaleRingModuleAdjunction (h ≫ k) SV SZ
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS))
      ((proEtaleRingModuleAdjunction k RV RW ckR).comp
        (proEtaleRingModuleAdjunction h RW RZ chR))
      (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR))
    dsimp only [q]
    rw [mateEquiv_hcomp]
    have hk' := restrictionPullback_mate k RV SV RW SW aV aW ckR ckS hk
    have hh' := restrictionPullback_mate h RW SW RZ SZ aW aZ chR chS hh
    have hc' := restrictionPullback_mate (h ≫ k) RV SV RZ SZ aV aZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
      (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
      (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh)
    change _ = _ at hk' hh' hc'
    have hkq : mateEquiv (proEtaleRingModuleAdjunction k SV SW ckS)
        (proEtaleRingModuleAdjunction k RV RW ckR)
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv k RV SV RW SW aV aW ckR ckS hk)) =
        TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage k RV SV RW SW aV aW ckR ckS hk).hom := by
      apply TwoSquare.ext
      intro N
      exact congrArg (fun z ↦ z.app N) hk'
    have hhq : mateEquiv (proEtaleRingModuleAdjunction h SW SZ chS)
        (proEtaleRingModuleAdjunction h RW RZ chR)
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv h RW SW RZ SZ aW aZ chR chS hh)) =
        TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage h RW SW RZ SZ aW aZ chR chS hh).hom := by
      apply TwoSquare.ext
      intro N
      exact congrArg (fun z ↦ z.app N) hh'
    have hcq : mateEquiv
        (proEtaleRingModuleAdjunction (h ≫ k) SV SZ
          (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS))
        (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
          (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR))
        r = TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage (h ≫ k) RV SV RZ SZ aV aZ
            (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
            (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
            (restrictionComposite_comm h k RV SV RW SW RZ SZ
              aV aW aZ ckR chR ckS chS hk hh)).hom := by
      apply TwoSquare.ext
      intro N
      exact congrArg (fun z ↦ z.app N) hc'
    rw [hkq, hhq, hcq]
    change ((TwoSquare.mk _ _ _ _ _).hComp (TwoSquare.mk _ _ _ _ _)).whiskerBottom
        (restrictionRComp h k RV RW RZ ckR chR).hom =
      (TwoSquare.mk _ _ _ _ _).whiskerTop (restrictionRComp h k SV SW SZ ckS chS).hom
    apply TwoSquare.ext
    intro N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app]
    simp only [ModuleCat.comp_apply, TwoSquare.natTrans]
    erw [restrictionDirect_apply k RV SV RW SW aV aW ckR ckS hk _ Y n]
    change ((restrictionRComp h k RV RW RZ ckR chR).hom.app
        ((proEtaleRingRestrictScalars aZ).obj N)).val.app Y
        (((proEtaleRingRestrictionDirectImage h RW SW RZ SZ aW aZ chR chS hh).hom.app
          N).val.app ((proEtaleBaseChange k).op.obj Y) n) =
      ((proEtaleRingRestrictionDirectImage (h ≫ k) RV SV RZ SZ aV aZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
        (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh)).hom.app
          N).val.app Y (((restrictionRComp h k SV SW SZ ckS chS).hom.app N).val.app Y n)
    erw [restrictionDirect_apply h RW SW RZ SZ aW aZ chR chS hh N _ n,
      restrictionDirect_apply (h ≫ k) RV SV RZ SZ aV aZ _ _ _ N Y _]
    obtain ⟨Y⟩ := Y
    erw [restrictionRComp_apply h k RV RW RZ ckR chR
        ((proEtaleRingRestrictScalars aZ).obj N) Y n,
      restrictionRComp_apply h k SV SW SZ ckS chS N Y n]
    rfl
  have hm := congrArg (fun z ↦ z.app M) hc
  simpa only [q, r, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hm
end

private theorem compatible_sigma_eq {ι : Type*} {B C : ι → Type*}
    (P : ∀ i, B i → C i → Prop) {i j : ι}
    {b : B i} {b' : B j} {c : C i} {c' : C j}
    (h : i = j) (hb : HEq b b') (hc : HEq c c')
    (p : P i b c) (q : P j b' c') :
    (⟨i, ⟨(b, c), p⟩⟩ : Σ k, {v : B k × C k // P k v.1 v.2}) =
      ⟨j, ⟨(b', c'), q⟩⟩ := by
  subst j
  cases hb
  cases hc
  rfl

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- Restriction of compatible coefficient systems respects the normalized ordinary
pullback-square compositor. This involves neither derived functors nor exchange mates.
Source: Stacks Project, Tags 03D7, 03D8 and 0D6D
(blueprint: lem-weil-pbc-ring-restriction-pullback-square).

Proof: take right-adjoint mates of the restriction/pullback comparisons along each
of the two composable paths. The ordinary restriction/direct-image comparisons are
identity on all sections. The right-adjoint conjugate of exchangeModuleComposition
is restriction along Over.pullbackComp, by its normalization. Restriction of scalars
changes neither sections nor these restriction maps. Consequently the two composites
involving direct-image composition and scalar restriction agree on every section.
The mate-pasting laws and injectivity of the mate bijections give compatibility with
each inverse-image compositor. Paste the two resulting equations across the equality
of the coefficient-decorated composite scheme morphisms supplied by the two coherent
ringed squares. Equality transport is natural in the scalar map; its proof components
agree by proof irrelevance. Cancel the first compositor to obtain the displayed
square. The argument applies to arbitrary coefficients, zero rings and empty schemes. -/
theorem proEtaleRingRestriction_square
    (r s : StrictTowerRingedSquare sq)
    (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
    (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
    (hf : r.cf.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aY ≫ s.cf.hom)
    (hg : r.cg.hom ≫ aY' =
      (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ s.cg.hom)
    (hg' : r.cg'.hom ≫ aX' =
      (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).map aX ≫ s.cg'.hom)
    (hf' : r.cf'.hom ≫ aX' =
      (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).map aY' ≫ s.cf'.hom)
    (M : proEtaleRingModules Y s.RY) :
    r.exchangeModuleSquare.hom.app ((proEtaleRingRestrictScalars aY).obj M) ≫
      (proEtaleRingModulePullback g' r.RX r.RX' r.cg').map
        ((proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
          aY aX r.cf s.cf hf).app M) ≫
      (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
        aX aX' r.cg' s.cg' hg').app
        ((proEtaleRingModulePullback f s.RY s.RX s.cf).obj M) =
    (proEtaleRingModulePullback f' r.RY' r.RX' r.cf').map
        ((proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
          aY aY' r.cg s.cg hg).app M) ≫
      (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
        aY' aX' r.cf' s.cf' hf').app
        ((proEtaleRingModulePullback g s.RY s.RY' s.cg).obj M) ≫
      (proEtaleRingRestrictScalars aX').map (s.exchangeModuleSquare.hom.app M) := by
  let B (u : X' ⟶ Y) :=
    (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj r.RY ≅ r.RX'
  let C (u : X' ⟶ Y) :=
    (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj s.RY ≅ s.RX'
  let compatible (u : X' ⟶ Y) (b : B u) (c : C u) :=
    b.hom ≫ aX' = (proEtaleSheafInverseImage u CommRingCat.{t + 1}).map aY ≫ c.hom
  let E := Σ u : X' ⟶ Y, {v : B u × C u // compatible u v.1 v.2}
  let left : E := ⟨f' ≫ g, ⟨
    (proEtaleRingCompositeCoefficients f' g r.RY r.RY' r.RX' r.cg r.cf',
     proEtaleRingCompositeCoefficients f' g s.RY s.RY' s.RX' s.cg s.cf'),
    restrictionComposite_comm f' g r.RY s.RY r.RY' s.RY' r.RX' s.RX'
      aY aY' aX' r.cg r.cf' s.cg s.cf' hg hf'⟩⟩
  let right : E := ⟨g' ≫ f, ⟨
    (proEtaleRingCompositeCoefficients g' f r.RY r.RX r.RX' r.cf r.cg',
     proEtaleRingCompositeCoefficients g' f s.RY s.RX s.RX' s.cf s.cg'),
    restrictionComposite_comm g' f r.RY s.RY r.RX s.RX r.RX' s.RX'
      aY aX aX' r.cf r.cg' s.cf s.cg' hf hg'⟩⟩
  have h : left = right :=
    compatible_sigma_eq compatible sq.w.symm r.coherent.symm s.coherent.symm _ _
  let P (z : E) := proEtaleRingModulePullback z.1 r.RY r.RX' z.2.1.1
  let Q (z : E) := proEtaleRingModulePullback z.1 s.RY s.RX' z.2.1.2
  let q (z : E) := proEtaleRingRestrictionPullbackInv z.1 r.RY s.RY r.RX' s.RX'
    aY aX' z.2.1.1 z.2.1.2 z.2.2
  have hz : r.exchangeModuleSquare.symm =
      (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg').symm ≪≫
        eqToIso (congrArg P h.symm) ≪≫
        exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf' := by
    have he : congrArg P h.symm = congrArg
        (fun z : (Σ u : X' ⟶ Y, B u) ↦
          proEtaleRingModulePullback z.1 r.RY r.RX' z.2)
        r.exchangeCoefficients_eq.symm := rfl
    rw [he]
    apply Iso.ext
    simp only [StrictTowerRingedSquare.exchangeModuleSquare, Iso.symm_hom,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, eqToIso.inv, eqToIso.hom]
  have hw : s.exchangeModuleSquare.symm =
      (exchangeModuleComposition g' f s.RY s.RX s.RX' s.cf s.cg').symm ≪≫
        eqToIso (congrArg Q h.symm) ≪≫
        exchangeModuleComposition f' g s.RY s.RY' s.RX' s.cg s.cf' := by
    have he : congrArg Q h.symm = congrArg
        (fun z : (Σ u : X' ⟶ Y, C u) ↦
          proEtaleRingModulePullback z.1 s.RY s.RX' z.2)
        s.exchangeCoefficients_eq.symm := rfl
    rw [he]
    apply Iso.ext
    simp only [StrictTowerRingedSquare.exchangeModuleSquare, Iso.symm_hom,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, eqToIso.inv, eqToIso.hom]
  exact AlgebraicGeometry.ProEtale.pasteTransport P Q
    (proEtaleRingRestrictScalars aY) (proEtaleRingRestrictScalars aX') q h
    (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf')
    (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg')
    (exchangeModuleComposition f' g s.RY s.RY' s.RX' s.cg s.cf')
    (exchangeModuleComposition g' f s.RY s.RX s.RX' s.cf s.cg')
    (Functor.whiskerRight
      (proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
        aY aY' r.cg s.cg hg)
      (proEtaleRingModulePullback f' r.RY' r.RX' r.cf'))
    (Functor.whiskerLeft (proEtaleRingModulePullback g s.RY s.RY' s.cg)
      (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
        aY' aX' r.cf' s.cf' hf'))
    (Functor.whiskerRight
      (proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
        aY aX r.cf s.cf hf)
      (proEtaleRingModulePullback g' r.RX r.RX' r.cg'))
    (Functor.whiskerLeft (proEtaleRingModulePullback f s.RY s.RX s.cf)
      (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
        aX aX' r.cg' s.cg' hg'))
    (restrictionComparison_comp f' g r.RY s.RY r.RY' s.RY' r.RX' s.RX'
      aY aY' aX' r.cg r.cf' s.cg s.cf' hg hf')
    (restrictionComparison_comp g' f r.RY s.RY r.RX s.RX r.RX' s.RX'
      aY aX aX' r.cf r.cg' s.cf s.cg' hf hg')
    r.exchangeModuleSquare.symm s.exchangeModuleSquare.symm hz hw M

private def termwiseSquareHom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    (q : F ⋙ G ⟶ H ⋙ I) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ⟶
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj I where
  app M := Functor.whiskerLeft M q
  naturality {M N} a := by
    apply NatTrans.ext
    funext n
    exact q.naturality (a.app n)

private def termwiseSquareIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    (e : F ⋙ G ≅ H ⋙ I) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj I where
  hom := termwiseSquareHom e.hom
  inv := termwiseSquareHom e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    exact e.hom_inv_id_app (M.obj n)
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    exact e.inv_hom_id_app (M.obj n)

private theorem towerCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ N, c.app (R₀.obj N) ≫ I.map (qG.app N) ≫ qI.app (G'.obj N) =
      H.map (qJ.app N) ≫ qH.app (J'.obj N) ≫ R₃.map (d.app N)) :
    Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ _ _).obj R₀)
        (termwiseSquareHom c) ≫
      Functor.whiskerRight (termwiseSquareHom qG)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj I) ≫
      Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G')
        (termwiseSquareHom qI) =
    Functor.whiskerRight (termwiseSquareHom qJ)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj H) ≫
      Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J')
        (termwiseSquareHom qH) ≫
      Functor.whiskerRight (termwiseSquareHom d)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj R₃) := by
  apply NatTrans.ext
  funext N
  apply NatTrans.ext
  funext n
  exact hc (N.obj n)

-- Inferred proposition keeps the normalized termwise interfaces shared.
set_option linter.defProp false in
private def restrictionTowerCube_nat
    (r s : StrictTowerRingedSquare sq)
    (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
    (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
    (hf : r.cf.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aY ≫ s.cf.hom)
    (hg : r.cg.hom ≫ aY' =
      (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ s.cg.hom)
    (hg' : r.cg'.hom ≫ aX' =
      (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).map aX ≫ s.cg'.hom)
    (hf' : r.cf'.hom ≫ aX' =
      (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).map aY' ≫ s.cf'.hom) :=
  towerCube
    (C₀ := proEtaleRingModules Y r.RY)
    (C₁ := proEtaleRingModules Y' r.RY')
    (C₂ := proEtaleRingModules X r.RX)
    (C₃ := proEtaleRingModules X' r.RX')
    (D₀ := proEtaleRingModules Y s.RY)
    (D₁ := proEtaleRingModules Y' s.RY')
    (D₂ := proEtaleRingModules X s.RX)
    (D₃ := proEtaleRingModules X' s.RX')
    (R₀ := proEtaleRingRestrictScalars aY)
    (R₁ := proEtaleRingRestrictScalars aY')
    (R₂ := proEtaleRingRestrictScalars aX)
    (R₃ := proEtaleRingRestrictScalars aX')
    (J := proEtaleRingModulePullback g r.RY r.RY' r.cg)
    (H := proEtaleRingModulePullback f' r.RY' r.RX' r.cf')
    (G := proEtaleRingModulePullback f r.RY r.RX r.cf)
    (I := proEtaleRingModulePullback g' r.RX r.RX' r.cg')
    (J' := proEtaleRingModulePullback g s.RY s.RY' s.cg)
    (H' := proEtaleRingModulePullback f' s.RY' s.RX' s.cf')
    (G' := proEtaleRingModulePullback f s.RY s.RX s.cf)
    (I' := proEtaleRingModulePullback g' s.RX s.RX' s.cg')
    (proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
      aY aY' r.cg s.cg hg)
    (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
      aY' aX' r.cf' s.cf' hf')
    (proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
      aY aX r.cf s.cf hf)
    (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
      aX aX' r.cg' s.cg' hg')
    r.exchangeModuleSquare.hom s.exchangeModuleSquare.hom
    (proEtaleRingRestriction_square r s aY aX aY' aX' hf hg hg' hf')

private instance termwise_preservesFiniteLimits
    {C D : Type*} [Category C] [Category D] [HasFiniteLimits C]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) :=
  ⟨fun J _ _ ↦ whiskeringRight_preservesLimitsOfShape (C := ℕᵒᵖ) (J := J) F⟩

private instance termwise_preservesFiniteColimits
    {C D : Type*} [Category C] [Category D] [HasFiniteColimits C]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) :=
  ⟨fun J _ _ ↦ whiskeringRight_preservesColimitsOfShape (C := ℕᵒᵖ) (J := J) F⟩

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem localizeTowerSquare_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      (F₂ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G)
      (G₁ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj H)
      (G₂ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj I)
      (termwiseSquareIso e) =
    (Functor.mapDerivedCategoryCompIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G)
      (G := (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj I)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e) ≪≫
    Functor.mapDerivedCategoryCompIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj H)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj I) := rfl

private theorem towerSquare_localization (r : StrictTowerRingedSquare sq) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := exchangeTowerModulePull g r.RY r.RY' r.cg)
      (F₂ := exchangeTowerModulePull f' r.RY' r.RX' r.cf')
      (G₁ := exchangeTowerModulePull f r.RY r.RX r.cf)
      (G₂ := exchangeTowerModulePull g' r.RX r.RX' r.cg')
        (termwiseSquareIso r.exchangeModuleSquare) =
      r.exchangeTowerSquare := by
  exact localizeTowerSquare_eq
    (F := proEtaleRingModulePullback g r.RY r.RY' r.cg)
    (G := proEtaleRingModulePullback f' r.RY' r.RX' r.cf')
    (H := proEtaleRingModulePullback f r.RY r.RX r.cf)
    (I := proEtaleRingModulePullback g' r.RX r.RX' r.cg') r.exchangeModuleSquare

private theorem derivedCube_nat
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : Functor.whiskerLeft R₀ c.hom ≫ Functor.whiskerRight qG.hom I ≫
        Functor.whiskerLeft G' qI.hom =
      Functor.whiskerRight qJ.hom H ≫ Functor.whiskerLeft J' qH.hom ≫
        Functor.whiskerRight d.hom R₃) :
    Functor.whiskerLeft R₀.mapDerivedCategory (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qI).hom =
    Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom R₃.mapDerivedCategory := by
  apply NatTrans.ext
  funext M
  exact AlgebraicGeometry.ProEtale.derivedCube qJ qH qG qI c d
    (fun N ↦ congrArg (fun z ↦ z.app N) hc) M


end AlgebraicGeometry.Scheme
