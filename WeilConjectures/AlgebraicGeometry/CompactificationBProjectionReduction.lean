/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationBProjectionData
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.CompactificationBProjectionDomains
import WeilConjectures.AlgebraicGeometry.CompactificationBOrdinaryProjectionSquare

/-! # Compactification projection and the pinned reconstruction comparison

Source: current blueprint, integral-adjunction-direct-image.proof.md (1)--(3)
and tower-geometric-gamma.proof.md (2)
(blueprint: lem-pur-compactification-b-projection-reduction).

The unchanged projection coordinates are publicly re-exported from the data module.
The proof combines the bounded-domain and ordinary-square steps by naturality of
reconstruction, completion-unit conjugation, and cancellation of inverse maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CompactificationBProjection
open CompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (m : DescentModels l E)

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  Functor.mapDerivedCategory SheafOfModules.changeOfRings SheafOfModules.monoidalCategory
  reduction totalLimit derivedTowerEquivalence towerEquivalence
  integralCompletedTensor integralDerivedPullback

private def transposeNaturalTransformation
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : A ⥤ C) (R : B ⥤ C) (L : C ⥤ B)
    (a : R ⊣ L) (t : F ⋙ R ⟶ G) : F ⟶ G ⋙ L where
  app X := a.homEquiv _ _ (t.app X)
  naturality _X _Y f :=
    a.homEquiv_naturality_left_square (F.map f) _ _ (G.map f) (t.naturality f)

private def reconstructionNaturalTransformation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y)) :
    integralImage l E c ⋙ red l E m Y ⟶ red l E m X ⋙ systemImage l E c := by
  let o := transposeNaturalTransformation
    (lim l E m X AX ⋙ ringedOpen l E c.i)
    (VaryingRing.J (rings l E) (transitions l E) c.i)
    (red l E m c.Z) (lim l E m c.Z AZ) (adj l E m c.Z AZ)
    (Functor.whiskerLeft (lim l E m X AX) (m.openScalar c.i).hom ≫
      Functor.whiskerRight (adj l E m X AX).counit
        (VaryingRing.J (rings l E) (transitions l E) c.i))
  let p := transposeNaturalTransformation
    (lim l E m c.Z AZ ⋙ ringedPush l E c.g)
    (VaryingRing.P (rings l E) (transitions l E) c.g)
    (red l E m Y) (lim l E m Y AY) (adj l E m Y AY)
    (Functor.whiskerLeft (lim l E m c.Z AZ) (properScalar l E m c.g) ≫
      Functor.whiskerRight (adj l E m c.Z AZ).counit
        (VaryingRing.P (rings l E) (transitions l E) c.g))
  let t : integralImage l E c ⟶ red l E m X ⋙ systemImage l E c ⋙ lim l E m Y AY :=
    Functor.whiskerRight (adj l E m X AX).unit (integralImage l E c) ≫
      Functor.whiskerRight (Functor.whiskerLeft (red l E m X) o) (ringedPush l E c.g) ≫
      Functor.whiskerLeft
        (red l E m X ⋙ VaryingRing.J (rings l E) (transitions l E) c.i) p
  exact Functor.whiskerRight t (red l E m Y) ≫
    Functor.whiskerLeft (red l E m X ⋙ systemImage l E c) (adj l E m Y AY).counit

private theorem reconstruction_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    {N N' : CompleteProjectionDescent.Integral l E X} (t : N ⟶ N') :
    (red l E m Y).map ((integralImage l E c).map t) ≫
        reconstruction l E m c AX AZ AY N' =
      reconstruction l E m c AX AZ AY N ≫
        (systemImage l E c).map ((red l E m X).map t) := by
  exact (reconstructionNaturalTransformation l E m c AX AZ AY).naturality t

private theorem innerUnit_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' : CompleteProjectionDescent.Integral l E Y}
    {M M' : CompleteProjectionDescent.Integral l E X} (a : K ⟶ K') (b : M ⟶ M') :
    (m.integral.tensor X).ordinary.tensor.map
        (Prod.mkHom ((ringedPull l E f).map a) b) ≫ innerUnit l E m f K' M' =
      innerUnit l E m f K M ≫ (integralCompletedTensor l E X).map
        (Prod.mkHom ((integralDerivedPullback l E f).map a) b) := by
  let t := Functor.whiskerLeft ((ringedPull l E f).prod (𝟭 _))
      ((m.integral.tensor X).chi l E) ≫
    Functor.whiskerRight
      (NatTrans.prod ((m.integral.pull f).unit l E) (𝟙 (𝟭 _)))
      (integralCompletedTensor l E X)
  exact t.naturality (Prod.mkHom a b)

private theorem conjugate_square
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (R : C ⥤ D) (R' : C' ⥤ D') (P : C' ⥤ C) (F : D' ⥤ D)
    {A : C} {B B' : C'} {S : D} {T : D'} (a : A ⟶ P.obj B) (h : B ≅ B')
    (b : R.obj (P.obj B) ⟶ F.obj (R'.obj B))
    (b' : R.obj (P.obj B') ⟶ F.obj (R'.obj B'))
    (q : R'.obj B ⟶ T) (s : R.obj A ⟶ S) (theta : S ⟶ F.obj T)
    (hn : R.map (P.map h.hom) ≫ b' = b ≫ F.map (R'.map h.hom))
    (hs : R.map a ≫ b ≫ F.map q = s ≫ theta) :
    R.map (a ≫ P.map h.hom) ≫ b' ≫ F.map (R'.map h.inv ≫ q) = s ≫ theta := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (R.map (P.map h.hom)) b', hn]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (R'.map h.hom)) (F.map (R'.map h.inv)) (F.map q),
    ← F.map_comp, ← R'.map_comp, h.hom_inv_id, R'.map_id, F.map_id, Category.id_comp]
  exact hs

private theorem inverse_square
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A B : C} {S T : D} (a : A ⟶ B) (b : R.obj B ⟶ T)
    (s : R.obj A ⟶ S) (theta : S ⟶ T) [IsIso a] [IsIso theta]
    (hs : R.map a ≫ b = s ≫ theta) : R.map (inv a) ≫ s = b ≫ inv theta := by
  apply (cancel_mono theta).1
  rw [Category.assoc, ← hs, ← Category.assoc, ← R.map_comp, IsIso.inv_hom_id,
    R.map_id, Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The completed projection respects the specified reconstruction comparison b.
Source: current blueprint, integral-adjunction-direct-image.proof.md (1)--(3),
and tower-geometric-gamma.proof.md (2)
(blueprint: lem-pur-compactification-b-projection-reduction).

Proof:
1. Ordinary pullback and tensor preserve complete constructible objects by
   det-lem-int-tensor-pullback and det-lem-int-tensor-product. Compact support
   does so by det-sp-integral-direct-image-tower. Pullback preserves the Tor
   interval, tensor adds intervals, and compact support widens it by 2d, using
   lem-sf-pullback-tor-amplitude and lem-sf-tensor-ctf. Apply normalized equivalence.
2. The quotient augmentation and the tensor balancing of
   lem-sp-reduction-derived-monoidal-tower identify ordinary tensors with completed
   ones. Their completion-unit isomorphisms are h and v below. Reducing their
   inverses gives exactly q and the tensor part of s, by the actual triangle identity.
3. The proper factor is the mate of counit tensor identity; the open factor's
   inverse is the adjunct of open unit tensor identity, by
   lem-sf-open-tensor-normalization. The canonical pullback compositor of
   lem-sfb-ringed-derived-monoidal-comparisons identifies these with the completed
   projection factors. Extension by zero preserves completeness by
   det-lem-int-tensor-shriek.
4. Quasi-compactness of j follows from
   lemma-nagata-open-immersion-qc-over-separated-target. Apply
   lem-sp-complete-compactification-limit-realization. Its canonical comparison
   followed by the reconstruction counit is precisely reconstruction, hence the
   b pinned in lem-sp-integral-reconstruction-comparisons, not a levelwise choice.
5. lem-sp-tower-compact-support-projection-formula makes the open factor invertible.
   Apply lem-sp-complete-projection-mate-descent to the common-bounded inputs of
   Step 1. Reducing its unit-conjugation formula and using counit naturality gives
   the projection square in the ordinary tensor order, before finite evaluation.
6. Interchange both tensor factors. On bidegree (a,b) both paths have sign
   (-1)^(ab); the degree-zero quotient scalar moves across the balanced tensor.
   Thus the reduction tensor comparison commutes with the canonical symmetries.
   lem-pur-completed-operation-tower-substitution identifies the completed symmetry
   with this same system symmetry. Naturality of the pinned b moves P of symmetry
   through b. The square is the displayed equality with s and q.
7. Every map used is natural on entire systems. The completion-unit formulas make
   h and v unique, so the square is natural in both inputs and keeps all transitions.
8. When the projections are invertible, compose the square with their inverses;
   functoriality preserves inverses and gives the final displayed identity.
   Cofinality ell^n = varpi^(en) permits arbitrary ramification throughout. -/
theorem compactification_b_projection_reduction
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (X Y : Over (Scheme.Spec.obj (op (CommRingCat.of D.k))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [IsSeparated f.left] (c : Compactification f.left)
    (AX : SpNormalizedEquivalence l E X.left (m.abelian X.left) (m.red X.left))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y.left (m.abelian Y.left) (m.red Y.left))
    (K : finiteTorConstructibleIntegralCategory l E Y.left)
    (M : finiteTorConstructibleIntegralCategory l E X.left) :
    ∃ (h : ordinaryInner l E m f.left K.obj M.obj ≅
        completedInner l E f.left K.obj M.obj)
      (v : ordinarySource l E m c K.obj M.obj ≅
        completedSource l E c K.obj M.obj)
      (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X.left).obj M.obj)
        ((VaryingRing.G (rings l E) (transitions l E) c.g).obj
          ((red l E m Y.left).obj K.obj)))),
      h.hom = innerUnit l E m f.left K.obj M.obj ∧
      v.hom = sourceUnit l E m c K.obj M.obj ∧
      finiteTorConstructibleIntegral l E X.left (completedInner l E f.left K.obj M.obj) ∧
      finiteTorConstructibleIntegral l E Y.left (completedSource l E c K.obj M.obj) ∧
      finiteTorConstructibleIntegral l E Y.left ((integralImage l E c).obj M.obj) ∧
      finiteTorConstructibleIntegral l E Y.left ((integralImage l E c).obj
        (completedInner l E f.left K.obj M.obj)) ∧
      normalized l E m X.left ((red l E m X.left).obj M.obj) ∧
      normalized l E m Y.left ((red l E m Y.left).obj K.obj) ∧
      normalized l E m X.left ((red l E m X.left).obj
        (completedInner l E f.left K.obj M.obj)) ∧
      normalized l E m Y.left ((red l E m Y.left).obj
        (completedSource l E c K.obj M.obj)) ∧
      normalized l E m Y.left
        ((systemImage l E c).obj ((red l E m X.left).obj
        (completedInner l E f.left K.obj M.obj))) ∧
      normalized l E m Y.left ((red l E m Y.left).obj
        ((integralImage l E c).obj M.obj)) ∧
      normalized l E m Y.left ((red l E m Y.left).obj
        ((integralImage l E c).obj (completedInner l E f.left K.obj M.obj))) ∧
      normalized l E m X.left ((m.systems X.left).closed.tensor.obj
        ((VaryingRing.G (rings l E) (transitions l E) f.left).obj
          ((red l E m Y.left).obj K.obj), (red l E m X.left).obj M.obj)) ∧
      normalized l E m Y.left ((m.systems Y.left).closed.tensor.obj
        ((red l E m Y.left).obj K.obj,
          (systemImage l E c).obj ((red l E m X.left).obj M.obj))) ∧
      normalized l E m Y.left ((systemImage l E c).obj
        ((m.systems X.left).closed.tensor.obj
          ((VaryingRing.G (rings l E) (transitions l E) f.left).obj
            ((red l E m Y.left).obj K.obj), (red l E m X.left).obj M.obj))) ∧
      IsIso (reconstruction l E m c AX AZ AY M.obj) ∧
      IsIso (reconstruction l E m c AX AZ AY (completedInner l E f.left K.obj M.obj)) ∧
      IsIso (q l E m f.left K.obj M.obj h) ∧
      IsIso (s l E m c AX AZ AY K.obj M.obj v) ∧
      ((red l E m Y.left).map (alpha l E m c K.obj M.obj v h) ≫
          reconstruction l E m c AX AZ AY (completedInner l E f.left K.obj M.obj) ≫
          (systemImage l E c).map (q l E m f.left K.obj M.obj h) =
        s l E m c AX AZ AY K.obj M.obj v ≫
          systemAlpha l E m c ((red l E m Y.left).obj K.obj)
            ((red l E m X.left).obj M.obj) hOpen) ∧
      (∀ (hi : IsIso (alpha l E m c K.obj M.obj v h))
        (ht : IsIso (systemAlpha l E m c ((red l E m Y.left).obj K.obj)
          ((red l E m X.left).obj M.obj) hOpen)),
        (red l E m Y.left).map
            (@inv _ _ _ _ (alpha l E m c K.obj M.obj v h) hi) ≫
          s l E m c AX AZ AY K.obj M.obj v =
        reconstruction l E m c AX AZ AY (completedInner l E f.left K.obj M.obj) ≫
          (systemImage l E c).map (q l E m f.left K.obj M.obj h) ≫
          @inv _ _ _ _ (systemAlpha l E m c ((red l E m Y.left).obj K.obj)
            ((red l E m X.left).obj M.obj) hOpen) ht) ∧
      (∀ (K' : finiteTorConstructibleIntegralCategory l E Y.left)
        (M' : finiteTorConstructibleIntegralCategory l E X.left)
        (h' : ordinaryInner l E m f.left K'.obj M'.obj ≅
          completedInner l E f.left K'.obj M'.obj)
        (v' : ordinarySource l E m c K'.obj M'.obj ≅
          completedSource l E c K'.obj M'.obj)
        (a : K ⟶ K') (b : M ⟶ M'),
        h'.hom = innerUnit l E m f.left K'.obj M'.obj →
        v'.hom = sourceUnit l E m c K'.obj M'.obj →
        (integralCompletedTensor l E Y.left).map
            (Prod.mkHom a.hom ((integralImage l E c).map b.hom)) ≫
          alpha l E m c K'.obj M'.obj v' h' =
        alpha l E m c K.obj M.obj v h ≫
          (integralImage l E c).map ((integralCompletedTensor l E X.left).map
            (Prod.mkHom ((integralDerivedPullback l E f.left).map a.hom) b.hom))) := by
  obtain ⟨h, v, hOpen, hh, hv, hD, hV, hPM, hPD,
    hnM, hnK, hnD, hnV, hnFD, hnPM, hnPD, hnT, hnS, hnFT, hbM, hbD⟩ :=
    completion_projection_domains l E m D _hl X Y f d c AX AZ AY K M
  obtain ⟨hsquare, hnatural⟩ :=
    ordinary_projection_reduction_square l E m D _hl X Y f d c AX AZ AY K M hOpen
  have hq : IsIso (q l E m f.left K.obj M.obj h) := by
    change IsIso (((red l E m X.left).mapIso h.symm ≪≫
      (m.tensor X.left).app ((ringedPull l E f.left).obj K.obj, M.obj) ≪≫
      (m.systems X.left).closed.tensor.mapIso
        (Iso.prod ((m.pull f.left).app K.obj) (Iso.refl _))).hom)
    infer_instance
  have hs : IsIso (s l E m c AX AZ AY K.obj M.obj v) := by
    let := hbM
    change IsIso (((red l E m Y.left).mapIso v.symm ≪≫
      (m.tensor Y.left).app (K.obj, (integralImage l E c).obj M.obj) ≪≫
      (m.systems Y.left).closed.tensor.mapIso
        (Iso.prod (Iso.refl _) (asIso (reconstruction l E m c AX AZ AY M.obj)))).hom)
    infer_instance
  have square :
      (red l E m Y.left).map (alpha l E m c K.obj M.obj v h) ≫
          reconstruction l E m c AX AZ AY (completedInner l E f.left K.obj M.obj) ≫
          (systemImage l E c).map (q l E m f.left K.obj M.obj h) =
        s l E m c AX AZ AY K.obj M.obj v ≫
          systemAlpha l E m c ((red l E m Y.left).obj K.obj)
            ((red l E m X.left).obj M.obj) hOpen := by
    have ht := conjugate_square (red l E m Y.left) (red l E m X.left)
      (integralImage l E c)
      (systemImage l E c) (ordinaryAlpha l E m c K.obj M.obj) h
      (reconstruction l E m c AX AZ AY (ordinaryInner l E m f.left K.obj M.obj))
      (reconstruction l E m c AX AZ AY (completedInner l E f.left K.obj M.obj))
      ((m.tensor X.left).hom.app ((ringedPull l E f.left).obj K.obj, M.obj) ≫
        (m.systems X.left).closed.tensor.map
          (Prod.mkHom ((m.pull f.left).hom.app K.obj) (𝟙 _)))
      ((m.tensor Y.left).hom.app (K.obj, (integralImage l E c).obj M.obj) ≫
        (m.systems Y.left).closed.tensor.map
          (Prod.mkHom (𝟙 _) (reconstruction l E m c AX AZ AY M.obj)))
      (systemAlpha l E m c ((red l E m Y.left).obj K.obj)
        ((red l E m X.left).obj M.obj) hOpen)
      (reconstruction_naturality l E m c AX AZ AY h.hom)
      (by simpa only [Category.assoc] using hsquare)
    simpa only [alpha, q, s, Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ (red l E m Y.left).map v.inv ≫ t) ht
  refine ⟨h, v, hOpen, hh, hv, hD, hV, hPM, hPD, hnM, hnK, hnD, hnV,
    hnFD, hnPM, hnPD, hnT, hnS, hnFT, hbM, hbD, hq, hs, square, ?_, ?_⟩
  · intro hi ht
    let := hi
    let := ht
    simpa only [Category.assoc] using
      inverse_square (red l E m Y.left) _ _ _ _ square
  · intro K' M' h' v' a b hh' hv'
    have source := ((m.integral.tensor Y.left).chi l E).naturality
      (Prod.mkHom a.hom ((integralImage l E c).map b.hom))
    change (m.integral.tensor Y.left).ordinary.tensor.map
        (Prod.mkHom a.hom ((integralImage l E c).map b.hom)) ≫
          sourceUnit l E m c K'.obj M'.obj =
        sourceUnit l E m c K.obj M.obj ≫
          (integralCompletedTensor l E Y.left).map
            (Prod.mkHom a.hom ((integralImage l E c).map b.hom)) at source
    rw [← hv, ← hv'] at source
    have inner := innerUnit_naturality l E m f.left a.hom b.hom
    rw [← hh, ← hh'] at inner
    unfold alpha
    apply (cancel_epi v.hom).1
    simp only [← Category.assoc]
    rw [← source]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc _ (ordinaryAlpha l E m c K'.obj M'.obj) _,
      hnatural K'.obj M'.obj a.hom b.hom]
    simp only [Category.assoc]
    have hmap := congrArg (fun z =>
      ordinaryAlpha l E m c K.obj M.obj ≫ (integralImage l E c).map z) inner
    simpa only [Functor.map_comp, Category.assoc] using hmap

end AlgebraicGeometry.ProEtale.CompactificationBProjection
