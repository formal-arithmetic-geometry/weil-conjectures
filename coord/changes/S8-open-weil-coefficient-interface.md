# Open Weil coefficient interface and exact adjoint

## Reason

The remaining theorem combines four independent coefficient comparisons with
exactness and two weight consequences. The new comparison statements must refer
to the literal carrier, stage inclusion, and coefficient fibre, without importing
the theorem that will use them. Move those existing declarations unchanged into
`Sheaf.Paper.OpenWeilCoefficientFibres` and publicly re-export them from the item.
This is an interface factoring for acyclic proof dependencies. It is unrelated
to the compile-time limit: the original unsplit module had already compiled in
37.6 seconds during debugging (with instance errors), and the measured costly
steps were proof elaboration and instance matching in the adjunction argument.
No large definition is split or changed to evade the limit. Explicit instance
arguments repair the adjunction proof's elaboration.

The chosen extension stays exactly the same left-adjoint construction, with its
existence supplied by the same argument retaining exactness information. The new
public theorem `zlOpenWeilShriek_exact` records that information. Every original
public signature, definition body, and target statement is unchanged. Data is
still chosen only from an adjunction, which determines it up to natural iso.

## Old

The following declarations lived directly in
`Sheaf.Paper.ExtensionByZeroPunctual` (verbatim signatures and bodies):

```lean
theorem zlOpen_quasiCompact : QuasiCompact j₀.left := by
  let := LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  infer_instance

theorem zlOpenFiber_isOpenImmersion : IsOpenImmersion (zlFiberMap D j₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

def zlWeilHeartCarrier (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] : sfCommonStageWeilSheaf D l hl Y₀ Qbar ⥤ generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfCommonStageWeilForget D l hl Y₀ Qbar

def zlFiniteWeilHeartCarrier (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] : sfWeilSheaf D l hl Y₀ E ⥤ sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfWeilForget D l hl Y₀ E

theorem zlWeilStageSquare_naturality (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) (K M : sfRationalConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber Y₀).left) (f : K ⟶ M) : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map f) ≫ (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L M).hom = (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).hom ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion L).map ((sfWeilFrobeniusPullback D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)).map f) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let g := (D.geometricFrobenius Y₀).hom
  let R := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) g
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Qbar
    (D.geometricFiber Y₀).left
  let c : R ⋙ S.T (le_refl L) ≅ S.T (le_refl L) ⋙ R :=
    isoWhiskerLeft R (operationStageTransitionIso l Qbar _ L L le_rfl) ≪≫
      rationalPullbackScalarComparison l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Qbar L L le_rfl) g ≪≫
      isoWhiskerRight (operationStageTransitionIso l Qbar _ L L le_rfl).symm R
  have hc : c.hom.app K ≫ R.map ((S.T (le_refl L)).map f) ≫ c.inv.app M =
      (S.T (le_refl L)).map (R.map f) := by
    have hn := c.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp
  have hm := (@commonStageDerivedPullback_existsUnique l _ Qbar _ _ _ _ _ g
    (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).exists.choose_spec
  have ht := zlTransportHom (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
    (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) _ _
    (hm.2 _ _ L le_rfl le_rfl ((S.T (le_refl L)).map f))
  have same :
      (commonStagePullbackComparison l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) L le_rfl).hom ≫
          R.map ((S.T (le_refl L)).map f) ≫
        (commonStagePullbackComparison l Qbar g
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M) L le_rfl).inv =
            (S.T (le_refl L)).map (R.map f) := by
    simpa only [commonStagePullbackComparison, commonStagePullbackObject,
      GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι,
      StageSystem.PairCategory.toStage, Functor.comp_obj, c, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app] using hc
  have he := ht.trans (congrArg
    (GeneralAlgebraicallyClosedCoefficients.ofHom
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) L le_rfl le_rfl) same)
  apply (cancel_epi (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [sfWeilStagePullbackIdentification, sfCommonStageWeilFrobeniusPullback,
    sfWeilFrobeniusPullback, eqToIso,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι]
  unfold commonStageDerivedPullback
  simpa only [commonStagePullbackObject, R, S, g,
    GeneralAlgebraicallyClosedCoefficients.ofHom,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι] using he

def zlWeilStageSquare (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) : GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅ sfWeilFrobeniusPullback D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L :=
  NatIso.ofComponents (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L)
    (fun {K M} f ↦ zlWeilStageSquare_naturality D l hl Qbar Y₀ L K M f)

theorem zlWeilHeartStage_mem (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) (K : sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) : sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar ((CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (zlWeilStageSquare D l hl Qbar Y₀ L)).obj K.obj).carrier := by
  constructor
  · exact ⟨L, K.obj.carrier, K.property.1, ⟨Iso.refl _⟩⟩
  · exact ⟨L, K.obj.carrier, K.property.2, ⟨Iso.refl _⟩⟩

def zlWeilHeartStage (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) : sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤ sfCommonStageWeilSheaf D l hl Y₀ Qbar :=
  ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Qbar)).lift
      (ObjectProperty.ι _ ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
        (zlWeilStageSquare D l hl Qbar Y₀ L))
      (zlWeilHeartStage_mem D l hl Qbar Y₀ L)

def zlClosedCoefficientFiber (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (ι : Y₀.left.residueField y.val →+* D.k) (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) : sfWeilSheaf D l hl Y₀ E ⥤ ModuleCat.{u} E :=
  zlFiniteWeilHeartCarrier D l hl E Y₀ ⋙
    @rationalDerivedPullback l _ E _ _ _ _ _ (localClosedPoint D Y₀ y ι hι)
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) ⋙
    pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

def ZlPunctualUpperBound (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (iota : Qbar ≃+* ℂ) (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
    SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
      ‖iota α‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)

```

## New

The declarations below now live in `Sheaf.Paper.OpenWeilCoefficientFibres` and
are publicly re-exported by `Sheaf.Paper.ExtensionByZeroPunctual`. Their signatures
and bodies are verbatim the same. The private proved transport helper and the
local elaboration attributes used by the naturality proof move with them.

```lean
theorem zlOpen_quasiCompact : QuasiCompact j₀.left := by
  let := LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  infer_instance

theorem zlOpenFiber_isOpenImmersion : IsOpenImmersion (zlFiberMap D j₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

def zlWeilHeartCarrier (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] : sfCommonStageWeilSheaf D l hl Y₀ Qbar ⥤ generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfCommonStageWeilForget D l hl Y₀ Qbar

def zlFiniteWeilHeartCarrier (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] : sfWeilSheaf D l hl Y₀ E ⥤ sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfWeilForget D l hl Y₀ E

theorem zlWeilStageSquare_naturality (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) (K M : sfRationalConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber Y₀).left) (f : K ⟶ M) : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map f) ≫ (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L M).hom = (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).hom ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion L).map ((sfWeilFrobeniusPullback D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)).map f) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let g := (D.geometricFrobenius Y₀).hom
  let R := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) g
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Qbar
    (D.geometricFiber Y₀).left
  let c : R ⋙ S.T (le_refl L) ≅ S.T (le_refl L) ⋙ R :=
    isoWhiskerLeft R (operationStageTransitionIso l Qbar _ L L le_rfl) ≪≫
      rationalPullbackScalarComparison l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Qbar L L le_rfl) g ≪≫
      isoWhiskerRight (operationStageTransitionIso l Qbar _ L L le_rfl).symm R
  have hc : c.hom.app K ≫ R.map ((S.T (le_refl L)).map f) ≫ c.inv.app M =
      (S.T (le_refl L)).map (R.map f) := by
    have hn := c.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp
  have hm := (@commonStageDerivedPullback_existsUnique l _ Qbar _ _ _ _ _ g
    (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).exists.choose_spec
  have ht := zlTransportHom (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
    (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) _ _
    (hm.2 _ _ L le_rfl le_rfl ((S.T (le_refl L)).map f))
  have same :
      (commonStagePullbackComparison l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) L le_rfl).hom ≫
          R.map ((S.T (le_refl L)).map f) ≫
        (commonStagePullbackComparison l Qbar g
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M) L le_rfl).inv =
            (S.T (le_refl L)).map (R.map f) := by
    simpa only [commonStagePullbackComparison, commonStagePullbackObject,
      GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι,
      StageSystem.PairCategory.toStage, Functor.comp_obj, c, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app] using hc
  have he := ht.trans (congrArg
    (GeneralAlgebraicallyClosedCoefficients.ofHom
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) L le_rfl le_rfl) same)
  apply (cancel_epi (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [sfWeilStagePullbackIdentification, sfCommonStageWeilFrobeniusPullback,
    sfWeilFrobeniusPullback, eqToIso,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι]
  unfold commonStageDerivedPullback
  simpa only [commonStagePullbackObject, R, S, g,
    GeneralAlgebraicallyClosedCoefficients.ofHom,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι] using he

def zlWeilStageSquare (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) : GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅ sfWeilFrobeniusPullback D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L :=
  NatIso.ofComponents (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L)
    (fun {K M} f ↦ zlWeilStageSquare_naturality D l hl Qbar Y₀ L K M f)

theorem zlWeilHeartStage_mem (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) (K : sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) : sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar ((CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (zlWeilStageSquare D l hl Qbar Y₀ L)).obj K.obj).carrier := by
  constructor
  · exact ⟨L, K.obj.carrier, K.property.1, ⟨Iso.refl _⟩⟩
  · exact ⟨L, K.obj.carrier, K.property.2, ⟨Iso.refl _⟩⟩

def zlWeilHeartStage (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (L : Padic.FiniteCoefficientFields l Qbar) : sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤ sfCommonStageWeilSheaf D l hl Y₀ Qbar :=
  ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Qbar)).lift
      (ObjectProperty.ι _ ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
        (zlWeilStageSquare D l hl Qbar Y₀ L))
      (zlWeilHeartStage_mem D l hl Qbar Y₀ L)

def zlClosedCoefficientFiber (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (ι : Y₀.left.residueField y.val →+* D.k) (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) : sfWeilSheaf D l hl Y₀ E ⥤ ModuleCat.{u} E :=
  zlFiniteWeilHeartCarrier D l hl E Y₀ ⋙
    @rationalDerivedPullback l _ E _ _ _ _ _ (localClosedPoint D Y₀ y ι hι)
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) ⋙
    pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

def ZlPunctualUpperBound (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (iota : Qbar ≃+* ℂ) (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
    SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
      ‖iota α‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)

```

The added theorem has the following signature:

```lean
theorem zlOpenWeilShriek_exact : (zlOpenWeilShriek D l hl Qbar j₀).Additive ∧ PreservesFiniteLimits (zlOpenWeilShriek D l hl Qbar j₀) ∧ PreservesFiniteColimits (zlOpenWeilShriek D l hl Qbar j₀)
```

## Users

`tools/downstream.py Sheaf.Paper.ExtensionByZeroPunctual --uses
zlOpenWeilShriek zlWeilHeartCarrier zlWeilHeartStage zlClosedCoefficientFiber
ZlPunctualUpperBound` finds only the following consumer. No adaptation is required.
The helper modules in this delivery are new, use the unchanged coefficient
interface, and do not change any consumer statement. No adopted source-library
module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExtensionByZeroPunctual | S8 | Publicly re-exports unchanged coefficient declarations; proves exactness and assembles the main theorem. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed in current claim records | Sees the identical declarations through the public re-export; no edit. |
| Sheaf.Paper.OpenWeilCoefficientFibres | new, S8 | Receives the unchanged coefficient interface and proved private helper. |
| Sheaf.Paper.OpenWeilCarrierRealization | new, S8 | States just the underlying compact-support carrier comparison. |
| Sheaf.Paper.OpenWeilGeometricFibres | new, S8 | States just the natural geometric fibre comparison. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | new, S8 | States just finite-stage and local-Frobenius comparisons. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | new, S8 | States weight-independent eigenvalue transport and residue cardinality equality. |

## Status

landed 20261025T203144-L-2787764 2026-10-25 (merge of deliver/S8/Sheaf.Paper.ExtensionByZeroPunctual)
