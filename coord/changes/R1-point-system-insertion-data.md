# WeilConjectures.PointSystemInsertion fixed constructions

## Reason

The coefficient, sheaf-comparison, strict-insertion and localization arguments must use
identical constructions without circular module imports. Move the existing declarations
preceding pointSystemInsertionComposition verbatim into PointSystemInsertionData. The
original module publicly re-exports it, retaining every original public import. No
signature, definition body, instance value, scalar map, category or predicate changes.
No target statement or meaning changes. This is an interface extraction; no consumer
source needs adaptation.

## Old

The following declarations are in lean/Sheaf/Paper/PointSystemInsertionComposition.lean
(the intervening private helpers and all earlier private helpers move verbatim too):

```lean
/-- Site reindexing by the specified positive power, with coefficient level unchanged.
Source: Stacks 03CB (blueprint: lem-trf-point-system-insertion-composition). -/
def reindex (r : ℕ) : (ℕ × (Spec (.of k)).ProEt) ⥤ (ℕ × (Spec (.of k)).ProEt) :=
  (𝟭 ℕ).prod (proEtaleIsoPostcompose (h ^ (r + 1)).hom)

/-- This reindexing preserves the vertical sheaf condition.
Source: Stacks 03CB, 0941 (blueprint: lem-trf-point-system-insertion-composition).
Proof: vertical covers are pro-etale covers in each fixed coefficient slice.
Postcomposition by an isomorphism preserves those covers and has the inverse
postcomposition equivalence. The index coordinate is unchanged. -/
@[instance] theorem reindexContinuous (r : ℕ) :
    (reindex k h r).IsContinuous
      (coefficientSequenceTopology (ProEt.topology (Spec (.of k))))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of k)))) := by
  let F := proEtaleIsoPostcompose (h ^ (r + 1)).hom
  let e := proEtaleIsoPostcompose_equivalence (h ^ (r + 1)).hom
  let E : (Spec (.of k)).ProEt ≌ (Spec (.of k)).ProEt :=
    CategoryTheory.Equivalence.mk F
      (proEtaleIsoPostcompose (inv (h ^ (r + 1)).hom))
      e.2.1.some.symm e.2.2.1.some
  have : (reindex k h r).IsEquivalence :=
    ((CategoryTheory.Equivalence.refl (C := ℕ)).prod E).isEquivalence_functor
  apply Functor.isContinuous_iff_coverPreserving.mpr
  exact sequence_cover_preserving _ _ (CoverPreserving.of_isContinuous F _ _)

/-- The existing sequence coefficient ring, forgetting only commutativity.
Source: Stacks 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
abbrev sequenceRing :=
  (sheafCompose (coefficientSequenceTopology (ProEt.topology (Spec (.of k))))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E (Spec (.of k)))

private theorem postcompose_cocontinuous
    (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g] :
    (proEtaleIsoPostcompose g).IsCocontinuous
      (ProEt.topology (Spec (.of k))) (ProEt.topology (Spec (.of k))) := by
  let e := proEtaleIsoPostcompose_equivalence g
  let eqv : (Spec (.of k)).ProEt ≌ (Spec (.of k)).ProEt :=
    CategoryTheory.Equivalence.mk (proEtaleIsoPostcompose g)
      (proEtaleIsoPostcompose (inv g)) e.2.1.some.symm e.2.2.1.some
  exact (eqv.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.the project server.some

private def constantComparisonIso
    (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g]
    (A : CommRingCat.{max u (t + 1)}) :
    (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
      ((constantSheaf (ProEt.topology (Spec (.of k)))
        CommRingCat.{max u (t + 1)}).obj A) ≅
    (constantSheaf (ProEt.topology (Spec (.of k)))
      CommRingCat.{max u (t + 1)}).obj A := by
  have := postcompose_cocontinuous k g
  exact ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of k)))
      (ProEt.topology (Spec (.of k)))).symm.app
        ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)

private theorem constantComparisonIso_eq
    (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g]
    (A : CommRingCat.{max u (t + 1)}) :
    (sheafCompose (ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (constantComparisonIso k g A).hom = isoSectionwiseConstantMap g A := by
  have := postcompose_cocontinuous k g
  apply (isoSectionwiseConstantMap_existsUnique g A).unique
  · intro U a
    let i := (sheafToPresheaf (ProEt.topology (Spec (.of k)))
      CommRingCat.{max u (t + 1)}).mapIso
        (((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
          CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of k)))
            (ProEt.topology (Spec (.of k)))).app
              ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A))
    have h : (proEtaleIsoPostcompose g).op.whiskerLeft
        (toSheafify (ProEt.topology (Spec (.of k)))
          ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)) ≫ i.inv =
        toSheafify (ProEt.topology (Spec (.of k)))
          ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A) := by
      apply (i.comp_inv_eq).2
      exact ((proEtaleIsoPostcompose g).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of k)))
          (ProEt.topology (Spec (.of k)))
            ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)).symm
    exact congrArg (fun f ↦ f.app (op U) a) h
  · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec

set_option backward.isDefEq.respectTransparency.types false

private theorem ringSystem_map {m n : ℕ} (h : n ≤ m) :
    (sheafCompose (ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((coefficientSequenceCommRingSystem l E (Spec (.of k))).map (homOfLE h).op) =
      (integralCoefficientSheafSystem l E (Spec (.of k))).map (homOfLE h).op := by
  let ε : (coefficientSequenceCommRingSystem l E (Spec (.of k)) ⋙
        sheafCompose (ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})) ⟶
      integralCoefficientSheafSystem l E (Spec (.of k)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun k ↦ by
      dsimp only [Functor.comp_map, coefficientSequenceCommRingSystem,
        integralCoefficientSheafSystem]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      simp only [Category.comp_id, Category.id_comp]
      rfl)
  have he := ε.naturality (homOfLE h).op
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at he
  simpa only [Category.comp_id, Category.id_comp, Functor.comp_map] using he

private theorem sequence_map {X Y : ℕ × (Spec (.of k)).ProEt} (f : Y ⟶ X) :
    (sequenceRing k l E).obj.map f.op =
      ((integralCoefficientSheafSystem l E (Spec (.of k))).map f.1.op).hom.app
          (op X.2) ≫
        (integralCoefficientSheaf l E (Spec (.of k)) Y.1).obj.map f.2.op := by
  have he := congrArg (fun k ↦ k.hom.app (op X.2))
    (ringSystem_map k l E (leOfHom f.1))
  change (forget₂ CommRingCat RingCat).map (_ ≫ _) = _
  rw [Functor.map_comp]
  change (forget₂ CommRingCat RingCat).map
    (((coefficientSequenceCommRingSystem l E (Spec (.of k))).map
      (homOfLE (leOfHom f.1)).op).hom.app (op X.2)) ≫ _ = _
  change (forget₂ CommRingCat RingCat).map
    (((coefficientSequenceCommRingSystem l E (Spec (.of k))).map
      (homOfLE (leOfHom f.1)).op).hom.app (op X.2)) = _ at he
  rw [he]
  rfl

private theorem finite_comparison_naturality
    (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g] (n : ℕ) :
    inverseImageFiniteCoefficientMap l E g (n + 1) ≫
        integralCoefficientSheafTransition l E (Spec (.of k)) n =
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        (integralCoefficientSheafTransition l E (Spec (.of k)) n) ≫
          inverseImageFiniteCoefficientMap l E g n := by
  let q : CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  have := postcompose_cocontinuous k g
  let e := ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of k)))
      (ProEt.topology (Spec (.of k)))).symm
  have h := e.hom.naturality ((Functor.const (Spec (.of k)).ProEtᵒᵖ).map q)
  let W := sheafCompose (ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have h' := congrArg W.map h.symm
  simp only [Functor.map_comp] at h'
  change W.map (constantComparisonIso k g _).hom ≫ _ =
    _ ≫ W.map (constantComparisonIso k g _).hom at h'
  rw [constantComparisonIso_eq, constantComparisonIso_eq] at h'
  exact h'

private def inverseFiniteSystem
    (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g] :
    integralCoefficientSheafSystem l E (Spec (.of k)) ⟶
      integralCoefficientSheafSystem l E (Spec (.of k)) ⋙
        isoSectionwiseInverseImage g RingCat.{max u (t + 1)} :=
  NatTrans.ofOpSequence
    (fun n ↦ inv (inverseImageFiniteCoefficientMap l E g n)) (fun n ↦ by
      dsimp only [Functor.comp_map, integralCoefficientSheafSystem]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      apply (cancel_mono (inverseImageFiniteCoefficientMap l E g n)).mp
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
        ← finite_comparison_naturality, ← Category.assoc, IsIso.inv_hom_id,
        Category.id_comp])

/-- The coefficient map is uniquely prescribed on every section at every level.
Source: Stacks 0H7J, 0941 (blueprint: lem-trf-point-system-insertion-composition).
Proof: inverse finite constant-coefficient comparisons commute with reductions by
naturality of constant sheafification. Their inverses therefore assemble as a
natural transformation of the sequence ring sheaf; sectionwise extensionality gives
uniqueness. -/
theorem coefficient_existsUnique (r : ℕ) :
    ∃! c : sequenceRing k l E ⟶
      ((reindex k h r).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology (Spec (.of k))))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of k))))).obj
          (sequenceRing k l E),
      ∀ (n : ℕ) (U : (Spec (.of k)).ProEt),
        HEq (c.hom.app (op (n, U)))
          ((inv (inverseImageFiniteCoefficientMap l E (h ^ (r + 1)).hom n)).hom.app
            (op U)) := by
  let g := (h ^ (r + 1)).hom
  let c : sequenceRing k l E ⟶
      ((reindex k h r).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology (Spec (.of k))))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of k))))).obj
          (sequenceRing k l E) :=
    ⟨{ app X := ((inverseFiniteSystem k l E g).app (op X.unop.1)).hom.app
          (op X.unop.2)
       naturality X Y f := by
         have hn := (inverseFiniteSystem k l E g).naturality f.unop.1.op
         have hh := congrArg (fun z ↦ z.hom.app (op X.unop.2)) hn
         have hv := ((inverseFiniteSystem k l E g).app (op Y.unop.1)).hom.naturality
           f.unop.2.op
         simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hh
         change (sequenceRing k l E).obj.map f ≫ _ =
           _ ≫ (sequenceRing k l E).obj.map ((reindex k h r).map f.unop).op
         rw [show f = f.unop.op from rfl, sequence_map, sequence_map]
         exact (Category.assoc _ _ _).trans
           ((congrArg (fun z ↦
             ((integralCoefficientSheafSystem l E (Spec (.of k))).map
               f.unop.1.op).hom.app (op X.unop.2) ≫ z) hv).trans
             ((Category.assoc _ _ _).symm.trans
               ((congrArg (fun z ↦ z ≫
                 ((integralCoefficientSheafSystem l E (Spec (.of k)) ⋙
                   isoSectionwiseInverseImage g RingCat).obj
                     (op Y.unop.1)).obj.map f.unop.2.op) hh).trans
                   (Category.assoc _ _ _)))) }⟩
  refine ⟨c, fun _ _ ↦ HEq.rfl, ?_⟩
  intro d hd
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  exact eq_of_heq (hd X.unop.1 X.unop.2)


attribute [local irreducible] CategoryTheory.constantSheaf

/-- The uniquely normalized coefficient map; no unprescribed ring map is chosen.
Source: Stacks 0H7J (blueprint: lem-trf-point-system-insertion-composition). -/
def coefficient (r : ℕ) := (coefficient_existsUnique k h l E r).exists.choose

/-- Whole-system inverse image, applying actual reindexing to all original transitions.
Source: Stacks 03CB, 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
def G (r : ℕ) : coefficientSequenceModules l E (Spec (.of k)) ⥤
    coefficientSequenceModules l E (Spec (.of k)) :=
  SheafOfModules.pushforward (F := reindex k h r) (coefficient k h l E r)

/-- Exactness is componentwise and places no condition on an input system.
Source: Stacks 015F, 0941 (blueprint: lem-trf-point-system-insertion-composition).
Proof: underlying inverse images are exact site equivalences; coefficient transport
changes only scalar actions. Kernels and cokernels of semilinear strict systems are
componentwise, so reindexing preserves them as well as componentwise addition. -/
theorem G_exact (r : ℕ) : (G k h l E r).Additive ∧
    PreservesFiniteLimits (G k h l E r) ∧ PreservesFiniteColimits (G k h l E r) := by
  let g := (h ^ (r + 1)).hom
  let Q := proEtaleIsoPostcompose g
  let Q' := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let e₀ : (Spec (.of k)).ProEt ≌ (Spec (.of k)).ProEt :=
    CategoryTheory.Equivalence.mk Q Q' e.2.1.some.symm e.2.2.1.some
  let e₁ := (CategoryTheory.Equivalence.refl (C := ℕ)).prod e₀
  let P := (𝟭 ℕ).prod Q'
  let J := coefficientSequenceTopology (ProEt.topology (Spec (.of k)))
  have : P.IsEquivalence := e₁.isEquivalence_inverse
  have : P.IsContinuous J J := by
    apply Functor.isContinuous_iff_coverPreserving.mpr
    exact sequence_cover_preserving _ _ (CoverPreserving.of_isContinuous Q' _ _)
  have : (reindex k h r ⋙ P).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  have : (P ⋙ reindex k h r).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  have : e₁.functor.IsContinuous J J := reindexContinuous k h r
  have : e₁.inverse.IsContinuous J J := inferInstanceAs (P.IsContinuous J J)
  have : (e₁.functor ⋙ e₁.inverse).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  have : (e₁.inverse ⋙ e₁.functor).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  let A := AddCommGrpCat.{max u (t + 1)}
  let H := (reindex k h r).sheafPushforwardContinuous A J J
  let H' := P.sheafPushforwardContinuous A J J
  let es : Sheaf J A ≌ Sheaf J A := CategoryTheory.Equivalence.mk H H'
    ((Functor.sheafPushforwardContinuousComp P (reindex k h r) A J J J ≪≫
      Functor.sheafPushforwardContinuousId' e₁.counitIso A J).symm)
    (Functor.sheafPushforwardContinuousComp (reindex k h r) P A J J J ≪≫
      Functor.sheafPushforwardContinuousId' e₁.unitIso.symm A J)
  have : H.IsEquivalence := es.isEquivalence_functor
  let V := SheafOfModules.toSheaf.{max u (t + 1)} (sequenceRing k l E)
  let T := G k h l E r
  have : T.Additive := ⟨fun {_ _} f g ↦ by ext U x; rfl⟩
  let ei : T ⋙ V ≅ V ⋙ H := Iso.refl _
  have : PreservesFiniteLimits (T ⋙ V) := preservesFiniteLimits_of_natIso ei.symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T V
  have : PreservesFiniteColimits (T ⋙ V) := preservesFiniteColimits_of_natIso ei.symm
  have : ReflectsFiniteColimits V :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨inferInstance, inferInstance,
    preservesFiniteColimits_of_reflects_of_preserves T V⟩

/-- Additivity supplied by exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-insertion-composition). -/
instance GAdditive (r : ℕ) : (G k h l E r).Additive := (G_exact k h l E r).1

/-- Left exactness supplied by componentwise exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-insertion-composition). -/
instance GLimits (r : ℕ) : PreservesFiniteLimits (G k h l E r) :=
  (G_exact k h l E r).2.1

/-- Right exactness supplied by componentwise exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-insertion-composition). -/
instance GColimits (r : ℕ) : PreservesFiniteColimits (G k h l E r) :=
  (G_exact k h l E r).2.2

/-- Existing finite or completed module inverse image with its canonical coefficients.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-insertion-composition). -/
abbrev F (r : ℕ) (a : Option ℕ) :
    SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E (Spec (.of k)) a) ⥤
      SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E (Spec (.of k)) a) :=
  pointRestrictionInverseImage l E (h ^ (r + 1)).hom a

/-- Levelwise completed inverse image on actual module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
abbrev FTow (r : ℕ) :
    (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of k))) ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of k))) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F k h l E r none)

/-- Underlying inverse image on coefficient sheaves, in the recorded sectionwise model.
Source: Stacks 03CB (blueprint: lem-trf-point-system-insertion-composition). -/
abbrev ringF (r : ℕ) :
    Sheaf (ProEt.topology (Spec (.of k))) RingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology (Spec (.of k))) RingCat.{max u (t + 1)} :=
  isoSectionwiseInverseImage (h ^ (r + 1)).hom RingCat.{max u (t + 1)}

/-- The actual coefficient map with both its endpoints displayed.
Source: Stacks 0H7J, 03CO (blueprint: lem-trf-point-system-insertion-composition). -/
abbrev c (r : ℕ) (a : Option ℕ) :
    (ringF.{t, u} k h r).obj (pointRestrictionRing l E (Spec (.of k)) a) ⟶
      pointRestrictionRing l E (Spec (.of k)) a :=
  pointRestrictionCoefficientMap l E (h ^ (r + 1)).hom a

/-- The specified site compositor on sheaves of rings, in sectionwise coordinates.
Source: Stacks 03CB (blueprint: lem-trf-point-system-insertion-composition). -/
def ringCompositor (m : ℕ) :
    isoSectionwiseInverseImage (h ^ (m + 1)).hom RingCat.{max u (t + 1)} ⋙
      isoSectionwiseInverseImage (h ^ (0 + 1)).hom RingCat.{max u (t + 1)} ≅
    isoSectionwiseInverseImage (h ^ ((m + 1) + 1)).hom RingCat.{max u (t + 1)} :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (pointSheafReindexCompositor h m).symm)
    RingCat.{max u (t + 1)} (ProEt.topology (Spec (.of k)))
      (ProEt.topology (Spec (.of k))) (ProEt.topology (Spec (.of k)))

/-- Final-object sections after actual scalar restriction, keeping the whole tower.
The common-universe lift of R is the recorded coefficient-tower convention.
Source: Stacks 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
def sections : coefficientSequenceModules l E (Spec (.of k)) ⥤
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  coefficientSequenceRestriction l E (Spec (.of k)) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E k none)

private theorem point_evaluation_surjective (k : Type t) [Field k] [IsAlgClosed k]
    (F G : Sheaf (ProEt.topology (Spec (.of k))) (Type (max u (t + 1))))
    (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  classical
  have : WLocalSpace (PrimeSpectrum k) :=
    { eq_of_specializes := fun _ _ _ _ ↦ Subsingleton.elim _ _
      isClosed_closedPoints := by
        have : closedPoints (PrimeSpectrum k) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact mem_closedPoints_iff.mpr isClosed_singleton
        rw [this]
        exact isClosed_univ }
  have : IsWLocalRing k := ⟨inferInstance⟩
  have : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k _
      (RingEquiv.ofBijective (IsLocalRing.residue k)
        ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  have : IsStrictlyHenselianLocalRing k := ⟨inferInstance⟩
  have hstrict (m : Ideal k) [m.IsMaximal] :
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    apply IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.atUnits k m.primeCompl (S := Localization.AtPrime m) ?_).toRingEquiv
    intro x hx
    exact isUnit_iff_ne_zero.mpr (fun he ↦ hx (he ▸ m.zero_mem))
  exact ProEt.surjective_app_of_affine_ring_retractions (Spec (.of k)) k (𝟙 _)
    (fun B _ φ hf hw ↦
      RingHom.exists_retraction_of_wlocal_geometric_criterion hstrict φ hf hw) F G f

private theorem restriction_sections_exact (k : Type t) [Field k] [IsAlgClosed k]
    (a : Option ℕ) :
    PreservesFiniteLimits (pointRestrictionSections l E k a) ∧
      PreservesFiniteColimits (pointRestrictionSections l E k a) := by
  let R := pointRestrictionRing l E (Spec (.of k)) a
  let ev := SheafOfModules.evaluation.{max u (t + 1)} R
    (op (ProEt.mk (𝟙 (Spec (.of k)))))
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} g).mpr inferInstance
    let g' := (sheafCompose (ProEt.topology (Spec (.of k)))
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map g
    have : Epi g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr
      (point_evaluation_surjective k _ _ g')
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteLimits ev := Functor.preservesFiniteLimits_of_preservesHomology ev
  have : PreservesFiniteColimits ev := Functor.preservesFiniteColimits_of_preservesHomology ev
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let T : ModuleCat.{max u (t + 1)} (R.obj.obj U) ⥤
      ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E a) :=
    ModuleCat.restrictScalars (pointRestrictionScalarAt l E (Spec (.of k)) a U.unop)
  let V := forget₂
    (ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E a))
    AddCommGrpCat.{max u (t + 1)}
  have : PreservesFiniteLimits (T ⋙ V) :=
    inferInstanceAs (PreservesFiniteLimits
      (forget₂ (ModuleCat.{max u (t + 1)} (R.obj.obj U)) AddCommGrpCat.{max u (t + 1)}))
  have : PreservesFiniteColimits (T ⋙ V) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat.{max u (t + 1)} (R.obj.obj U)) AddCommGrpCat.{max u (t + 1)})
    infer_instance
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T V
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_reflects_of_preserves T V
  exact ⟨comp_preservesFiniteLimits ev T, comp_preservesFiniteColimits ev T⟩

/-- Whole-system sections are exact over an algebraically closed point.
Source: Stacks 0941, 0946 (blueprint: lem-trf-point-system-insertion-composition).
Proof: the algebraically closed point is w-contractible, so final-object sections
are exact. Scalar restriction does not change kernels or cokernels. Exactness in
the system category and in ordinary module towers is componentwise. -/
theorem sections_exact [IsAlgClosed k] : (sections k l E).Additive ∧
    PreservesFiniteLimits (sections k l E) ∧ PreservesFiniteColimits (sections k l E) := by
  have := (restriction_sections_exact l E k none).1
  have := (restriction_sections_exact l E k none).2
  let T := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E k none)
  have : PreservesFiniteLimits T := by
    constructor
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
    intro n
    change PreservesLimitsOfShape J
      ((evaluation ℕᵒᵖ _).obj n ⋙ pointRestrictionSections l E k none)
    infer_instance
  have : PreservesFiniteColimits T := by
    constructor
    intro J _ _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    change PreservesColimitsOfShape J
      ((evaluation ℕᵒᵖ _).obj n ⋙ pointRestrictionSections l E k none)
    infer_instance
  refine ⟨?_, comp_preservesFiniteLimits (coefficientSequenceRestriction l E _) T,
    comp_preservesFiniteColimits (coefficientSequenceRestriction l E _) T⟩
  constructor
  intro M N f g
  ext n x
  change (((coefficientSequenceRestriction l E _).map (f + g)).app n).val.app _ x = _
  rw [Functor.map_add]
  rfl

/-- Additivity of the whole-system sections functor.
Source: Stacks 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
instance sectionsAdditive [IsAlgClosed k] : (sections k l E).Additive :=
  (sections_exact k l E).1

/-- Left exactness of whole-system sections.
Source: Stacks 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
instance sectionsLimits [IsAlgClosed k] : PreservesFiniteLimits (sections k l E) :=
  (sections_exact k l E).2.1

/-- Right exactness of whole-system sections.
Source: Stacks 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
instance sectionsColimits [IsAlgClosed k] : PreservesFiniteColimits (sections k l E) :=
  (sections_exact k l E).2.2

/-- Standard ordinary unbounded localization of entire R-module towers.
Source: Stacks 05RU (blueprint: lem-trf-point-system-insertion-composition). -/
instance towerDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  HasDerivedCategory.standard _

/-- Actual tensor pullback at finite level, as recorded in the comparison dependency.
Source: Stacks 03D3 (blueprint: lem-trf-point-system-insertion-composition). -/
abbrev tensorPull (r n : ℕ) :
    integralOperationsFiniteModules l E (Spec (.of k)) n ⥤
      integralOperationsFiniteModules l E (Spec (.of k)) n :=
  integralOperationsLevelPullback l E (h ^ (r + 1)).hom n

/-- The actual ordinary module compositor, oriented from successive to direct pullback.
It is the inverse of the uniquely adjunction-normalized comparison in the dependency.
Source: Stacks 03D8 (blueprint: lem-trf-point-system-insertion-composition). -/
def tensorCompositor (m n : ℕ) : tensorPull k h l E m n ⋙ tensorPull k h l E 0 n ≅
    tensorPull k h l E (m + 1) n :=
  (coefficientModulePullbackComposition (h ^ (0 + 1)).hom (h ^ (m + 1)).hom
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).symm ≪≫
    eqToIso (congrArg (fun g ↦ integralOperationsLevelPullback l E g n)
      (congrArg Iso.hom (pow_succ h (m + 1))).symm)

/-- Termwise application of a natural whole-system insertion, with factored target.
Source: Stacks 015F (blueprint: lem-trf-point-system-insertion-composition). -/
def complexInsertion [IsAlgClosed k] (r : ℕ)
    (u : sections k l E ⟶ G k h l E r ⋙ sections k l E) :
    (sections k l E).mapHomologicalComplex (.up ℤ) ⟶
      (G k h l E r).mapHomologicalComplex (.up ℤ) ⋙
        (sections k l E).mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex u (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (G k h l E r ⋙ sections k l E)) (.up ℤ)).inv

attribute [local irreducible] G sections

/-- The complete normalized compositor and insertion assertion, before and after
localization. All sheaf, tower, chain and derived maps are natural transformations;
all component normalizations are imposed on the actual dependency constructions.
Source: Stacks 03CB, 0H7J, 03D8 and blueprint Global powers
(blueprint: lem-trf-point-system-insertion-composition). -/
structure Maps [IsAlgClosed k] where
  /-- Natural module compositors, finite and completed. -/
  d : ∀ (m : ℕ) (a : Option ℕ), F k h l E m a ⋙ F k h l E 0 a ≅
    F k h l E (m + 1) a
  /-- Natural compositors of entire strict quotient-linear systems. -/
  t : ∀ m : ℕ, G k h l E m ⋙ G k h l E 0 ≅ G k h l E (m + 1)
  /-- The actual scalar-restriction comparison of whole towers. -/
  b : ∀ r : ℕ, coefficientSequenceRestriction l E (Spec (.of k)) ⋙ FTow k h l E r ≅
    G k h l E r ⋙ coefficientSequenceRestriction l E (Spec (.of k))
  /-- The specified finite tensor-unit comparison is invertible. -/
  j : ∀ r n : ℕ, F k h l E r (some n) ≅ tensorPull k h l E r n
  /-- R-linear insertion as a natural transformation of entire towers. -/
  u : ∀ r : ℕ, sections k l E ⟶ G k h l E r ⋙ sections k l E
  /-- Localization of insertion on entire ordinary unbounded derived categories. -/
  I : ∀ r : ℕ, (sections k l E).mapDerivedCategory ⟶
    (G k h l E r).mapDerivedCategory ⋙ (sections k l E).mapDerivedCategory

/-- Evaluation and inverse image change the action but not the underlying section group.
Source: Stacks 03D6, 0941 (blueprint: lem-trf-point-system-insertion-composition).
Proof: evaluation is restriction to the coefficient slice; its recorded ring equality
only transports the action. Inverse image precomposes the underlying abelian presheaf
by postcomposition with h^(r+1). Forgetting both scalar actions gives the displayed group. -/
theorem inverseImageEvaluationSection_eq (r n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of k))) (U : (Spec (.of k)).ProEt) :
    ((F k h l E r (some n)).obj
      ((coefficientSequenceEvaluation l E (Spec (.of k)) n).obj M)).val.presheaf.obj (op U) =
      M.val.presheaf.obj (op (n, (proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U)) := by
  rfl

/-- The specified finite tensor unit, with only the canonical equality of section groups
transported explicitly. No isomorphism of unprescribed coefficients is used.
Source: Stacks 03D2, 03EK (blueprint: lem-trf-point-system-insertion-composition). -/
def finiteUnit [IsAlgClosed k] (P : Maps k h l E) (r n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of k))) (U : (Spec (.of k)).ProEt)
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))) :
    ((tensorPull k h l E r n).obj
      ((coefficientSequenceEvaluation l E (Spec (.of k)) n).obj M)).val.obj (op U) :=
  ((P.j r n).hom.app
    ((coefficientSequenceEvaluation l E (Spec (.of k)) n).obj M)).val.app (op U)
    ((eqToHom (inverseImageEvaluationSection_eq k h l E r n M U).symm) x)

/-- The finite tensor transition conjugates the actual underlying abelian horizontal
restriction by the tensor-unit comparisons. Using the underlying abelian presheaf
retains precisely the original semilinear map, without a spurious common finite action.
Source: Stacks 03D2, 03EK (blueprint: lem-trf-point-system-insertion-composition). -/
def tensorTransition [IsAlgClosed k] (P : Maps k h l E) (r n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of k))) (U : (Spec (.of k)).ProEt) :
    ((tensorPull k h l E r (n + 1)).obj
        ((coefficientSequenceEvaluation l E (Spec (.of k)) (n + 1)).obj M)).val.obj (op U) →
      ((tensorPull k h l E r n).obj
        ((coefficientSequenceEvaluation l E (Spec (.of k)) n).obj M)).val.obj (op U) :=
  fun x ↦ finiteUnit k h l E P r n M U
    (M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
      (𝟙 ((proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))).op
      ((eqToHom (inverseImageEvaluationSection_eq k h l E r (n + 1) M U))
        (((P.j r (n + 1)).inv.app
          ((coefficientSequenceEvaluation l E (Spec (.of k)) (n + 1)).obj M)).val.app
            (op U) x)))

/-- One group of the normalized whole-system compositor laws.
Source: Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-insertion-composition). -/
def CoefficientLaws [IsAlgClosed k] : Prop :=
  (∀ (m : ℕ) (a : Option ℕ),
    (ringCompositor.{t, u} k h m).hom.app (pointRestrictionRing l E (Spec (.of k)) a) ≫
        c k h l E (m + 1) a =
      (ringF.{t, u} k h 0).map (c k h l E m a) ≫ c k h l E 0 a) ∧
  (∀ r n : ℕ,
    inverseImageCompletedCoefficientMap l E (h ^ (r + 1)).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of k))) (op n) =
      (isoSectionwiseInverseImage (h ^ (r + 1)).hom RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (h ^ (r + 1)).hom n
)

/-- One group of the normalized whole-system compositor laws.
Source: Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-insertion-composition). -/
def SectionLaws [IsAlgClosed k] (P : Maps k h l E) : Prop :=
  (∀ (m : ℕ) (a : Option ℕ)
    (M : SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E (Spec (.of k)) a))
    (U : (Spec (.of k)).ProEt)
    (x : ((F k h l E m a ⋙ F k h l E 0 a).obj M).val.obj (op U)),
    HEq (((P.d m a).hom.app M).val.app (op U) x) x) ∧
  (∀ (m : ℕ) (M : coefficientSequenceModules l E (Spec (.of k)))
    (n : ℕ) (U : (Spec (.of k)).ProEt)
    (x : ((G k h l E m ⋙ G k h l E 0).obj M).val.obj (op (n, U))),
    HEq (((P.t m).hom.app M).val.app (op (n, U)) x) x) ∧
  (∀ (r : ℕ) (M : coefficientSequenceModules l E (Spec (.of k)))
    (n : ℕ) (U : (Spec (.of k)).ProEt)
    (x : (((coefficientSequenceRestriction l E (Spec (.of k)) ⋙
      FTow k h l E r).obj M).obj (op n)).val.obj (op U)),
    HEq ((((P.b r).hom.app M).app (op n)).val.app (op U) x) x
)

/-- The levelwise module compositor on a completed-module tower, retaining its maps.
The associator writes out the two parentheses in the iterated tower functor.
Source: Stacks 03CB, 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
def towerCompositor [IsAlgClosed k] (P : Maps k h l E) (m : ℕ)
    (T : ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of k))) :
    (FTow k h l E 0).obj ((FTow k h l E m).obj T) ≅
      (FTow k h l E (m + 1)).obj T :=
  Functor.associator T (F k h l E m none) (F k h l E 0 none) ≪≫
    Functor.isoWhiskerLeft T (P.d m none)

/-- The scalar restriction coherence as an equality of actual whole-tower maps.
Source: Stacks 03CB, 0941 (blueprint: lem-trf-point-system-insertion-composition). -/
def RestrictionCompositionLaws [IsAlgClosed k] (P : Maps k h l E) : Prop :=
  (∀ (m : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of k))),
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (F k h l E 0 none)).map
        ((P.b m).hom.app M) ≫ (P.b 0).hom.app ((G k h l E m).obj M) ≫
        (coefficientSequenceRestriction l E (Spec (.of k))).map ((P.t m).hom.app M) =
      (towerCompositor k h l E P m
        ((coefficientSequenceRestriction l E (Spec (.of k))).obj M)).hom ≫
        (P.b (m + 1)).hom.app M)

/-- One group of the normalized whole-system compositor laws.
Source: Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-insertion-composition). -/
def TensorLaws [IsAlgClosed k] (P : Maps k h l E) : Prop :=
  (∀ (r n : ℕ) (M : integralOperationsFiniteModules l E (Spec (.of k)) n)
    (U : (Spec (.of k)).ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))),
    ((P.j r n).hom.app M).val.app (op U) x =
      (((tensorPull k h l E r n).obj M).val.map
        (proEtaleIsoCommaArrow (h ^ (r + 1)).hom U).op)
        (integralOperationsPullbackGenerator l E (h ^ (r + 1)).hom n M
          ((proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U) x)) ∧
  (∀ (m n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of k)) n),
    (P.j 0 n).hom.app ((F k h l E m (some n)).obj M) ≫
        (tensorPull k h l E 0 n).map ((P.j m n).hom.app M) ≫
        (tensorCompositor k h l E m n).hom.app M =
      (P.d m (some n)).hom.app M ≫ (P.j (m + 1) n).hom.app M
)

/-- The actual finite tensor-transition rule, including both paths on a unit insertion.
Source: Stacks 03D2, 03EK (blueprint: lem-trf-point-system-insertion-composition). -/
def TransitionLaws [IsAlgClosed k] (P : Maps k h l E) : Prop :=
  (∀ (r n : ℕ) (M : coefficientSequenceModules l E (Spec (.of k)))
    (U : (Spec (.of k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of k)) (n + 1)).obj.obj (op U))
    (x : M.val.obj
      (op (n + 1, (proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))),
    tensorTransition k h l E P r n M U
      (a • finiteUnit k h l E P r (n + 1) M U x) =
      ((integralCoefficientSheafTransition l E (Spec (.of k)) n).hom.app (op U) a) •
        (finiteUnit k h l E P r n M U
          (M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
            (𝟙 ((proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))).op x))) ∧
  (∀ (r n : ℕ) (M : coefficientSequenceModules l E (Spec (.of k)))
    (U : (Spec (.of k)).ProEt)
    (x : M.val.obj
      (op (n + 1, (proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))),
    tensorTransition k h l E P r n M U
      (finiteUnit k h l E P r (n + 1) M U x) =
      finiteUnit k h l E P r n M U
          (M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
            (𝟙 ((proEtaleIsoPostcompose (h ^ (r + 1)).hom).obj U))).op x))

/-- One group of the normalized whole-system compositor laws.
Source: Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-insertion-composition). -/
def StrictInsertionLaws [IsAlgClosed k] (P : Maps k h l E) : Prop :=
  (∀ (r : ℕ) (M : coefficientSequenceModules l E (Spec (.of k)))
    (n : ℕ),
    HEq (fun x : ((sections k l E).obj M).obj (op n) ↦
        (((P.u r).app M).app (op n)) x)
      (fun x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of k))))) ↦
        M.val.presheaf.map
          (Prod.mkHom (𝟙 n) (pointRestrictionArrow (h ^ (r + 1)).hom)).op x)) ∧
  (∀ (m : ℕ) (M : coefficientSequenceModules l E (Spec (.of k))),
    (P.u (m + 1)).app M = (P.u m).app M ≫ (P.u 0).app ((G k h l E m).obj M) ≫
      (sections k l E).map ((P.t m).hom.app M)) ∧
  (∀ (m : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ),
    (complexInsertion k h l E (m + 1) (P.u (m + 1))).app M =
      (complexInsertion k h l E m (P.u m)).app M ≫
        (complexInsertion k h l E 0 (P.u 0)).app
          (((G k h l E m).mapHomologicalComplex (.up ℤ)).obj M) ≫
        ((sections k l E).mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (P.t m) (.up ℤ)).hom.app M))

/-- One group of the normalized whole-system compositor laws.
Source: Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-insertion-composition). -/
def DerivedInsertionLaws [IsAlgClosed k] (P : Maps k h l E) : Prop :=
  (∀ (r : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ),
    (P.I r).app (DerivedCategory.Q.obj M) ≫
        (sections k l E).mapDerivedCategory.map
          ((G k h l E r).mapDerivedCategoryFactors.hom.app M) ≫
        (sections k l E).mapDerivedCategoryFactors.hom.app
          (((G k h l E r).mapHomologicalComplex (.up ℤ)).obj M) =
      (sections k l E).mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((complexInsertion k h l E r (P.u r)).app M)) ∧
  (∀ (m : ℕ) (C : coefficientSequenceDerived l E (Spec (.of k))),
    (P.I (m + 1)).app C = (P.I m).app C ≫
      (P.I 0).app ((G k h l E m).mapDerivedCategory.obj C) ≫
      (sections k l E).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompNatIso (P.t m)).hom.app C))

```

## New

The exact declarations above and their private helpers reside in
lean/Sheaf/Paper/PointSystemInsertionData.lean. The original module adds:

```lean
public import Sheaf.Paper.PointSystemInsertionData
```

Every original public import is retained. All namespaces, universes, binder types,
attributes and definition bodies remain identical. The original theorem keeps its
signature. Two new public theorem modules state strictly smaller sheaf-level steps;
the coefficient and derived arguments remain proved in the original module.

## Users

The complete transitive importer inventory from tools/downstream.py is the following
single module. It only imports the original module and does not mention the moved
PointSystemInsertion names. The public re-export preserves its complete interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointSystemInsertionComposition | R1 | Re-export identical constructions and prove theorem from two sheaf steps. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Identical imported interface; no adaptation. |

## Status

landed 20261026T070715-L-3644835 2026-10-26 (merge of deliver/R1/Sheaf.Paper.PointSystemInsertionComposition)
