# Semilinear exchange descent predicate module

## Reason

The assigned assembly theorem needs isomorphismExchangeScalarRefinementDescent.
That theorem publicly imports the assigned module solely for six predicate definitions,
so importing it back creates a cycle. Move the six existing definitions into
Sheaf.Paper.SemilinearExchangeDescentData. Publicly re-export this new module from the
original module and change scalar descent's import to the definition module. No name, universe, binder or public attribute changes; in particular no target changes
meaning. Four large predicates share their repeated coefficient datum using a local let.
Zeta reduction restores their exact original bodies; this prevents repeated coefficient
instance elaboration and large derived-functor comparisons. The two integral predicates
retained in the item use the same local sharing. HasDerivedCategory.standard is marked
locally irreducible during elaboration, as in ExchangeFunctoriality. The finite
composition construction, its etale realization and derived-functor localization are
also kept locally irreducible while assembling already-stated clauses. The assembly also gives the canonical reduction-module and reduction-tower
derived-category instances priority 2000 locally, matching PurCompletedReductionReindexing.
The repeated pbcIntegralDatum is kept locally irreducible in the assembly so that
elaborating its 21-clause statement does not expand the coefficient construction.
This is an import-cycle repair, independent of compile timing.

The definition review must recheck the target meanings because these predicates occur
in their closure. The local lets zeta-reduce to the old expressions; the moved
declarations retain their names and public import availability.

The assembly node's statement, stmt_deps and statement text are unchanged (a stage-3
delivery does not change stmt_deps without a statement correction; reviewer fix). The
existing descent-definition node, owner of its six output predicates already before this
delivery (existing:true on the old module), is recorded in the assembly's proof_deps and
in the uses of its fifth step.

The six moved docstring blueprint tags now name their existing definition-owner node,
def-pur-semilinear-exchange-descent-data, instead of the assembly lemma node.

The scalar-descent module is unclaimed in the current claim records. It has no downstream
importers in the baseline. The new module is owned by the existing definition node
`def-pur-semilinear-exchange-descent-data`; no new definition node is invented.

## Old

In `Sheaf.Paper.SemilinearExchangeReindexing`:

```lean
@[irreducible] def PurSemilinearRefinement (P : PurityFiniteSetting.{u}) : Prop :=
  (∀  {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
      (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
      (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g g)
      (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i gb₁)
      (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g g)
      (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i gb₂)
      (u : c₁.Refinement c₂) (u' : c₁'.Refinement c₂')
      (_hu : u'.hom ≫ gb₂ = gb₁ ≫ u.hom)
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l P.extension)) (ha : Ideal.span
      (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a
      ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum P.coefficients.l P.extension)
      K.obj),
  ((pbcIntegralDatum P.coefficients.l P.extension).completedPull g).map (cbcRefinementMap
      (pbcIntegralDatum P.coefficients.l P.extension) u K.obj) ≫
          cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) c₁ c₁' gb₁ sp₁ sj₁ r a ha K =
        cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) c₂ c₂' gb₂ sp₂ sj₂ r a ha K ≫
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) (qf :=
      cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
            u' (((pbcIntegralDatum P.coefficients.l P.extension).completedPull g').obj K.obj))
  ∧ (∀  {X Y : Scheme.{u}} {f : X ⟶ Y}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l P.extension)) (ha : Ideal.span
      (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a
      ha).FullSubcategory)
      (origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum P.coefficients.l P.extension)
      K.obj),
  (∀ (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
        (H : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a
      ha).FullSubcategory) (k : K.obj ⟶ H.obj),
        (cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c₂).map k ≫ cbcRefinementMap
      (pbcIntegralDatum P.coefficients.l P.extension) u H.obj =
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) u K.obj ≫ (cbcSupport
      (pbcIntegralDatum P.coefficients.l P.extension) c₁).map k) ∧
      (∀ c : Compactification f,
        cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension)
      (Compactification.Refinement.id c) K.obj = 𝟙 _) ∧
      (∀ (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃),
        cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) (u.comp v) K.obj =
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) v K.obj ≫
      cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) u K.obj) ∧
      (∀ (c₀ c₀' c₁ c₂ : Compactification f)
        (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
        (v₁ : c₀'.Refinement c₁) (v₂ : c₀'.Refinement c₂),
        cbcCompactificationComparison (pbcIntegralDatum P.coefficients.l P.extension) u₁ u₂ r a ha
      K origins =
          cbcCompactificationComparison (pbcIntegralDatum P.coefficients.l P.extension) v₁ v₂ r a
      ha K origins) ∧
      (∀ (c₀ c₁ c₂ c₃ : Compactification f)
        (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂) (u₃ : c₀.Refinement c₃),
        cbcCompactificationComparison (pbcIntegralDatum P.coefficients.l P.extension) u₁ u₂ r a ha
      K origins ≪≫
            cbcCompactificationComparison (pbcIntegralDatum P.coefficients.l P.extension) u₂ u₃ r
      a ha K origins =
          cbcCompactificationComparison (pbcIntegralDatum P.coefficients.l P.extension) u₁ u₃ r a
      ha K origins))
  ∧ (∀  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [Z.Over (Spec (.of P.field.k))]
      [IsSeparated (Z ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      [h.IsOver (Spec (.of P.field.k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (cf₁ cf₂ : Compactification f) (ch₁ ch₂ : Compactification h)
      (chf₁ chf₂ : Compactification (f ≫ h))
      (b₁ : cf₁.Z ⟶ chf₁.Z) (p₁ : chf₁.Z ⟶ ch₁.Z)
      (b₂ : cf₂.Z ⟶ chf₂.Z) (p₂ : chf₂.Z ⟶ ch₂.Z)
      [IsProper p₁]
      [IsProper p₂]
      (hb₁ : cf₁.i ≫ b₁ = chf₁.i) (hp₁ : b₁ ≫ p₁ = cf₁.g ≫ ch₁.i)
      (hq₁ : p₁ ≫ ch₁.g = chf₁.g)
      (hb₂ : cf₂.i ≫ b₂ = chf₂.i) (hp₂ : b₂ ≫ p₂ = cf₂.g ≫ ch₂.i)
      (hq₂ : p₂ ≫ ch₂.g = chf₂.g)
      (sq₁ : IsPullback b₁ cf₁.g p₁ ch₁.i) (sq₂ : IsPullback b₂ cf₂.g p₂ ch₂.i)
      (uf : cf₁.Refinement cf₂) (uh : ch₁.Refinement ch₂) (uhf : chf₁.Refinement chf₂)
      (_wb : uf.hom ≫ b₂ = b₁ ≫ uhf.hom) (_wp : uhf.hom ≫ p₂ = p₁ ≫ uh.hom)
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l P.extension)) (ha : Ideal.span
      (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a
      ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum P.coefficients.l P.extension)
      K.obj),
  cbcTowerCompositionMap (pbcIntegralDatum P.coefficients.l P.extension) cf₂ ch₂ chf₂ b₂ p₂ hb₂
      hp₂ hq₂ sq₂ K.obj ≫
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) uhf K.obj =
        (cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) ch₂).map (cbcRefinementMap
      (pbcIntegralDatum P.coefficients.l P.extension) uf K.obj) ≫
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l P.extension) uh ((cbcSupport
      (pbcIntegralDatum P.coefficients.l P.extension) cf₁).obj K.obj) ≫
            cbcTowerCompositionMap (pbcIntegralDatum P.coefficients.l P.extension) cf₁ ch₁ chf₁ b₁
      p₁ hb₁ hp₁ hq₁ sq₁ K.obj)

@[irreducible] def PurSemilinearRational (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb),
    ∃ (hS : ∀ K : PbcBoundedConstructibleComplete X
          (pbcIntegralDatum P.coefficients.l P.extension),
        PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum P.coefficients.l P.extension)
          ((cbcCompactSupportSource g c (pbcIntegralDatum P.coefficients.l P.extension)).obj
            K.obj))
      (hT : ∀ K : PbcBoundedConstructibleComplete X
          (pbcIntegralDatum P.coefficients.l P.extension),
        PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum P.coefficients.l P.extension)
          ((cbcCompactSupportTarget g' c' (pbcIntegralDatum P.coefficients.l P.extension)).obj
            K.obj)),
      ∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum P.coefficients.l P.extension))
        (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
        (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
        (hc : cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a ha K.obj),
      ∃ e : ((pbcIntegralDatum P.coefficients.l P.extension).completedPull g).obj
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj) ≅
        ((pbcIntegralDatum P.coefficients.l P.extension).pull g).obj
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj),
        e.inv = (pbcIntegralDatum P.coefficients.l P.extension).ordinaryToCompleted g
            ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj) ∧
        LiftedCbc.finiteExtensionCompactSupportExchangeComponent P.coefficients.l P.extension
            c c' gb sp sj r a ha hS hT K hc =
          LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension (hS K) (hT K)
            (e.hom ≫
              (PurReindexing.purIntegralReindexingExchange (pbcIntegralDatum P.coefficients.l
      P.extension)
                c c' gb sp sj).app K.obj ≫
              (cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c').map
                ((pbcIntegralDatum P.coefficients.l P.extension).ordinaryToCompleted g' K.obj))

@[irreducible] def PurSemilinearCommonStage (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      [IsNoetherian X] [IsNoetherian Y']
      [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
      [iX : Fact (∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x))]
      [_dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
      [_iY' : Fact (∀ y : Y', IsUnit (P.coefficients.l : Y'.presheaf.stalk y))],
    Nonempty (CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar c c' gb sp sj) ∧
    ∀ D : CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar c c' gb sp sj,
      (∀ K : pbcQbarCategory P.coefficients.l P.coefficients.Qbar X,
        IsIso ((StageSystem.Morphism.descNatTrans D.exchange).app K)) ∧
      (∀ (E : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar)
        (K : pbcIntegralStage P.coefficients.l P.coefficients.Qbar X E),
        ∃ e : ((pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).completedPull g).obj
            ((cbcSupport (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E) c).obj K.obj) ≅
          ((pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).pull g).obj
            ((cbcSupport (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E) c).obj K.obj),
          e.inv = (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).ordinaryToCompleted g
              ((cbcSupport (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E) c).obj
                K.obj) ∧
          HEq ((D.exchange.τ E).app
              ((pbcStageLocalization P.coefficients.l P.coefficients.Qbar X E).obj K))
            ((pbcStageLocalization P.coefficients.l P.coefficients.Qbar Y' E).map
              (ObjectProperty.homMk
                (X := ⟨_, D.presSource E K⟩) (Y := ⟨_, D.presTarget E K⟩)
                (e.hom ≫
                  (PurReindexing.purIntegralReindexingExchange
                    (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E)
                    c c' gb sp sj).app K.obj ≫
                  (cbcSupport (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E) c').map
                    ((pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).ordinaryToCompleted
                      g' K.obj))))) ∧
      ∀ (K : pbcQbarCategory P.coefficients.l P.coefficients.Qbar X)
        (M : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar)
        (h : K.stage ≤ M),
        (StageSystem.Morphism.descNatTrans D.exchange).app K =
          StageSystem.PairCategory.mkHom
            (X := D.U.base.functor.obj K) (Y := D.V.base.functor.obj K) M h h
            ((D.U.base.β h).hom.app K.obj ≫
              (D.exchange.τ M).app
                (((pbcScalarSystem P.coefficients.l P.coefficients.Qbar X dX.out iX.out).T h).obj
                  K.obj) ≫ (D.V.base.β h).inv.app K.obj)

@[irreducible] def PurSemilinearScalar (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      [IsNoetherian X] [IsNoetherian Y']
      [_dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
      [_iX : Fact (∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x))]
      [_dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
      [_iY' : Fact (∀ y : Y', IsUnit (P.coefficients.l : Y'.presheaf.stalk y))],
    ∀ (D : CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar c c' gb sp sj)
      (E F : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar) (h : E ≤ F)
      (K : pbcIntegralStage P.coefficients.l P.coefficients.Qbar X E)
      (rE : ℕ) (aE : Fin rE → PbcIntegralRing P.coefficients.l
        (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E))
      (haE : Ideal.span (Set.range aE) =
        (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).ideal)
      (hcE : cbcCompleteProperty (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E)
        X rE aE haE K.obj)
      (rF : ℕ) (aF : Fin rF → PbcIntegralRing P.coefficients.l
        (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar F))
      (haF : Ideal.span (Set.range aF) =
        (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar F).ideal),
    ∃ hcF : cbcCompleteProperty (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar F)
        X rF aF haF
        ((pbcEmbeddingAmbientTensor P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E)
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar F)
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) X).obj K.obj),
      completedCompactSupportExchange
          (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar F)
          c c' gb sp sj rF aF haF ⟨_, hcF⟩ ≫
        cbcScalarTargetInverse P.coefficients.l _ _
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) g' c'
          (D.scalarPull'.map h) K.obj =
      cbcScalarSourceInverse P.coefficients.l _ _
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) g c
          (D.scalarPull.map h) K.obj ≫
        (pbcEmbeddingAmbientTensor P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E)
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar F)
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) Y').map
            (completedCompactSupportExchange
              (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E)
              c c' gb sp sj rE aE haE ⟨K.obj, hcE⟩)

@[irreducible] def PurSemilinearFiniteCompactComparison (P : PurityFiniteSetting.{u}) : Prop :=
  (∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f]
      [IsIso g] [IsIso g'] [HasCompactification f] [HasCompactification f']
      [QuasiCompact f] [QuasiCompact f'] (sq : IsPullback g' f' f g) (c : Compactification f),
  (Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).lowerShriekBaseChange sq =
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1}
      P.Coefficient)).shriekBaseChangeOfIsPullback sq
      c).whiskerTop
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).shriekIso
      (HasCompactification.compactification f) c).hom).whiskerBottom
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).shriekIso _
      (HasCompactification.compactification f')).hom)

@[irreducible] def PurSemilinearRationalCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  (∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (_hX : CbcFiniteExtensionDomain P.coefficients.l X) (_hY : CbcFiniteExtensionDomain
      P.coefficients.l Y)
      (c : Compactification f)
      (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
      (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum P.coefficients.l P.extension)),
  ∃ (_hK : (pbcIntegralDatum P.coefficients.l P.extension).TowerComplete X K.obj)
        (hF : (pbcIntegralDatum P.coefficients.l P.extension).TowerComplete Y
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum P.coefficients.l P.extension)
          (((pbcIntegralDatum P.coefficients.l P.extension).completedPull (𝟙 Y)).obj
            ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj)))
        (hT : PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum P.coefficients.l P.extension)
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj)),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) c c (𝟙 c.Z) sp sj r a ha
              ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩ ≫
            (cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).map
              ((pbcIntegralDatum P.coefficients.l P.extension).completedPullId X K.obj _hK).hom) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          ((pbcIntegralDatum P.coefficients.l P.extension).completedPullId Y
            ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj) hF).hom)
  ∧ (∀ {X X' X'' Y Y' Y'' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsIso g] [IsIso g'] [IsIso h] [IsIso h']
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (_hX : CbcFiniteExtensionDomain P.coefficients.l X) (_hX' : CbcFiniteExtensionDomain
      P.coefficients.l X')
      (_hX'' : CbcFiniteExtensionDomain P.coefficients.l X'') (_hY : CbcFiniteExtensionDomain
      P.coefficients.l Y)
      (_hY' : CbcFiniteExtensionDomain P.coefficients.l Y') (_hY'' : CbcFiniteExtensionDomain
      P.coefficients.l Y'')
      (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
      (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
      (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
      (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
      (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
      (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
      (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
      (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum P.coefficients.l P.extension)),
  ∃ (_hK' : cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X' r a ha
          (((pbcIntegralDatum P.coefficients.l P.extension).completedPull g').obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Y'' (pbcIntegralDatum P.coefficients.l P.extension)
          (((pbcIntegralDatum P.coefficients.l P.extension).completedPull (h ≫ g)).obj
            ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj)))
        (hT : PbcIsBoundedConstructibleComplete Y'' (pbcIntegralDatum P.coefficients.l P.extension)
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c'').obj
            (((pbcIntegralDatum P.coefficients.l P.extension).completedPull (h' ≫ g')).obj K.obj))),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) c c'' (hb ≫ gb) sp sj r a ha
            ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (((pbcIntegralDatum P.coefficients.l P.extension).completedPullComp h g).hom.app
              ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj) ≫
            ((pbcIntegralDatum P.coefficients.l P.extension).completedPull h).map
              (cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) c c' gb sp₁ sj₁ r a ha
                ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) ≫
            cbcExchange (pbcIntegralDatum P.coefficients.l P.extension)
              (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
              c' c'' hb sp₂ sj₂ r a ha
              ⟨((pbcIntegralDatum P.coefficients.l P.extension).completedPull g').obj K.obj, _hK'⟩ ≫
            (cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c'').map
              (((pbcIntegralDatum P.coefficients.l P.extension).completedPullComp h' g').inv.app
      K.obj)))
  ∧ (∀ {X X' Y Y' Z Z' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
      {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsIso gx] [IsIso gy] [IsIso gz]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [Z.Over (Spec (.of P.field.k))]
      [IsSeparated (Z ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      [h.IsOver (Spec (.of P.field.k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (_hX : CbcFiniteExtensionDomain P.coefficients.l X) (_hX' : CbcFiniteExtensionDomain
      P.coefficients.l X')
      (_hY : CbcFiniteExtensionDomain P.coefficients.l Y) (_hY' : CbcFiniteExtensionDomain
      P.coefficients.l Y')
      (_hZ : CbcFiniteExtensionDomain P.coefficients.l Z) (_hZ' : CbcFiniteExtensionDomain
      P.coefficients.l Z')
      (cf : Compactification f) (ch : Compactification h)
      (chf : Compactification (f ≫ h))
      (cf' : Compactification f') (ch' : Compactification h')
      (chf' : Compactification (f' ≫ h'))
      (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
      (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
      (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
      (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
      (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
      (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
      (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
      (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
      (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
      [IsProper p] [IsProper p']
      (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
      (hq : p ≫ ch.g = chf.g)
      (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
      (hq' : p' ≫ ch'.g = chf'.g)
      (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
      (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum P.coefficients.l P.extension)),
  ∃ (hF : cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) Y r a ha
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) cf).obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Z' (pbcIntegralDatum P.coefficients.l P.extension)
          (((pbcIntegralDatum P.coefficients.l P.extension).completedPull gz).obj
            ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) ch).obj
              ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) cf).obj K.obj))))
        (hT : PbcIsBoundedConstructibleComplete Z' (pbcIntegralDatum P.coefficients.l P.extension)
          ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) chf').obj
            (((pbcIntegralDatum P.coefficients.l P.extension).completedPull gx).obj K.obj))),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (((pbcIntegralDatum P.coefficients.l P.extension).completedPull gz).map
              (cbcTowerCompositionMap (pbcIntegralDatum P.coefficients.l P.extension)
                cf ch chf b p hb hp hq sq K.obj) ≫
            cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) chf chf' gbhf sphf sjhf r
      a ha
              ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) ch ch' gbh sph sjh r a ha
              ⟨(cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) cf).obj K.obj, hF⟩ ≫
            (cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) ch').map
              (cbcExchange (pbcIntegralDatum P.coefficients.l P.extension) cf cf' gbf spf sjf r a ha
                ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) ≫
            cbcTowerCompositionMap (pbcIntegralDatum P.coefficients.l P.extension)
              (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
              cf' ch' chf' b' p' hb' hp' hq' sq'
              (((pbcIntegralDatum P.coefficients.l P.extension).completedPull gx).obj K.obj)))
```

The scalar consumer has:

```lean
public import Sheaf.Paper.SemilinearExchangeReindexing
```

The retained integral predicates in `Sheaf.Paper.SemilinearExchangeReindexing`:

```lean
@[irreducible] def PurSemilinearCompletedReindexing (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (T' T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
      [IsSeparated (T ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
      [QuasiCompact (T ↘ Spec (.of P.field.k))] (g : T' ⟶ T) [IsIso g],
    PurReindexing.PurCompletedReindexingAt (pbcIntegralDatum P.coefficients.l P.extension) g

@[irreducible] def PurSemilinearIntegralIsomorphism (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb),
    PurReindexing.PurCompletedReindexingSquare (pbcIntegralDatum P.coefficients.l P.extension) sp ∧
    ∀ (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension)
        X r a ha).FullSubcategory),
      IsIso (completedCompactSupportExchange (pbcIntegralDatum P.coefficients.l P.extension)
        c c' gb sp sj r a ha K)
```

## New

In `Sheaf.Paper.SemilinearExchangeDescentData`:

```lean
@[irreducible] def PurSemilinearRefinement (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  (∀  {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
      (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
      (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g g)
      (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i gb₁)
      (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g g)
      (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i gb₂)
      (u : c₁.Refinement c₂) (u' : c₁'.Refinement c₂')
      (_hu : u'.hom ≫ gb₂ = gb₁ ≫ u.hom)
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l P.extension)) (ha : Ideal.span
      (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a
      ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d
      K.obj),
  (d.completedPull g).map (cbcRefinementMap
      d u K.obj) ≫
          cbcExchange d c₁ c₁' gb₁ sp₁ sj₁ r a ha K =
        cbcExchange d c₂ c₂' gb₂ sp₂ sj₂ r a ha K ≫
          cbcRefinementMap d (qf :=
      cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
            u' ((d.completedPull g').obj K.obj))
  ∧ (∀  {X Y : Scheme.{u}} {f : X ⟶ Y}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l P.extension)) (ha : Ideal.span
      (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a
      ha).FullSubcategory)
      (origins : PbcHasCompatibleEtaleOrigins X d
      K.obj),
  (∀ (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
        (H : (cbcCompleteProperty d X r a
      ha).FullSubcategory) (k : K.obj ⟶ H.obj),
        (cbcSupport d c₂).map k ≫ cbcRefinementMap
      d u H.obj =
          cbcRefinementMap d u K.obj ≫ (cbcSupport
      d c₁).map k) ∧
      (∀ c : Compactification f,
        cbcRefinementMap d
      (Compactification.Refinement.id c) K.obj = 𝟙 _) ∧
      (∀ (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃),
        cbcRefinementMap d (u.comp v) K.obj =
          cbcRefinementMap d v K.obj ≫
      cbcRefinementMap d u K.obj) ∧
      (∀ (c₀ c₀' c₁ c₂ : Compactification f)
        (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
        (v₁ : c₀'.Refinement c₁) (v₂ : c₀'.Refinement c₂),
        cbcCompactificationComparison d u₁ u₂ r a ha
      K origins =
          cbcCompactificationComparison d v₁ v₂ r a
      ha K origins) ∧
      (∀ (c₀ c₁ c₂ c₃ : Compactification f)
        (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂) (u₃ : c₀.Refinement c₃),
        cbcCompactificationComparison d u₁ u₂ r a ha
      K origins ≪≫
            cbcCompactificationComparison d u₂ u₃ r
      a ha K origins =
          cbcCompactificationComparison d u₁ u₃ r a
      ha K origins))
  ∧ (∀  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [Z.Over (Spec (.of P.field.k))]
      [IsSeparated (Z ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      [h.IsOver (Spec (.of P.field.k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (cf₁ cf₂ : Compactification f) (ch₁ ch₂ : Compactification h)
      (chf₁ chf₂ : Compactification (f ≫ h))
      (b₁ : cf₁.Z ⟶ chf₁.Z) (p₁ : chf₁.Z ⟶ ch₁.Z)
      (b₂ : cf₂.Z ⟶ chf₂.Z) (p₂ : chf₂.Z ⟶ ch₂.Z)
      [IsProper p₁]
      [IsProper p₂]
      (hb₁ : cf₁.i ≫ b₁ = chf₁.i) (hp₁ : b₁ ≫ p₁ = cf₁.g ≫ ch₁.i)
      (hq₁ : p₁ ≫ ch₁.g = chf₁.g)
      (hb₂ : cf₂.i ≫ b₂ = chf₂.i) (hp₂ : b₂ ≫ p₂ = cf₂.g ≫ ch₂.i)
      (hq₂ : p₂ ≫ ch₂.g = chf₂.g)
      (sq₁ : IsPullback b₁ cf₁.g p₁ ch₁.i) (sq₂ : IsPullback b₂ cf₂.g p₂ ch₂.i)
      (uf : cf₁.Refinement cf₂) (uh : ch₁.Refinement ch₂) (uhf : chf₁.Refinement chf₂)
      (_wb : uf.hom ≫ b₂ = b₁ ≫ uhf.hom) (_wp : uhf.hom ≫ p₂ = p₁ ≫ uh.hom)
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l P.extension)) (ha : Ideal.span
      (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a
      ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d
      K.obj),
  cbcTowerCompositionMap d cf₂ ch₂ chf₂ b₂ p₂ hb₂
      hp₂ hq₂ sq₂ K.obj ≫
          cbcRefinementMap d uhf K.obj =
        (cbcSupport d ch₂).map (cbcRefinementMap
      d uf K.obj) ≫
          cbcRefinementMap d uh ((cbcSupport
      d cf₁).obj K.obj) ≫
            cbcTowerCompositionMap d cf₁ ch₁ chf₁ b₁
      p₁ hb₁ hp₁ hq₁ sq₁ K.obj)


/-- The raw rational exchange is the localized, ordered reindexing composite.
The inverse of e is the specified quotient completion unit, so e is uniquely fixed.
The preservation witnesses are conclusions, and the tuple is any finite generating tuple.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearRational (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb),
    ∃ (hS : ∀ K : PbcBoundedConstructibleComplete X
          d,
        PbcIsBoundedConstructibleComplete Y' d
          ((cbcCompactSupportSource g c d).obj
            K.obj))
      (hT : ∀ K : PbcBoundedConstructibleComplete X
          d,
        PbcIsBoundedConstructibleComplete Y' d
          ((cbcCompactSupportTarget g' c' d).obj
            K.obj)),
      ∀ (K : PbcBoundedConstructibleComplete X d)
        (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
        (ha : Ideal.span (Set.range a) = d.ideal)
        (hc : cbcCompleteProperty d X r a ha K.obj),
      ∃ e : (d.completedPull g).obj
          ((cbcSupport d c).obj K.obj) ≅
        (d.pull g).obj
          ((cbcSupport d c).obj K.obj),
        e.inv = d.ordinaryToCompleted g
            ((cbcSupport d c).obj K.obj) ∧
        LiftedCbc.finiteExtensionCompactSupportExchangeComponent P.coefficients.l P.extension
            c c' gb sp sj r a ha hS hT K hc =
          LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension (hS K) (hT K)
            (e.hom ≫
              (PurReindexing.purIntegralReindexingExchange d
                c c' gb sp sj).app K.obj ≫
              (cbcSupport d c').map
                (d.ordinaryToCompleted g' K.obj))


/-- The canonical common-stage exchange is the image of the integral reindexing
identity at every finite stage. A normalized model is supplied as a conclusion; every
normalized model has the same ordered identity. Its scalar beta maps retain the identity
and field-tower cocycles, and its descent retains every common overfield representative.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearCommonStage (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      [IsNoetherian X] [IsNoetherian Y']
      [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
      [iX : Fact (∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x))]
      [_dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
      [_iY' : Fact (∀ y : Y', IsUnit (P.coefficients.l : Y'.presheaf.stalk y))],
    Nonempty (CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar c c' gb sp sj) ∧
    ∀ D : CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar c c' gb sp sj,
      (∀ K : pbcQbarCategory P.coefficients.l P.coefficients.Qbar X,
        IsIso ((StageSystem.Morphism.descNatTrans D.exchange).app K)) ∧
      (∀ (E : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar)
        (K : pbcIntegralStage P.coefficients.l P.coefficients.Qbar X E),
        let d := pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E
        ∃ e : (d.completedPull g).obj
            ((cbcSupport d c).obj K.obj) ≅
          (d.pull g).obj
            ((cbcSupport d c).obj K.obj),
          e.inv = d.ordinaryToCompleted g
              ((cbcSupport d c).obj
                K.obj) ∧
          HEq ((D.exchange.τ E).app
              ((pbcStageLocalization P.coefficients.l P.coefficients.Qbar X E).obj K))
            ((pbcStageLocalization P.coefficients.l P.coefficients.Qbar Y' E).map
              (ObjectProperty.homMk
                (X := ⟨_, D.presSource E K⟩) (Y := ⟨_, D.presTarget E K⟩)
                (e.hom ≫
                  (PurReindexing.purIntegralReindexingExchange
                    d
                    c c' gb sp sj).app K.obj ≫
                  (cbcSupport d c').map
                    (d.ordinaryToCompleted
                      g' K.obj))))) ∧
      ∀ (K : pbcQbarCategory P.coefficients.l P.coefficients.Qbar X)
        (M : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar)
        (h : K.stage ≤ M),
        (StageSystem.Morphism.descNatTrans D.exchange).app K =
          StageSystem.PairCategory.mkHom
            (X := D.U.base.functor.obj K) (Y := D.V.base.functor.obj K) M h h
            ((D.U.base.β h).hom.app K.obj ≫
              (D.exchange.τ M).app
                (((pbcScalarSystem P.coefficients.l P.coefficients.Qbar X dX.out iX.out).T h).obj
                  K.obj) ≫ (D.V.base.β h).inv.app K.obj)


/-- The supplied unit-normalized common-stage scalar comparisons intertwine
the actual integral exchange. Equal and proper finite coefficient extensions are
included. These maps are fixed by the completed-pullback unit, proper counit and
open unit in CbcQbarExchangeModel; none is an arbitrary comparison.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearScalar (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      [IsNoetherian X] [IsNoetherian Y']
      [_dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
      [_iX : Fact (∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x))]
      [_dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
      [_iY' : Fact (∀ y : Y', IsUnit (P.coefficients.l : Y'.presheaf.stalk y))],
    ∀ (D : CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar c c' gb sp sj)
      (E F : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar) (h : E ≤ F)
      (K : pbcIntegralStage P.coefficients.l P.coefficients.Qbar X E)
      (rE : ℕ) (aE : Fin rE → PbcIntegralRing P.coefficients.l
        (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E))
      (haE : Ideal.span (Set.range aE) =
        (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).ideal)
      (hcE : cbcCompleteProperty (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E)
        X rE aE haE K.obj)
      (rF : ℕ) (aF : Fin rF → PbcIntegralRing P.coefficients.l
        (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar F))
      (haF : Ideal.span (Set.range aF) =
        (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar F).ideal),
    ∃ hcF : cbcCompleteProperty (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar F)
        X rF aF haF
        ((pbcEmbeddingAmbientTensor P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E)
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar F)
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) X).obj K.obj),
      completedCompactSupportExchange
          (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar F)
          c c' gb sp sj rF aF haF ⟨_, hcF⟩ ≫
        cbcScalarTargetInverse P.coefficients.l _ _
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) g' c'
          (D.scalarPull'.map h) K.obj =
      cbcScalarSourceInverse P.coefficients.l _ _
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) g c
          (D.scalarPull.map h) K.obj ≫
        (pbcEmbeddingAmbientTensor P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E)
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar F)
          (pbcFiniteFieldInclusion P.coefficients.l P.coefficients.Qbar h) Y').map
            (completedCompactSupportExchange
              (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E)
              c c' gb sp sj rE aE haE ⟨K.obj, hcE⟩)


/-- The finite chosen-compactification exchange inserted into the canonical
compactification-independent comparison, on the retained field-base domain.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearFiniteCompactComparison (P : PurityFiniteSetting.{u}) : Prop :=
  (∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f]
      [IsIso g] [IsIso g'] [HasCompactification f] [HasCompactification f']
      [QuasiCompact f] [QuasiCompact f'] (sq : IsPullback g' f' f g) (c : Compactification f),
  (Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).lowerShriekBaseChange sq =
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1}
      P.Coefficient)).shriekBaseChangeOfIsPullback sq
      c).whiskerTop
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).shriekIso
      (HasCompactification.compactification f) c).hom).whiskerBottom
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).shriekIso _
      (HasCompactification.compactification f')).hom)


/-- Identity and both pasting laws after scalar localization, written as
equalities between the images of the two actual ordered integral paths. All
constructibility endpoints and canonical composition maps are retained.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearRationalCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  (∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (_hX : CbcFiniteExtensionDomain P.coefficients.l X) (_hY : CbcFiniteExtensionDomain
      P.coefficients.l Y)
      (c : Compactification f)
      (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
      (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (K : PbcBoundedConstructibleComplete X d),
  ∃ (_hK : d.TowerComplete X K.obj)
        (hF : d.TowerComplete Y
          ((cbcSupport d c).obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Y d
          ((d.completedPull (𝟙 Y)).obj
            ((cbcSupport d c).obj K.obj)))
        (hT : PbcIsBoundedConstructibleComplete Y d
          ((cbcSupport d c).obj K.obj)),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (cbcExchange d c c (𝟙 c.Z) sp sj r a ha
              ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩ ≫
            (cbcSupport d c).map
              (d.completedPullId X K.obj _hK).hom) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (d.completedPullId Y
            ((cbcSupport d c).obj K.obj) hF).hom)
  ∧ (∀ {X X' X'' Y Y' Y'' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsIso g] [IsIso g'] [IsIso h] [IsIso h']
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (_hX : CbcFiniteExtensionDomain P.coefficients.l X) (_hX' : CbcFiniteExtensionDomain
      P.coefficients.l X')
      (_hX'' : CbcFiniteExtensionDomain P.coefficients.l X'') (_hY : CbcFiniteExtensionDomain
      P.coefficients.l Y)
      (_hY' : CbcFiniteExtensionDomain P.coefficients.l Y') (_hY'' : CbcFiniteExtensionDomain
      P.coefficients.l Y'')
      (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
      (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
      (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
      (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
      (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
      (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
      (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
      (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (K : PbcBoundedConstructibleComplete X d),
  ∃ (_hK' : cbcCompleteProperty d X' r a ha
          ((d.completedPull g').obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Y'' d
          ((d.completedPull (h ≫ g)).obj
            ((cbcSupport d c).obj K.obj)))
        (hT : PbcIsBoundedConstructibleComplete Y'' d
          ((cbcSupport d c'').obj
            ((d.completedPull (h' ≫ g')).obj K.obj))),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (cbcExchange d c c'' (hb ≫ gb) sp sj r a ha
            ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          ((d.completedPullComp h g).hom.app
              ((cbcSupport d c).obj K.obj) ≫
            (d.completedPull h).map
              (cbcExchange d c c' gb sp₁ sj₁ r a ha
                ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) ≫
            cbcExchange d
              (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
              c' c'' hb sp₂ sj₂ r a ha
              ⟨(d.completedPull g').obj K.obj, _hK'⟩ ≫
            (cbcSupport d c'').map
              ((d.completedPullComp h' g').inv.app
      K.obj)))
  ∧ (∀ {X X' Y Y' Z Z' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
      {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsIso gx] [IsIso gy] [IsIso gz]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [Z.Over (Spec (.of P.field.k))]
      [IsSeparated (Z ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      [h.IsOver (Spec (.of P.field.k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (_hX : CbcFiniteExtensionDomain P.coefficients.l X) (_hX' : CbcFiniteExtensionDomain
      P.coefficients.l X')
      (_hY : CbcFiniteExtensionDomain P.coefficients.l Y) (_hY' : CbcFiniteExtensionDomain
      P.coefficients.l Y')
      (_hZ : CbcFiniteExtensionDomain P.coefficients.l Z) (_hZ' : CbcFiniteExtensionDomain
      P.coefficients.l Z')
      (cf : Compactification f) (ch : Compactification h)
      (chf : Compactification (f ≫ h))
      (cf' : Compactification f') (ch' : Compactification h')
      (chf' : Compactification (f' ≫ h'))
      (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
      (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
      (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
      (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
      (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
      (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
      (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
      (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
      (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
      [IsProper p] [IsProper p']
      (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
      (hq : p ≫ ch.g = chf.g)
      (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
      (hq' : p' ≫ ch'.g = chf'.g)
      (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
      (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (K : PbcBoundedConstructibleComplete X d),
  ∃ (hF : cbcCompleteProperty d Y r a ha
          ((cbcSupport d cf).obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Z' d
          ((d.completedPull gz).obj
            ((cbcSupport d ch).obj
              ((cbcSupport d cf).obj K.obj))))
        (hT : PbcIsBoundedConstructibleComplete Z' d
          ((cbcSupport d chf').obj
            ((d.completedPull gx).obj K.obj))),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          ((d.completedPull gz).map
              (cbcTowerCompositionMap d
                cf ch chf b p hb hp hq sq K.obj) ≫
            cbcExchange d chf chf' gbhf sphf sjhf r
      a ha
              ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hS hT
          (cbcExchange d ch ch' gbh sph sjh r a ha
              ⟨(cbcSupport d cf).obj K.obj, hF⟩ ≫
            (cbcSupport d ch').map
              (cbcExchange d cf cf' gbf spf sjf r a ha
                ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l P.extension X K r a
      ha⟩) ≫
            cbcTowerCompositionMap d
              (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
              cf' ch' chf' b' p' hb' hp' hq' sq'
              ((d.completedPull gx).obj K.obj)))
```

The original module publicly imports this definition module. The scalar-descent module
replaces its public import of the original module with this definition module.

The retained integral predicates in `Sheaf.Paper.SemilinearExchangeReindexing`:

```lean
@[irreducible] def PurSemilinearCompletedReindexing (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  ∀ (T' T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
      [IsSeparated (T ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
      [QuasiCompact (T ↘ Spec (.of P.field.k))] (g : T' ⟶ T) [IsIso g],
    PurReindexing.PurCompletedReindexingAt d g

@[irreducible] def PurSemilinearIntegralIsomorphism (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb),
    PurReindexing.PurCompletedReindexingSquare d sp ∧
    ∀ (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d
        X r a ha).FullSubcategory),
      IsIso (completedCompactSupportExchange d
        c c' gb sp sj r a ha K)
```

## Users

The source-only `tools/downstream.py Sheaf.Paper.SemilinearExchangeReindexing --uses`
check found the following complete downstream set. The six names are used only by the
assigned module and the scalar-descent module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Definitions publicly re-exported unchanged; assembly proved. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Replace one public import to break the cycle; every declaration unchanged. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed in checked records | Original import re-exports every declaration it needs; no adaptation or semantic effect. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed in checked records | Transitive import only; no moved-name use or semantic effect. |

## Status

landed 20261026T024112-L-638917 2026-10-26 (merge of deliver/U2/Sheaf.Paper.SemilinearExchangeReindexing)
