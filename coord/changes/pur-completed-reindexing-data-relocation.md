# Completed reindexing data declarations

## Reason

The four strictly smaller proof steps must import the specified concrete maps without
importing the theorem that combines them. Move the seven existing definitions
to Sheaf.Paper.PurCompletedReindexingData and publicly re-export that module from the
original module. Their names, binders, universes, types, visibility, and public import surface are
unchanged. Four bodies are verbatim. The two predicates factor their literal clauses through
named definitions. The tower-mate body passes through the generic
purWhiskerCompositeMap wrapper around the identical whiskering map. This avoids a
40-second kernel comparison after substituting the large tensor functors. This is dependency organization for the mathematical
reduction, not a split made to evade a compile limit.

## Old

The following exact source occurs in lean/Sheaf/Paper/PurCompletedReductionReindexing.lean:

```lean
/-- The two canonical routes for a test object around the commuting scheme square.
Source: Stacks Tags 09A5 and 07A7, fibre-product pasting
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingTestSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (w : v ≫ p = p' ≫ g) :
    proEtaleBaseChange g ⋙ proEtaleBaseChange p' ≅
      proEtaleBaseChange p ⋙ proEtaleBaseChange v :=
  (MorphismProperty.Over.pullbackComp p' g).symm ≪≫
    eqToIso (congrArg (fun f : X' ⟶ Y ↦ proEtaleBaseChange f) w.symm) ≪≫
      MorphismProperty.Over.pullbackComp v p

/-- The canonical completed-coefficient specialization of the ringed square.
Source: Stacks Tag 07A7, using the completed coefficient composition equations
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingRingedSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : StrictTowerRingedSquare sq where
  RY := d.completedRing Y
  RX := d.completedRing X
  RY' := d.completedRing Y'
  RX' := d.completedRing X'
  cf := d.integralRingIso p
  cg := d.integralRingIso g
  cg' := d.integralRingIso v
  cf' := d.integralRingIso p'
  coherent := d.integral_coherent sq

/-- The ordinary module mate of the specified, section-normalized pullback square.
Source: Stacks Tag 07A7; the canonical adjunctions have their tensor-unit normalization
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingModuleMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso p) ⋙ proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g) ⟶
      proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v) ⋙
        proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
          (d.integralRingIso p') :=
  (mateEquiv
    (proEtaleRingModuleAdjunction p (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso p))
    (proEtaleRingModuleAdjunction p' (d.completedRing Y') (d.completedRing X')
      (d.integralRingIso p'))
    (TwoSquare.mk _ _ _ _ (purReindexingRingedSquare d sq).exchangeModuleSquare.hom)).natTrans

/-- The actual ordinary strict-diagram mate, including every index arrow.
Source: Stacks Tag 07A7 on the ringed diagram site
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingTowerModuleMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    d.towerModulePush p ⋙ d.towerModulePull g ⟶
      d.towerModulePull v ⋙ d.towerModulePush p' :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).map (purReindexingModuleMate d sq)

/-- The specified ordinary completed-ring derived direct-image mate.
Source: Stacks Tag 07A7, with the published coherent completed coefficient maps
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingDerivedMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    d.push p ⋙ d.pull g ⟶ d.pull v ⋙ d.push p' :=
  proEtaleAmbientRingedExchange sq
    (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
    (d.integralRingIso p) (d.integralRingIso g) (d.integralRingIso v)
    (d.integralRingIso p') (d.integral_coherent sq)

/-- Exact reindexing, its reverse, its normalized limit comparison, and its strict
reduction tensor normalization. The ordinary tensor presentation is canonically
inverse image with action a.x = c inverse(a).x; no completeness restriction is imposed
on the equivalences or on the inverse-limit comparison.
Source: extracted argument, steps 1--5; Stacks Tags 09A5, 0A07, 03EL and 099N
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def PurCompletedReindexingAt {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ e : proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ⋙
        SheafOfModules.toSheaf (reductionModuleRing T' (d.completedRing T')) ≅
      SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙
        isoSectionwiseInverseImage u AddCommGrpCat.{t + 1},
    ∀ (M : reductionModules T (d.completedRing T)) (U : T'.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose u).obj U))),
      (e.inv.app M).hom.app (op U) x =
        ((proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).obj M).val.map (proEtaleIsoCommaArrow u U).op
          (((proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
            (d.integralRingIso u)).unit.app M).val.app
              (op ((proEtaleIsoPostcompose u).obj U)) x)) ∧
  (∃ e : reductionModules T (d.completedRing T) ≌
      reductionModules T' (d.completedRing T'),
    e.functor = proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ∧
    e.inverse = proEtaleRingModulePullback (inv u) (d.completedRing T')
        (d.completedRing T) (d.integralRingIso (inv u))) ∧
  PreservesFiniteLimits (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)) ∧
  PreservesFiniteColimits (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)) ∧
  (∃ e : d.towers T ≌ d.towers T',
    e.functor = d.towerModulePull u ∧ e.inverse = d.towerModulePull (inv u)) ∧
  PreservesFiniteLimits (d.towerModulePull u) ∧
  PreservesFiniteColimits (d.towerModulePull u) ∧
  (∃ e : d.derived T ≌ d.derived T',
    e.functor = d.pull u ∧ e.inverse = d.pull (inv u)) ∧
  (∃ e : DerivedCategory (d.towers T) ≌ DerivedCategory (d.towers T'),
    e.functor = d.towerPull u ∧ e.inverse = d.towerPull (inv u)) ∧
  (∃ beta : completedTowerLimit T (d.completedRing T) ⋙
      proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ≅
      d.towerModulePull u ⋙ completedTowerLimit T' (d.completedRing T'),
    (∀ (C : d.towers T) (n : ℕᵒᵖ),
      beta.hom.app C ≫ limit.π ((d.towerModulePull u).obj C) n =
        (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).map (limit.π C n)) ∧
    ∃ b : completedRlim T (d.completedRing T) ⋙ d.pull u ≅
      d.towerPull u ⋙ completedRlim T' (d.completedRing T'),
    (∀ I : CochainComplex (d.towers T) ℤ, I.IsKInjective →
      (d.pull u).map ((completedTowerLimit T (d.completedRing T)).rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        (completedRlim T' (d.completedRing T')).map
          ((d.towerModulePull u).mapDerivedCategoryFactors.hom.app I) =
      (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).mapDerivedCategoryFactors.hom.app
          (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        (completedTowerLimit T' (d.completedRing T')).rightDerivedFunctorUnitQ
          (((d.towerModulePull u).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ K : d.derived T, d.TowerComplete T K →
      ∃ e : (d.completedPull u).obj K ≅ (d.pull u).obj K,
        e.inv = d.ordinaryToCompleted u K ∧
        e.hom ≫ (d.pull u).map (d.completionUnit T K) =
          b.inv.app ((completedReductionTower T d).obj K))) ∧
  IsCompletedReductionPullbackComparison d u (d.reductionTowerPullbackIso u) ∧
  (∀ (n : ℕ) (M : reductionModules T (d.completedRing T)) (W : T.ProEtᵒᵖ)
      (x : M.val.obj W) (a : (d.finiteRing T n).obj.obj W),
    ((completedReductionLevelPullbackIso d u n).hom.app M).val.app
        ((proEtaleBaseChange u).op.obj W)
        (((proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
          (d.integralRingIso u)).unit.app ((completedReductionLevel T d n).obj M)).val.app
            W (reductionTensorSection T (d.projection T n) M W a x)) =
      reductionTensorSection T' (d.projection T' n)
        ((proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).obj M)
        ((proEtaleBaseChange u).op.obj W)
        ((proEtaleRingDirectImageMap u (d.finiteRing T n) (d.finiteRing T' n)
          (d.finiteRingIso u n)).hom.app W a)
        (((proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
          (d.integralRingIso u)).unit.app M).val.app W x)) ∧
  (∀ (M : reductionModules T (d.completedRing T)) (n m : ℕᵒᵖ) (a : n ⟶ m),
    ((completedReductionModuleTowerFunctor T d ⋙ d.towerModulePull u).obj M).map a ≫
        (completedReductionLevelPullbackIso d u m.unop).hom.app M =
      (completedReductionLevelPullbackIso d u n.unop).hom.app M ≫
        ((proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ⋙
          completedReductionModuleTowerFunctor T' d).obj M).map a)

/-- Section and K-injective normalizations of both specified direct-image mates.
The first equation is restriction along the canonical fibre-product square after
inverse-image units. Since g is an isomorphism, its base-changed tests cover all tests.
The last equations identify the derived mates on actual K-injective complexes,
including strict tower complexes, rather than merely asserting they are invertible.
Source: extracted argument, steps 6--8; Stacks Tags 07A7, 08BJ and 0FND
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def PurCompletedReindexingSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingModuleMate d sq) ∧
  IsIso (purReindexingTowerModuleMate d sq) ∧
  IsIso (purReindexingDerivedMate d sq) ∧
  IsIso (purReindexingRingedSquare d sq).exchangeTowerMate ∧
  (∀ (M : reductionModules X (d.completedRing X)) (V : Y.ProEt)
      (x : M.val.obj (op ((proEtaleBaseChange p).obj V))),
    ((purReindexingModuleMate d sq).app M).val.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing Y')
          (d.integralRingIso g)).unit.app
            ((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso p)).obj M)).val.app (op V) x) =
      ((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).obj M).val.map
        ((purReindexingTestSquare sq.w).hom.app V).op
        (((proEtaleRingModuleAdjunction v (d.completedRing X) (d.completedRing X')
          (d.integralRingIso v)).unit.app M).val.app
            (op ((proEtaleBaseChange p).obj V)) x)) ∧
  (∀ I : CochainComplex (reductionModules X (d.completedRing X)) ℤ, I.IsKInjective →
    (d.pull g).map
        ((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso p)).rightDerivedFunctorUnitQ I) ≫
      (purReindexingDerivedMate d sq).app (DerivedCategory.Q.obj I) ≫
      (d.push p').map ((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).mapDerivedCategoryFactors.hom.app I) =
    (proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g)).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso p)).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (purReindexingModuleMate d sq) (.up ℤ)).app I) ≫
      (proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
        (d.integralRingIso p')).rightDerivedFunctorUnitQ
          (((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ I : CochainComplex (d.towers X) ℤ, I.IsKInjective →
    (d.towerPull g).map ((d.towerModulePush p).rightDerivedFunctorUnitQ I) ≫
      (purReindexingRingedSquare d sq).exchangeTowerMate.app (DerivedCategory.Q.obj I) ≫
      (d.towerPush p').map ((d.towerModulePull v).mapDerivedCategoryFactors.hom.app I) =
    (d.towerModulePull g).mapDerivedCategoryFactors.hom.app
        (((d.towerModulePush p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (purReindexingTowerModuleMate d sq) (.up ℤ)).app I) ≫
      (d.towerModulePush p').rightDerivedFunctorUnitQ
        (((d.towerModulePull v).mapHomologicalComplex (.up ℤ)).obj I))

```

## New

The data are publicly re-exported from Sheaf.Paper.PurCompletedReindexingData.
All original signatures and public imports are retained. The tower mate uses a
generic wrapper around the identical whiskering map. Each clause of the two large
predicates is named separately; unfolding those names yields the old predicate
bodies verbatim. No hypothesis or equation is added or removed. This shares the
fully typed clauses between the split statements and assembly and avoids the
observed 60-133 second kernel checks of repeated specialized expressions.
No target signature or mathematical meaning changes.

The new source is:

```lean
/-- Whisker a transformation between composites, with the composite tower functors
written explicitly. This generic wrapper keeps checking away from tensor data.
Source: Mathlib Functor.whiskeringRight
(blueprint: def-pur-completed-reindexing-data). -/
def purWhiskerCompositeMap
    {J C D D' E : Type*} [Category J] [Category C] [Category D] [Category D'] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    (a : F ⋙ G ⟶ F' ⋙ G') :
    (Functor.whiskeringRight J C D).obj F ⋙ (Functor.whiskeringRight J D E).obj G ⟶
      (Functor.whiskeringRight J C D').obj F' ⋙ (Functor.whiskeringRight J D' E).obj G' :=
  (Functor.whiskeringRight J C E).map a

/-- The two canonical routes for a test object around the commuting scheme square.
Source: Stacks Tags 09A5 and 07A7, fibre-product pasting
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingTestSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (w : v ≫ p = p' ≫ g) :
    proEtaleBaseChange g ⋙ proEtaleBaseChange p' ≅
      proEtaleBaseChange p ⋙ proEtaleBaseChange v :=
  (MorphismProperty.Over.pullbackComp p' g).symm ≪≫
    eqToIso (congrArg (fun f : X' ⟶ Y ↦ proEtaleBaseChange f) w.symm) ≪≫
      MorphismProperty.Over.pullbackComp v p

/-- The canonical completed-coefficient specialization of the ringed square.
Source: Stacks Tag 07A7, using the completed coefficient composition equations
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingRingedSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : StrictTowerRingedSquare sq where
  RY := d.completedRing Y
  RX := d.completedRing X
  RY' := d.completedRing Y'
  RX' := d.completedRing X'
  cf := d.integralRingIso p
  cg := d.integralRingIso g
  cg' := d.integralRingIso v
  cf' := d.integralRingIso p'
  coherent := d.integral_coherent sq

/-- The ordinary module mate of the specified, section-normalized pullback square.
Source: Stacks Tag 07A7; the canonical adjunctions have their tensor-unit normalization
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingModuleMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso p) ⋙ proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g) ⟶
      proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v) ⋙
        proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
          (d.integralRingIso p') :=
  (mateEquiv
    (proEtaleRingModuleAdjunction p (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso p))
    (proEtaleRingModuleAdjunction p' (d.completedRing Y') (d.completedRing X')
      (d.integralRingIso p'))
    (TwoSquare.mk _ _ _ _ (purReindexingRingedSquare d sq).exchangeModuleSquare.hom)).natTrans

/-- The actual ordinary strict-diagram mate, including every index arrow.
Source: Stacks Tag 07A7 on the ringed diagram site
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingTowerModuleMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    d.towerModulePush p ⋙ d.towerModulePull g ⟶
      d.towerModulePull v ⋙ d.towerModulePush p' :=
  purWhiskerCompositeMap (J := ℕᵒᵖ) _ _ _ _ (purReindexingModuleMate d sq)

/-- The specified ordinary completed-ring derived direct-image mate.
Source: Stacks Tag 07A7, with the published coherent completed coefficient maps
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
def purReindexingDerivedMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    d.push p ⋙ d.pull g ⟶ d.pull v ⋙ d.push p' :=
  proEtaleAmbientRingedExchange sq
    (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
    (d.integralRingIso p) (d.integralRingIso g) (d.integralRingIso v)
    (d.integralRingIso p') (d.integral_coherent sq)

/- Exact reindexing, its reverse, its normalized limit comparison, and its strict
reduction tensor normalization. The ordinary tensor presentation is canonically
inverse image with action a.x = c inverse(a).x; no completeness restriction is imposed
on the equivalences or on the inverse-limit comparison.
Source: extracted argument, steps 1--5; Stacks Tags 09A5, 0A07, 03EL and 099N
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtSections {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ e : proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ⋙
        SheafOfModules.toSheaf (reductionModuleRing T' (d.completedRing T')) ≅
      SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙
        isoSectionwiseInverseImage u AddCommGrpCat.{t + 1},
    ∀ (M : reductionModules T (d.completedRing T)) (U : T'.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose u).obj U))),
      (e.inv.app M).hom.app (op U) x =
        ((proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).obj M).val.map (proEtaleIsoCommaArrow u U).op
          (((proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
            (d.integralRingIso u)).unit.app M).val.app
              (op ((proEtaleIsoPostcompose u).obj U)) x))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtModules {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ e : reductionModules T (d.completedRing T) ≌
      reductionModules T' (d.completedRing T'),
    e.functor = proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ∧
    e.inverse = proEtaleRingModulePullback (inv u) (d.completedRing T')
        (d.completedRing T) (d.integralRingIso (inv u)))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtModuleLimits {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  PreservesFiniteLimits (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtModuleColimits {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  PreservesFiniteColimits (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtTowers {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ e : d.towers T ≌ d.towers T',
    e.functor = d.towerModulePull u ∧ e.inverse = d.towerModulePull (inv u))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtTowerLimits {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  PreservesFiniteLimits (d.towerModulePull u)

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtTowerColimits {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  PreservesFiniteColimits (d.towerModulePull u)

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtDerived {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ e : d.derived T ≌ d.derived T',
    e.functor = d.pull u ∧ e.inverse = d.pull (inv u))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtDerivedTowers {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ e : DerivedCategory (d.towers T) ≌ DerivedCategory (d.towers T'),
    e.functor = d.towerPull u ∧ e.inverse = d.towerPull (inv u))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtLimit {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ beta : completedTowerLimit T (d.completedRing T) ⋙
      proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ≅
      d.towerModulePull u ⋙ completedTowerLimit T' (d.completedRing T'),
    (∀ (C : d.towers T) (n : ℕᵒᵖ),
      beta.hom.app C ≫ limit.π ((d.towerModulePull u).obj C) n =
        (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).map (limit.π C n)) ∧
    ∃ b : completedRlim T (d.completedRing T) ⋙ d.pull u ≅
      d.towerPull u ⋙ completedRlim T' (d.completedRing T'),
    (∀ I : CochainComplex (d.towers T) ℤ, I.IsKInjective →
      (d.pull u).map ((completedTowerLimit T (d.completedRing T)).rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        (completedRlim T' (d.completedRing T')).map
          ((d.towerModulePull u).mapDerivedCategoryFactors.hom.app I) =
      (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).mapDerivedCategoryFactors.hom.app
          (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        (completedTowerLimit T' (d.completedRing T')).rightDerivedFunctorUnitQ
          (((d.towerModulePull u).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ K : d.derived T, d.TowerComplete T K →
      ∃ e : (d.completedPull u).obj K ≅ (d.pull u).obj K,
        e.inv = d.ordinaryToCompleted u K ∧
        e.hom ≫ (d.pull u).map (d.completionUnit T K) =
          b.inv.app ((completedReductionTower T d).obj K)))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtReduction {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  IsCompletedReductionPullbackComparison d u (d.reductionTowerPullbackIso u)

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtTensor {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∀ (n : ℕ) (M : reductionModules T (d.completedRing T)) (W : T.ProEtᵒᵖ)
      (x : M.val.obj W) (a : (d.finiteRing T n).obj.obj W),
    ((completedReductionLevelPullbackIso d u n).hom.app M).val.app
        ((proEtaleBaseChange u).op.obj W)
        (((proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
          (d.integralRingIso u)).unit.app ((completedReductionLevel T d n).obj M)).val.app
            W (reductionTensorSection T (d.projection T n) M W a x)) =
      reductionTensorSection T' (d.projection T' n)
        ((proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).obj M)
        ((proEtaleBaseChange u).op.obj W)
        ((proEtaleRingDirectImageMap u (d.finiteRing T n) (d.finiteRing T' n)
          (d.finiteRingIso u n)).hom.app W a)
        (((proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
          (d.integralRingIso u)).unit.app M).val.app W x))

/-- A literal clause of PurCompletedReindexingAt.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingAtTransitions {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∀ (M : reductionModules T (d.completedRing T)) (n m : ℕᵒᵖ) (a : n ⟶ m),
    ((completedReductionModuleTowerFunctor T d ⋙ d.towerModulePull u).obj M).map a ≫
        (completedReductionLevelPullbackIso d u m.unop).hom.app M =
      (completedReductionLevelPullbackIso d u n.unop).hom.app M ≫
        ((proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ⋙
          completedReductionModuleTowerFunctor T' d).obj M).map a)

def PurCompletedReindexingAt {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  PurCompletedReindexingAtSections d u ∧
  PurCompletedReindexingAtModules d u ∧
  PurCompletedReindexingAtModuleLimits d u ∧
  PurCompletedReindexingAtModuleColimits d u ∧
  PurCompletedReindexingAtTowers d u ∧
  PurCompletedReindexingAtTowerLimits d u ∧
  PurCompletedReindexingAtTowerColimits d u ∧
  PurCompletedReindexingAtDerived d u ∧
  PurCompletedReindexingAtDerivedTowers d u ∧
  PurCompletedReindexingAtLimit d u ∧
  PurCompletedReindexingAtReduction d u ∧
  PurCompletedReindexingAtTensor d u ∧
  PurCompletedReindexingAtTransitions d u

/- Section and K-injective normalizations of both specified direct-image mates.
The first equation is restriction along the canonical fibre-product square after
inverse-image units. Since g is an isomorphism, its base-changed tests cover all tests.
The last equations identify the derived mates on actual K-injective complexes,
including strict tower complexes, rather than merely asserting they are invertible.
Source: extracted argument, steps 6--8; Stacks Tags 07A7, 08BJ and 0FND
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing). -/
/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareOrdinary {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingModuleMate d sq)

/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareOrdinaryTowers {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingTowerModuleMate d sq)

/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareDerived {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingDerivedMate d sq)

/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareDerivedTowers {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingRingedSquare d sq).exchangeTowerMate

/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareSections {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  (∀ (M : reductionModules X (d.completedRing X)) (V : Y.ProEt)
      (x : M.val.obj (op ((proEtaleBaseChange p).obj V))),
    ((purReindexingModuleMate d sq).app M).val.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing Y')
          (d.integralRingIso g)).unit.app
            ((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso p)).obj M)).val.app (op V) x) =
      ((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).obj M).val.map
        ((purReindexingTestSquare sq.w).hom.app V).op
        (((proEtaleRingModuleAdjunction v (d.completedRing X) (d.completedRing X')
          (d.integralRingIso v)).unit.app M).val.app
            (op ((proEtaleBaseChange p).obj V)) x))

/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareDerivedUnits {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  (∀ I : CochainComplex (reductionModules X (d.completedRing X)) ℤ, I.IsKInjective →
    (d.pull g).map
        ((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso p)).rightDerivedFunctorUnitQ I) ≫
      (purReindexingDerivedMate d sq).app (DerivedCategory.Q.obj I) ≫
      (d.push p').map ((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).mapDerivedCategoryFactors.hom.app I) =
    (proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g)).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso p)).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (purReindexingModuleMate d sq) (.up ℤ)).app I) ≫
      (proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
        (d.integralRingIso p')).rightDerivedFunctorUnitQ
          (((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).mapHomologicalComplex (.up ℤ)).obj I))

/-- A literal clause of PurCompletedReindexingSquare.
Source: extracted reindexing normalization
(blueprint: def-pur-completed-reindexing-data). -/
def PurCompletedReindexingSquareDerivedTowerUnits {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  (∀ I : CochainComplex (d.towers X) ℤ, I.IsKInjective →
    (d.towerPull g).map ((d.towerModulePush p).rightDerivedFunctorUnitQ I) ≫
      (purReindexingRingedSquare d sq).exchangeTowerMate.app (DerivedCategory.Q.obj I) ≫
      (d.towerPush p').map ((d.towerModulePull v).mapDerivedCategoryFactors.hom.app I) =
    (d.towerModulePull g).mapDerivedCategoryFactors.hom.app
        (((d.towerModulePush p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (purReindexingTowerModuleMate d sq) (.up ℤ)).app I) ≫
      (d.towerModulePush p').rightDerivedFunctorUnitQ
        (((d.towerModulePull v).mapHomologicalComplex (.up ℤ)).obj I))

def PurCompletedReindexingSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  PurCompletedReindexingSquareOrdinary d sq ∧
  PurCompletedReindexingSquareOrdinaryTowers d sq ∧
  PurCompletedReindexingSquareDerived d sq ∧
  PurCompletedReindexingSquareDerivedTowers d sq ∧
  PurCompletedReindexingSquareSections d sq ∧
  PurCompletedReindexingSquareDerivedUnits d sq ∧
  PurCompletedReindexingSquareDerivedTowerUnits d sq
```

## Users

The read-only tools/downstream.py query found these six downstream modules. No consumer
needs a source adaptation; the exact names and definitions remain publicly available.
The local claim snapshot has no claim record for these modules; no ownership is taken.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | no local claim record | same re-exported declarations; no edit |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | no local claim record | same re-exported declarations; no edit |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | no local claim record | same re-exported declarations; no edit |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | no local claim record | same re-exported declarations; no edit |
| Sheaf.Paper.SemilinearExchangeReindexing | no local claim record | same re-exported declarations; no edit |
| Sheaf.Paper.SemilinearExchangeReindexingData | no local claim record | same re-exported declarations; no edit |
| Sheaf.Paper.PurCompletedReductionReindexing | W2 | re-exports unchanged data, proves assembly |

## Status

landed 20261025T203551-L-2828711 2026-10-25 (merge of deliver/W2/Sheaf.Paper.PurCompletedReductionReindexing)
