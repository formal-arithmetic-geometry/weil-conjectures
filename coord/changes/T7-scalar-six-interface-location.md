# ScalarSix coefficient and extension interfaces

## Reason

The scalar-six proof needs lemmas about its interfaces without importing its own existence
theorem. Move the interfaces to ScalarSixDefinitions and publicly re-export them. The first
27 declarations keep their types and values. Four aliases become reducible abbreviations,
and the three transport formulas factor through generic equivalence cancellation. The
extension proposition is repackaged as nonemptiness of
a structure with exactly the same witnesses and equations, because dependent existential
assembly causes repeated expensive kernel unfolding. This is a representation repair;
no functor or comparison is replaced and no target statement changes. Each large function
type and each proof clause is named separately with its exact old formula. The structures
store those witnesses and named propositions, rather than repeating dependent formulas in
their generated constructor and projection types.

## Old

The following exact declaration block was in
`lean/Sheaf/SixFunctors/ScalarSixPullback.lean`:

```lean
/-- Bundled parameters for commutative condensed coefficients.
Source: blueprint coefficient change (blueprint: det-prop-scalar-six-pullback). -/
abbrev ScalarSixRing := CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Expose the left functor already specified by an adjunction. This avoids rebuilding
its K-flat tensor instances when specializing the published scalar adjunction.
Source: blueprint coefficient change (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixAdjunctionLeft {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (_adj : F ⊣ G) : C ⥤ D := F

/-- Ordinary unbounded derived scalar extension, using the published coefficient map
and the left functor of its derived adjunction (definitionally L(Ext)).
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X) :=
  scalarSixAdjunctionLeft (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))

/-- Exact inverse image applied termwise. This is canonically the total derived pullback.
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPull (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  D((f)^*⟦Λ.X⟧)

/-- The canonical non-flat pullback comparison, the scalar-adjunction mate of the
identity-on-underlying-sheaves restriction comparison `derivedComapUpperStarIso`.
Source: blueprint proof (1), steps 1--2 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPullHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixChange a X ⟶
      scalarSixChange a Y ⋙ scalarSixPull Λ' f :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)

/-- The ordinary, exact inverse-image compositor, localized termwise.
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPullComp (Λ : ScalarSixRing.{u}) {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ W) :
    scalarSixPull Λ (f ≫ g) ≅ scalarSixPull Λ g ⋙ scalarSixPull Λ f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ.X f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The tensor associator, fixed as the conjugate of transitivity of exact restriction.
On K-flat representatives its formula is c tensor (b tensor m) to cb tensor m.
Source: blueprint proof (3), step 7 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixTower {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    scalarSixChange a X ⋙ scalarSixChange b X ≅ scalarSixChange (a ≫ b) X :=
  (conjugateIsoEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X))
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)))).symm
    (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_comp (Λ := Λ.X) (Λ' := Λ'.X) (Λ'' := Λ''.X)
          a.hom.hom b.hom.hom X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapComp _ _ ) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)

/-- The fixed section-ring model of a condensed coefficient object.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixSectionRing (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  ModuleRingedComparison.ring Λ.X X

/-- The fixed exact equivalence on unbounded derived module categories, forward direction.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixForward (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) :=
  (ModuleRingedComparison.equivalence Λ.X X).functor.mapDerivedCategory

/-- The inverse of the same equivalence, applied termwise.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixBackward (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) :=
  (ModuleRingedComparison.equivalence Λ.X X).inverse.mapDerivedCategory

/-- Noetherian coefficient object for a finite-type scheme over a field. The two
Noetherian proofs follow from finite type and quasi-compactness, with no added hypotheses.
Source: blueprint proof (2), step 3 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixCoefficients (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    LocallyClosedCoefficients.{u} where
  scheme := X.left
  locallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  compact := QuasiCompact.compactSpace_of_compactSpace X.hom
  ring := scalarSixSectionRing Λ X.left

/-- Canonical coefficient identifications in the two module presentations. The adjunct
normalization fixes every section, hence determines the ring isomorphism uniquely.
Source: blueprint proof steps 1 and 3 (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixGeometry where
  coefficient : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (scalarSixSectionRing Λ Y) ≅ scalarSixSectionRing Λ X
  coefficientNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (scalarSixSectionRing Λ Y).obj.obj V),
    ((proEtaleRingDirectImageMap f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (coefficient Λ f)).hom.app V).hom r =
      ((condensedPushforwardHom Λ.X f).hom.app V).hom r

  push : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X Y).functor ≅
      (ModuleRingedComparison.equivalence Λ.X X).functor ⋙
        proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (coefficient Λ f)
  pushNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleRingedComparison.internalModules Λ.X X) (V : Y.ProEtᵒᵖ)
    (m : ((lowerStar Λ.X f).obj M).X.obj.obj V),
    ((push Λ f).hom.app M).val.app V m = m
  pull : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    upperStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X X).functor ≅
      (ModuleRingedComparison.equivalence Λ.X Y).functor ⋙
        proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (coefficient Λ f)
  pullNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (upperStarLowerStarAdjunction Λ.X f)
      (proEtaleRingModuleAdjunction f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (coefficient Λ f))
      (.mk _ _ _ _ (pull Λ f).inv)).natTrans = (push Λ f).hom

/-- The locally closed coefficient arrow with its canonically normalized coefficient map.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixImmersion (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    LocallyClosedCoefficientImmersion (scalarSixCoefficients Λ S) (scalarSixCoefficients Λ X)
    where
  hom := f.left
  immersion := inferInstance
  coefficient := G.coefficient Λ f.left

/-- Expose immersion stability in the over-category at its actual underlying map.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixOverCompImmersion {k : Type u} [Field k]
    {T S X : Over (Spec (.of k))} (g : T ⟶ S) (f : S ⟶ X)
    [IsImmersion g.left] [IsImmersion f.left] : IsImmersion (g ≫ f).left :=
  inferInstanceAs (IsImmersion (g.left ≫ f.left))

/-- Expose the published extension's additive structure without unfolding the arrow.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixExtensionAdditive (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    (E.extension a).Additive := E.additive a

/-- Expose the published extension's exactness, finite-limit half.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixExtensionFiniteLimits (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    PreservesFiniteLimits (E.extension a) := E.finiteLimits a

/-- Expose the published extension's exactness, finite-colimit half.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixExtensionFiniteColimits (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    PreservesFiniteColimits (E.extension a) := E.finiteColimits a

/-- The actual extension by zero on internal-module derived categories, transported
from the published exact locally closed extension. No choice of a new extension functor.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixExtension (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (Λ : ScalarSixRing.{u}) {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ f) ⋙
    scalarSixBackward Λ X.left

/-- The fixed equivalence on the two ordinary unbounded derived categories.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixEquivalence (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ≌
      DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) :=
  (ModuleRingedComparison.equivalence Λ.X X).mapDerivedCategory

/-- The localized, adjunction-normalized inverse-image square.
Source: blueprint proof steps 1--2 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPullSection (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixForward Λ X ≅ scalarSixForward Λ Y ⋙
      (proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (G.pull Λ f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Clause (1), with its canonical normalization, and the inverse-image square of (3).
All coefficient maps are allowed, including non-flat maps.
Source: blueprint clauses (1), (3) (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixPullbackData where
  theta : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    scalarSixPull Λ f ⋙ scalarSixChange a X ≅ scalarSixChange a Y ⋙ scalarSixPull Λ' f
  thetaNormalization : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y), (theta a f).hom = scalarSixPullHom a f
  composition : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)),
    (theta a (f ≫ g)).hom.app K ≫
        (scalarSixPullComp Λ' f g).hom.app ((scalarSixChange a W).obj K) =
      (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app K) ≫
        (theta a f).hom.app ((scalarSixPull Λ g).obj K) ≫
          (scalarSixPull Λ' f).map ((theta a g).hom.app K)
  tower : ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
    (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj K) ≫
        (theta (a ≫ b) f).hom.app K =
      (scalarSixChange b X).map ((theta a f).hom.app K) ≫
        (theta b f).hom.app ((scalarSixChange a Y).obj K) ≫
          (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app K)

section Standing

variable {k : Type u} [Field k]

/-- The ordinary open comparison and its adjunction-mate normalization. These are
witnesses in the assertion, not an assumed replacement extension functor.
Source: blueprint proof step 4 (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixOpenComparison (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] where
  comparison : ∀ (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left],
    openImmersionLowerShriek Λ.X j.left ⋙
        (ModuleRingedComparison.equivalence Λ.X X.left).functor ≅
      (ModuleRingedComparison.equivalence Λ.X S.left).functor ⋙
        E.extension (scalarSixImmersion G Λ j)
  normalization : ∀ (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left],
    (mateEquiv (openImmersionLowerShriekUpperStarAdjunction Λ.X j.left)
      (E.openAdjunction (scalarSixImmersion G Λ j)
        (inferInstanceAs (IsOpenImmersion j.left)))
      (.mk _ _ _ _ (comparison Λ j).inv)).natTrans = (G.pull Λ j.left).hom

variable (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
  (G : ScalarSixGeometry.{u})

/-- Transport of the normalized open comparison, using only localization and the
fixed equivalence unit. Source: blueprint proof step 4
(blueprint: det-prop-scalar-six-pullback). -/
def scalarSixOpenIso (O : ScalarSixOpenComparison E G k) (Λ : ScalarSixRing.{u})
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left] :
    scalarSixExtension E G Λ j ≅ D(openImmersionLowerShriek Λ.X j.left) :=
  letI := E.additive (scalarSixImmersion G Λ j)
  letI := E.finiteLimits (scalarSixImmersion G Λ j)
  letI := E.finiteColimits (scalarSixImmersion G Λ j)
  let d : D(openImmersionLowerShriek Λ.X j.left) ⋙ scalarSixForward Λ X.left ≅
      scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ j) :=
    (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ.X j.left)
      (ModuleRingedComparison.equivalence Λ.X X.left).functor).symm ≪≫
        Functor.mapDerivedCategoryNatIso (O.comparison Λ j) ≪≫
          Functor.mapDerivedCategoryCompIso
            (ModuleRingedComparison.equivalence Λ.X S.left).functor
            (E.extension (scalarSixImmersion G Λ j))
  Functor.isoWhiskerRight d.symm (scalarSixBackward Λ X.left) ≪≫
    Functor.isoWhiskerLeft D(openImmersionLowerShriek Λ.X j.left)
      (scalarSixEquivalence Λ X.left).unitIso.symm ≪≫ Functor.rightUnitor _


/-- Restriction of the actual extension, transported from the published derived
restriction and the normalized inverse-image square.
Source: blueprint proof step 6 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixRestriction (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    scalarSixExtension E G Λ f ⋙ scalarSixPull Λ f.left ≅ 𝟭 _ :=
  (Functor.rightUnitor (scalarSixExtension E G Λ f ⋙ scalarSixPull Λ f.left)).symm ≪≫
    Functor.isoWhiskerLeft (scalarSixExtension E G Λ f ⋙ scalarSixPull Λ f.left)
      (scalarSixEquivalence Λ S.left).unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ f) ⋙
          scalarSixBackward Λ X.left) (scalarSixPullSection G Λ f.left) ≪≫
        Functor.isoWhiskerLeft (scalarSixForward Λ S.left ⋙
          E.derived (scalarSixImmersion G Λ f))
          (Functor.isoWhiskerRight (scalarSixEquivalence Λ X.left).counitIso _) ≪≫
        Functor.isoWhiskerLeft (scalarSixForward Λ S.left)
          (D.restriction (scalarSixImmersion G Λ f)) ≪≫ Functor.rightUnitor _)
      (scalarSixBackward Λ S.left) ≪≫ (scalarSixEquivalence Λ S.left).unitIso.symm


/-- The extension compositor is the published gamma, with the middle equivalence
cancelled. The equality argument identifies exactly the canonical coefficient arrows.
Source: blueprint proof step 6 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixExtensionComp (Λ : ScalarSixRing.{u}) {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (h : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)) :
    scalarSixExtension E G Λ g ⋙ scalarSixExtension E G Λ f ≅
      scalarSixExtension E G Λ (g ≫ f) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (scalarSixForward Λ T.left ⋙
      E.derived (scalarSixImmersion G Λ g))
      (Functor.isoWhiskerRight (scalarSixEquivalence Λ S.left).counitIso
        (E.derived (scalarSixImmersion G Λ f)))) (scalarSixBackward Λ X.left) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (scalarSixForward Λ T.left)
      (D.gamma (scalarSixImmersion G Λ f) (scalarSixImmersion G Λ g) ≪≫
        eqToIso (congrArg E.derived h.symm))) (scalarSixBackward Λ X.left)


/-- Exact closed direct image, applied termwise and transported through the fixed
module equivalence. Exactness comes from the published closed comparison, rather than
from a new assumption on the coefficient ring.
Source: blueprint proof step 5 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixClosedPush (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left] :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  letI := E.additive (scalarSixImmersion G Λ i)
  letI := E.finiteLimits (scalarSixImmersion G Λ i)
  letI := E.finiteColimits (scalarSixImmersion G Λ i)
  let e := E.closedComparison (scalarSixImmersion G Λ i)
    (inferInstanceAs (IsClosedImmersion i.left))
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  scalarSixForward Λ S.left ⋙ (scalarSixImmersion G Λ i).push.mapDerivedCategory ⋙
    scalarSixBackward Λ X.left

/-- The closed specialization is the localization of the actual closed direct-image
comparison supplied by the coherence node.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixClosedIso (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left] :
    scalarSixExtension E G Λ i ≅ scalarSixClosedPush E G Λ i :=
  letI := E.additive (scalarSixImmersion G Λ i)
  letI := E.finiteLimits (scalarSixImmersion G Λ i)
  letI := E.finiteColimits (scalarSixImmersion G Λ i)
  let e := E.closedComparison (scalarSixImmersion G Λ i)
    (inferInstanceAs (IsClosedImmersion i.left))
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (scalarSixForward Λ S.left)
    (Functor.mapDerivedCategoryNatIso
      (E.closedComparison (scalarSixImmersion G Λ i)
        (inferInstanceAs (IsClosedImmersion i.left))))) (scalarSixBackward Λ X.left)


/-- All clauses for the standing separated finite-type schemes. The beta comparison
uses the published exact locally closed extension; its restriction is inverse theta.
The open, closed, composition and coefficient-tower equations specify every comparison.
Source: blueprint clauses (2)--(3) (blueprint: det-prop-scalar-six-pullback). -/
def ScalarSixExtensionData (E : LocallyClosedExtensionData.{u})
    (D : E.DerivedCoherence) (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) : Prop :=
  ∃ (beta : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) [IsImmersion f.left],
    scalarSixExtension E G Λ f ⋙ scalarSixChange a X.left ≅
      scalarSixChange a S.left ⋙ scalarSixExtension E G Λ' f),
  (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) [IsImmersion f.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
    (scalarSixPull Λ' f.left).map ((beta a f).hom.app M) ≫
        (scalarSixRestriction E D G Λ' f).hom.app ((scalarSixChange a S.left).obj M) =
      (C.theta a f.left).inv.app ((scalarSixExtension E G Λ f).obj M) ≫
        (scalarSixChange a S.left).map ((scalarSixRestriction E D G Λ f).hom.app M)) ∧
  ∃ (compositionIdentifier : ∀ (Λ : ScalarSixRing.{u}) {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left],
    scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)),
  (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X T.left)),
    (scalarSixChange a X.left).map
        ((scalarSixExtensionComp E D G Λ (k := k) (T := T) (S := S) (X := X) f g
          (compositionIdentifier Λ (T := T) (S := S) (X := X) f g)).hom.app M) ≫
        (beta a (g ≫ f)).hom.app M =
      (beta a f).hom.app ((scalarSixExtension E G Λ g).obj M) ≫
        (scalarSixExtension E G Λ' f).map ((beta a g).hom.app M) ≫
          (scalarSixExtensionComp E D G Λ' (k := k) (T := T) (S := S) (X := X) f g
            (compositionIdentifier Λ' (T := T) (S := S) (X := X) f g)).hom.app
            ((scalarSixChange a T.left).obj M)) ∧
  (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
    (scalarSixChange a X.left).map ((scalarSixOpenIso E G O Λ j).hom.app M) ≫
        (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j.left).hom.app M =
      (beta a j).hom.app M ≫
        (scalarSixOpenIso E G O Λ' j).hom.app ((scalarSixChange a S.left).obj M)) ∧
  ∃ (closed : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left],
    scalarSixClosedPush E G Λ i ⋙ scalarSixChange a X.left ≅
      scalarSixChange a S.left ⋙ scalarSixClosedPush E G Λ' i),
  (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
    (scalarSixChange a X.left).map ((scalarSixClosedIso E G Λ i).hom.app M) ≫
        (closed a i).hom.app M =
      (beta a i).hom.app M ≫
        (scalarSixClosedIso E G Λ' i).hom.app ((scalarSixChange a S.left).obj M)) ∧
  (∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) [IsImmersion f.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
    (scalarSixTower a b X.left).hom.app ((scalarSixExtension E G Λ f).obj M) ≫
        (beta (a ≫ b) f).hom.app M =
      (scalarSixChange b X.left).map ((beta a f).hom.app M) ≫
        (beta b f).hom.app ((scalarSixChange a S.left).obj M) ≫
          (scalarSixExtension E G Λ'' f).map ((scalarSixTower a b S.left).hom.app M))

end Standing
```

## New

The following declaration block is in
`lean/Sheaf/SixFunctors/ScalarSixDefinitions.lean`:

```lean
/-- Bundled parameters for commutative condensed coefficients.
Source: blueprint coefficient change (blueprint: det-prop-scalar-six-pullback). -/
abbrev ScalarSixRing := CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Expose the left functor already specified by an adjunction. This avoids rebuilding
its K-flat tensor instances when specializing the published scalar adjunction.
Source: blueprint coefficient change (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixAdjunctionLeft {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (_adj : F ⊣ G) : C ⥤ D := F

/-- Additivity of the unchanged forward module equivalence.
Source: internal module operations transport
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
instance scalarSixEquivalenceAdditive (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (ModuleRingedComparison.equivalence Λ.X X).functor.Additive :=
  ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).1

/-- Additivity of the unchanged inverse module equivalence.
Source: internal module operations transport
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
instance scalarSixEquivalenceInverseAdditive (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (ModuleRingedComparison.equivalence Λ.X X).inverse.Additive :=
  ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).2.1

/-- Ordinary unbounded derived scalar extension, using the published coefficient map
and the left functor of its derived adjunction (definitionally L(Ext)).
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X) :=
  scalarSixAdjunctionLeft (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))

/-- Exact inverse image applied termwise. This is canonically the total derived pullback.
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPull (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  D((f)^*⟦Λ.X⟧)

/-- The canonical non-flat pullback comparison, the scalar-adjunction mate of the
identity-on-underlying-sheaves restriction comparison `derivedComapUpperStarIso`.
Source: blueprint proof (1), steps 1--2 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPullHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixChange a X ⟶
      scalarSixChange a Y ⋙ scalarSixPull Λ' f :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)

/-- The ordinary, exact inverse-image compositor, localized termwise.
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPullComp (Λ : ScalarSixRing.{u}) {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ W) :
    scalarSixPull Λ (f ≫ g) ≅ scalarSixPull Λ g ⋙ scalarSixPull Λ f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ.X f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The tensor associator, fixed as the conjugate of transitivity of exact restriction.
On K-flat representatives its formula is c tensor (b tensor m) to cb tensor m.
Source: blueprint proof (3), step 7 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixTower {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    scalarSixChange a X ⋙ scalarSixChange b X ≅ scalarSixChange (a ≫ b) X :=
  (conjugateIsoEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X))
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)))).symm
    (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_comp (Λ := Λ.X) (Λ' := Λ'.X) (Λ'' := Λ''.X)
          a.hom.hom b.hom.hom X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapComp _ _ ) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)

/-- The fixed section-ring model of a condensed coefficient object.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixSectionRing (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  ModuleRingedComparison.ring Λ.X X

/-- The fixed exact equivalence on unbounded derived module categories, forward direction.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixForward (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) :=
  (ModuleRingedComparison.equivalence Λ.X X).functor.mapDerivedCategory

/-- The inverse of the same equivalence, applied termwise.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixBackward (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) :=
  (ModuleRingedComparison.equivalence Λ.X X).inverse.mapDerivedCategory

/-- Noetherian coefficient object for a finite-type scheme over a field. The two
Noetherian proofs follow from finite type and quasi-compactness, with no added hypotheses.
Source: blueprint proof (2), step 3 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixCoefficients (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    LocallyClosedCoefficients.{u} where
  scheme := X.left
  locallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  compact := QuasiCompact.compactSpace_of_compactSpace X.hom
  ring := scalarSixSectionRing Λ X.left

/-- Canonical coefficient identifications in the two module presentations. The adjunct
normalization fixes every section, hence determines the ring isomorphism uniquely.
Source: blueprint proof steps 1 and 3 (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixGeometry where
  coefficient : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (scalarSixSectionRing Λ Y) ≅ scalarSixSectionRing Λ X
  coefficientNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (scalarSixSectionRing Λ Y).obj.obj V),
    ((proEtaleRingDirectImageMap f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (coefficient Λ f)).hom.app V).hom r =
      ((condensedPushforwardHom Λ.X f).hom.app V).hom r

  push : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X Y).functor ≅
      (ModuleRingedComparison.equivalence Λ.X X).functor ⋙
        proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (coefficient Λ f)
  pushNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleRingedComparison.internalModules Λ.X X) (V : Y.ProEtᵒᵖ)
    (m : ((lowerStar Λ.X f).obj M).X.obj.obj V),
    ((push Λ f).hom.app M).val.app V m = m
  pull : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    upperStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X X).functor ≅
      (ModuleRingedComparison.equivalence Λ.X Y).functor ⋙
        proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (coefficient Λ f)
  pullNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (upperStarLowerStarAdjunction Λ.X f)
      (proEtaleRingModuleAdjunction f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (coefficient Λ f))
      (.mk _ _ _ _ (pull Λ f).inv)).natTrans = (push Λ f).hom

/-- The locally closed coefficient arrow with its canonically normalized coefficient map.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixImmersion (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    LocallyClosedCoefficientImmersion (scalarSixCoefficients Λ S) (scalarSixCoefficients Λ X)
    where
  hom := f.left
  immersion := inferInstance
  coefficient := G.coefficient Λ f.left

/-- Expose immersion stability in the over-category at its actual underlying map.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixOverCompImmersion {k : Type u} [Field k]
    {T S X : Over (Spec (.of k))} (g : T ⟶ S) (f : S ⟶ X)
    [IsImmersion g.left] [IsImmersion f.left] : IsImmersion (g ≫ f).left :=
  inferInstanceAs (IsImmersion (g.left ≫ f.left))

/-- Expose the published extension's additive structure without unfolding the arrow.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixExtensionAdditive (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    (E.extension a).Additive := E.additive a

/-- Expose the published extension's exactness, finite-limit half.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixExtensionFiniteLimits (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    PreservesFiniteLimits (E.extension a) := E.finiteLimits a

/-- Expose the published extension's exactness, finite-colimit half.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
instance scalarSixExtensionFiniteColimits (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    PreservesFiniteColimits (E.extension a) := E.finiteColimits a

/-- The actual extension by zero on internal-module derived categories, transported
from the published exact locally closed extension. No choice of a new extension functor.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixExtension (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (Λ : ScalarSixRing.{u}) {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ f) ⋙
    scalarSixBackward Λ X.left

/-- The fixed equivalence on the two ordinary unbounded derived categories.
Source: blueprint proof step 1 (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixEquivalence (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ≌
      DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) :=
  (ModuleRingedComparison.equivalence Λ.X X).mapDerivedCategory

/-- The localized, adjunction-normalized inverse-image square.
Source: blueprint proof steps 1--2 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixPullSection (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixForward Λ X ≅ scalarSixForward Λ Y ⋙
      (proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (G.pull Λ f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Clause (1), with its canonical normalization, and the inverse-image square of (3).
All coefficient maps are allowed, including non-flat maps.
Source: blueprint clauses (1), (3) (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixPullbackData where
  theta : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    scalarSixPull Λ f ⋙ scalarSixChange a X ≅ scalarSixChange a Y ⋙ scalarSixPull Λ' f
  thetaNormalization : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y), (theta a f).hom = scalarSixPullHom a f
  composition : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)),
    (theta a (f ≫ g)).hom.app K ≫
        (scalarSixPullComp Λ' f g).hom.app ((scalarSixChange a W).obj K) =
      (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app K) ≫
        (theta a f).hom.app ((scalarSixPull Λ g).obj K) ≫
          (scalarSixPull Λ' f).map ((theta a g).hom.app K)
  tower : ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
    (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj K) ≫
        (theta (a ≫ b) f).hom.app K =
      (scalarSixChange b X).map ((theta a f).hom.app K) ≫
        (theta b f).hom.app ((scalarSixChange a Y).obj K) ≫
          (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app K)

/-- Cancel the fixed presentation equivalence in an open extension comparison.
Source: functorial transport (blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def scalarSixTransportOpen
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (J : A ⥤ B) (F : C ⥤ D)
    (d : J ⋙ e'.functor ≅ e.functor ⋙ F) :
    e.functor ⋙ F ⋙ e'.inverse ≅ J :=
  Functor.isoWhiskerRight d.symm e'.inverse ≪≫
    Functor.isoWhiskerLeft J e'.unitIso.symm ≪≫ Functor.rightUnitor _

/-- Transport an extension's restriction through the fixed equivalences.
Source: functorial transport (blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def scalarSixTransportRestriction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (F : C ⥤ D) (R : B ⥤ A) (Q : D ⥤ C)
    (d : R ⋙ e.functor ≅ e'.functor ⋙ Q) (rho : F ⋙ Q ≅ 𝟭 C) :
    (e.functor ⋙ F ⋙ e'.inverse) ⋙ R ≅ 𝟭 A :=
  (Functor.rightUnitor ((e.functor ⋙ F ⋙ e'.inverse) ⋙ R)).symm ≪≫
    Functor.isoWhiskerLeft ((e.functor ⋙ F ⋙ e'.inverse) ⋙ R) e.unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (e.functor ⋙ F ⋙ e'.inverse) d ≪≫
        Functor.isoWhiskerLeft (e.functor ⋙ F)
          (Functor.isoWhiskerRight e'.counitIso Q) ≪≫
        Functor.isoWhiskerLeft e.functor rho ≪≫ Functor.rightUnitor _)
      e.inverse ≪≫ e.unitIso.symm

/-- Transport a compositor and cancel the middle presentation equivalence.
Source: functorial transport (blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def scalarSixTransportComposition
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    (eA : A ≌ A') (eB : B ≌ B') (eC : C ≌ C')
    (F : B' ⥤ C') (G : A' ⥤ B') (H : A' ⥤ C') (gamma : G ⋙ F ≅ H) :
    (eA.functor ⋙ G ⋙ eB.inverse) ⋙ (eB.functor ⋙ F ⋙ eC.inverse) ≅
      eA.functor ⋙ H ⋙ eC.inverse :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (eA.functor ⋙ G)
      (Functor.isoWhiskerRight eB.counitIso F)) eC.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft eA.functor gamma) eC.inverse

section Standing

variable {k : Type u} [Field k]

/-- The ordinary open comparison and its adjunction-mate normalization. These are
witnesses in the assertion, not an assumed replacement extension functor.
Source: blueprint proof step 4 (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixOpenComparison (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] where
  comparison : ∀ (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left],
    openImmersionLowerShriek Λ.X j.left ⋙
        (ModuleRingedComparison.equivalence Λ.X X.left).functor ≅
      (ModuleRingedComparison.equivalence Λ.X S.left).functor ⋙
        E.extension (scalarSixImmersion G Λ j)
  normalization : ∀ (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left],
    (mateEquiv (openImmersionLowerShriekUpperStarAdjunction Λ.X j.left)
      (E.openAdjunction (scalarSixImmersion G Λ j)
        (inferInstanceAs (IsOpenImmersion j.left)))
      (.mk _ _ _ _ (comparison Λ j).inv)).natTrans = (G.pull Λ j.left).hom

variable (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
  (G : ScalarSixGeometry.{u})

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport of the normalized open comparison, using only localization and the
fixed equivalence unit. Source: blueprint proof step 4
(blueprint: det-prop-scalar-six-pullback). -/
def scalarSixOpenIso (O : ScalarSixOpenComparison E G k) (Λ : ScalarSixRing.{u})
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left] :
    scalarSixExtension E G Λ j ≅ D(openImmersionLowerShriek Λ.X j.left) :=
  letI := E.additive (scalarSixImmersion G Λ j)
  letI := E.finiteLimits (scalarSixImmersion G Λ j)
  letI := E.finiteColimits (scalarSixImmersion G Λ j)
  let d : D(openImmersionLowerShriek Λ.X j.left) ⋙ scalarSixForward Λ X.left ≅
      scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ j) :=
    (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ.X j.left)
      (ModuleRingedComparison.equivalence Λ.X X.left).functor).symm ≪≫
        Functor.mapDerivedCategoryNatIso (O.comparison Λ j) ≪≫
          Functor.mapDerivedCategoryCompIso
            (ModuleRingedComparison.equivalence Λ.X S.left).functor
            (E.extension (scalarSixImmersion G Λ j))
  scalarSixTransportOpen (scalarSixEquivalence Λ S.left) (scalarSixEquivalence Λ X.left)
    D(openImmersionLowerShriek Λ.X j.left) (E.derived (scalarSixImmersion G Λ j)) d


/-- Restriction of the actual extension, transported from the published derived
restriction and the normalized inverse-image square.
Source: blueprint proof step 6 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixRestriction (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    scalarSixExtension E G Λ f ⋙ scalarSixPull Λ f.left ≅ 𝟭 _ :=
  scalarSixTransportRestriction
    (scalarSixEquivalence Λ S.left) (scalarSixEquivalence Λ X.left)
    (E.derived (scalarSixImmersion G Λ f)) (scalarSixPull Λ f.left)
    (scalarSixImmersion G Λ f).pull.mapDerivedCategory (scalarSixPullSection G Λ f.left)
    (D.restriction (scalarSixImmersion G Λ f))


/-- The extension compositor is the published gamma, with the middle equivalence
cancelled. The equality argument identifies exactly the canonical coefficient arrows.
Source: blueprint proof step 6 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixExtensionComp (Λ : ScalarSixRing.{u}) {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (h : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)) :
    scalarSixExtension E G Λ g ⋙ scalarSixExtension E G Λ f ≅
      scalarSixExtension E G Λ (g ≫ f) :=
  scalarSixTransportComposition
    (scalarSixEquivalence Λ T.left) (scalarSixEquivalence Λ S.left)
    (scalarSixEquivalence Λ X.left)
    (E.derived (scalarSixImmersion G Λ f)) (E.derived (scalarSixImmersion G Λ g))
    (E.derived (scalarSixImmersion G Λ (g ≫ f)))
    (D.gamma (scalarSixImmersion G Λ f) (scalarSixImmersion G Λ g) ≪≫
      eqToIso (congrArg E.derived h.symm))


/-- Exact closed direct image, applied termwise and transported through the fixed
module equivalence. Exactness comes from the published closed comparison, rather than
from a new assumption on the coefficient ring.
Source: blueprint proof step 5 (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixClosedPush (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left] :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  letI := E.additive (scalarSixImmersion G Λ i)
  letI := E.finiteLimits (scalarSixImmersion G Λ i)
  letI := E.finiteColimits (scalarSixImmersion G Λ i)
  let e := E.closedComparison (scalarSixImmersion G Λ i)
    (inferInstanceAs (IsClosedImmersion i.left))
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  scalarSixForward Λ S.left ⋙ (scalarSixImmersion G Λ i).push.mapDerivedCategory ⋙
    scalarSixBackward Λ X.left

/-- The closed specialization is the localization of the actual closed direct-image
comparison supplied by the coherence node.
Source: blueprint clause (2) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixClosedIso (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left] :
    scalarSixExtension E G Λ i ≅ scalarSixClosedPush E G Λ i :=
  letI := E.additive (scalarSixImmersion G Λ i)
  letI := E.finiteLimits (scalarSixImmersion G Λ i)
  letI := E.finiteColimits (scalarSixImmersion G Λ i)
  let e := E.closedComparison (scalarSixImmersion G Λ i)
    (inferInstanceAs (IsClosedImmersion i.left))
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (scalarSixForward Λ S.left)
    (Functor.mapDerivedCategoryNatIso
      (E.closedComparison (scalarSixImmersion G Λ i)
        (inferInstanceAs (IsClosedImmersion i.left))))) (scalarSixBackward Λ X.left)


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The published open scalar comparison at the fixed scalar-change functors.
This is exactly the existing comparison, with its functor types checked once.
Source: blueprint open comparison
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def scalarSixOpenScalarIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S X : Scheme.{u}} (j : S ⟶ X) [IsOpenImmersion j] :
    D(openImmersionLowerShriek Λ.X j) ⋙ scalarSixChange a X ≅
      scalarSixChange a S ⋙ D(openImmersionLowerShriek Λ'.X j) :=
  derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] scalarSixExtension scalarSixChange scalarSixPull
  scalarSixRestriction scalarSixExtensionComp scalarSixOpenIso scalarSixClosedIso
  scalarSixClosedPush scalarSixTower

/-- The type of single-arrow immersion comparisons, without an existence assertion.
Source: blueprint clause (2) (blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
abbrev ScalarSixImmersionComparisons (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left],
      scalarSixExtension E G Λ f ⋙ scalarSixChange a X.left ≅
        scalarSixChange a S.left ⋙ scalarSixExtension E G Λ' f

/-- The type of geometric coefficient-composition identities.
Source: blueprint clause (2) (blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
abbrev ScalarSixImmersionIdentifiers (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] :=
  ∀ (Λ : ScalarSixRing.{u}) {T S X : Over (Spec (.of k))}
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left],
      scalarSixImmersion G Λ (g ≫ f) =
        (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)

/-- An unchanged comparison equation, named to keep structure projections compact.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def ScalarSixImmersionNormalization (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k)
    (beta : ScalarSixImmersionComparisons E G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixPull Λ' f.left).map ((beta a f).hom.app M) ≫
          (scalarSixRestriction E D G Λ' f).hom.app ((scalarSixChange a S.left).obj M) =
        (C.theta a f.left).inv.app ((scalarSixExtension E G Λ f).obj M) ≫
          (scalarSixChange a S.left).map ((scalarSixRestriction E D G Λ f).hom.app M)

/-- An unchanged comparison equation, named to keep structure projections compact.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def ScalarSixImmersionComposition (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k)
    (beta : ScalarSixImmersionComparisons E G k)
    (compositionIdentifier : ScalarSixImmersionIdentifiers G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {T S X : Over (Spec (.of k))}
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X T.left)),
      (scalarSixChange a X.left).map
          ((scalarSixExtensionComp E D G Λ (k := k) (T := T) (S := S) (X := X) f g
            (compositionIdentifier Λ (T := T) (S := S) (X := X) f g)).hom.app M) ≫
          (beta a (g ≫ f)).hom.app M =
        (beta a f).hom.app ((scalarSixExtension E G Λ g).obj M) ≫
          (scalarSixExtension E G Λ' f).map ((beta a g).hom.app M) ≫
            (scalarSixExtensionComp E D G Λ' (k := k) (T := T) (S := S) (X := X) f g
              (compositionIdentifier Λ' (T := T) (S := S) (X := X) f g)).hom.app
              ((scalarSixChange a T.left).obj M)

/-- An unchanged comparison equation, named to keep structure projections compact.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def ScalarSixImmersionOpenValue (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k)
    (beta : ScalarSixImmersionComparisons E G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (j : S ⟶ X) [IsOpenImmersion j.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixChange a X.left).map ((scalarSixOpenIso E G O Λ j).hom.app M) ≫
          (scalarSixOpenScalarIso a j.left).hom.app M =
        (beta a j).hom.app M ≫
          (scalarSixOpenIso E G O Λ' j).hom.app ((scalarSixChange a S.left).obj M)

attribute [local irreducible] ScalarSixImmersionNormalization
  ScalarSixImmersionComposition ScalarSixImmersionOpenValue

/-- The single-arrow comparison and its exact geometric and open normalizations.
These fields only bundle the witnesses and equations previously in the existential
interface; no comparison data are chosen here.
Source: blueprint clause (2) (blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
structure ScalarSixNormalizedImmersionData (E : LocallyClosedExtensionData.{u})
    (D : E.DerivedCoherence) (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) where
  beta : ScalarSixImmersionComparisons E G k
  normalization : ScalarSixImmersionNormalization E D G C k O beta
  compositionIdentifier : ScalarSixImmersionIdentifiers G k
  composition : ScalarSixImmersionComposition E D G C k O beta compositionIdentifier
  openComparison : ScalarSixImmersionOpenValue E D G C k O beta

/-- An unchanged extension-comparison clause with its witnesses kept explicit.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
abbrev ScalarSixClosedComparisons (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (i : S ⟶ X) [IsClosedImmersion i.left],
      scalarSixClosedPush E G Λ i ⋙ scalarSixChange a X.left ≅
        scalarSixChange a S.left ⋙ scalarSixClosedPush E G Λ' i

/-- An unchanged extension-comparison clause with its witnesses kept explicit.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def ScalarSixClosedNormalization (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (k : Type u) [Field k] (beta : ScalarSixImmersionComparisons E G k)
    (closed : ScalarSixClosedComparisons E G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (i : S ⟶ X) [IsClosedImmersion i.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixChange a X.left).map ((scalarSixClosedIso E G Λ i).hom.app M) ≫
          (closed a i).hom.app M =
        (beta a i).hom.app M ≫
          (scalarSixClosedIso E G Λ' i).hom.app ((scalarSixChange a S.left).obj M)

/-- An unchanged extension-comparison clause with its witnesses kept explicit.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
def ScalarSixImmersionTower (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (k : Type u) [Field k] (beta : ScalarSixImmersionComparisons E G k) : Prop :=
  ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixTower a b X.left).hom.app ((scalarSixExtension E G Λ f).obj M) ≫
          (beta (a ≫ b) f).hom.app M =
        (scalarSixChange b X.left).map ((beta a f).hom.app M) ≫
          (beta b f).hom.app ((scalarSixChange a S.left).obj M) ≫
            (scalarSixExtension E G Λ'' f).map ((scalarSixTower a b S.left).hom.app M)

attribute [local irreducible] ScalarSixClosedNormalization ScalarSixImmersionTower

/-- The complete comparison data, with precisely the former existential clauses.
The structure shares its witnesses between proof fields instead of duplicating nested
existential predicates. No field is a construction from an existence theorem.
Source: blueprint clauses (2)--(3)
(blueprint: def-sfb-scalar-six-coefficient-interfaces). -/
structure ScalarSixExtensionComparisonData (E : LocallyClosedExtensionData.{u})
    (D : E.DerivedCoherence) (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) where
  normalized : ScalarSixNormalizedImmersionData E D G C k O
  closed : ScalarSixClosedComparisons E G k
  closedNormalization : ScalarSixClosedNormalization E G k normalized.beta closed
  tower : ScalarSixImmersionTower E G k normalized.beta

/-- All clauses for the standing separated finite-type schemes. The beta comparison
uses the published exact locally closed extension; its restriction is inverse theta.
The open, closed, composition and coefficient-tower equations specify every comparison.
Source: blueprint clauses (2)--(3) (blueprint: det-prop-scalar-six-pullback). -/
def ScalarSixExtensionData (E : LocallyClosedExtensionData.{u})
    (D : E.DerivedCoherence) (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) : Prop :=
  Nonempty (ScalarSixExtensionComparisonData E D G C k O)
```

The original module publicly imports `Sheaf.SixFunctors.ScalarSixDefinitions`. Its four
former public imports remain public through that module. The first 27 signatures and values are retained.
The aliases scalarSixSectionRing, scalarSixForward, scalarSixBackward and
scalarSixEquivalence become abbreviations of their original values. Two compact additive
instances are proved from internal_module_operations_transport; they expose the existing
exact equivalence without rebuilding its instances. The new generic
scalarSixTransportOpen, scalarSixTransportRestriction and scalarSixTransportComposition
express exactly the former equivalence-cancellation formulas. The corresponding three
concrete definitions specialize them with the same data. No scalar adjunction, derived
functor, unit, counit or compositor is replaced. The typed scalarSixOpenScalarIso alias
is exactly derivedOpenImmersionShriekIso. The open-value field uses this alias to check
its scalar functors once, without repeatedly unfolding scalarSixChange in every field.

`ScalarSixExtensionData` now means `Nonempty ScalarSixExtensionComparisonData`. That structure
extends `ScalarSixNormalizedImmersionData` and contains exactly the old witnesses and laws:

| Old existential part | New field |
| --- | --- |
| beta witness | normalized.beta |
| restriction normalization | normalized.normalization |
| compositionIdentifier witness | normalized.compositionIdentifier |
| geometric composition equation | normalized.composition |
| specified open equation | normalized.openComparison |
| closed witness | closed |
| closed equation | closedNormalization |
| coefficient-tower equation | tower |

Packing those witnesses and proofs into the constructor proves the new assertion from the
old one; reading the projections gives the old assertion from the new one. Every binder and
equation is retained verbatim apart from indentation and removal of outer conjunction
parentheses. Neither direction adds a hypothesis or chooses new comparison data. This
representation shares the witnesses across clauses and avoids the kernel repeatedly
checking the large dependent existential predicates. The normalized single-arrow lemma
asserts nonemptiness of the nested normalized structure, without the closed or tower fields.

Unused generated constructor/size helpers are suppressed; searches of both roots found
no consumer of those helpers. Explicit constructors and projections are retained.
No source-library module changes.

This repair changes a definition used below targets. The independent statement review must
check the old/new clause correspondence above, the retained binders and normalizations,
and the definitional equality of the named-adjunction formulas. Every target statement
remains textually unchanged and retains its mathematical meaning.

## Users

The table retains the union of downstream modules observed during the session, and the
textual users returned by downstream.py
--uses for each of the 28 declarations (full output retained in the sandbox scratchpad).
`ScalarSixExtensionData` has no textual consumer outside the item. PullHom has no external
textual consumer; Tower occurs only in the statements of CommonFieldLatticeGenerators
and ScalarSixLisseTowerComparison, where its type and definitionally equal value are
retained. No external proof destructs the repackaged existential, so no consumer edit is
forced. The same original public import exposes all existing names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusContractionScalarPasting | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCompletedBaseChange | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalCompletedRealization | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalFamilyExtension | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalFiniteReductions | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalScalarBaseChange | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | U4 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | E7 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | Z9 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralModels | J8 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | H5 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseTowerComparison | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | T7 | Own item: theorem proof and public re-export adapted in this packet. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Q3 | Public signatures retained through re-export; equivalent clauses; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Public signatures retained through re-export; equivalent clauses; no adaptation. |

## Status

landed 20261024T191254-L-290782 2026-10-24 (merge of deliver/T7/Sheaf.SixFunctors.ScalarSixPullback)
