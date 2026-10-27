# AlgebraicGeometry.SectionCompactSource map declaration ownership

## Reason

The two exchange arguments need the same prescribed source maps. Extract the existing
map declarations into `Sheaf.Paper.SectionCompactSourceMaps`, reexported by the item
module, so that separate component statements can mention those maps without an import
cycle. Every declaration name, signature, attribute and defining term is retained verbatim.
This is an interface extraction for component dependencies, with no mathematical definition
change and no new choice of data. The source-library tree is untouched.

## Old

The following declarations occur in `Sheaf.Paper.SectionCompactSourceExchange`:

```lean
/-- The constant etale module in degree zero.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def etaleConstant (B : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (SupportedConstantNormalization.constant A false B)

/-- The constant pro-etale module in degree zero.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def proConstant (B : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (SupportedConstantNormalization.constant A true B)

/-- The etale supported constant in degree zero.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def etaleSupported {B X : Scheme.{u}} (s : B ⟶ X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (SupportedConstantNormalization.supported A false s)

/-- The pro-etale supported constant in degree zero.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def proSupported {B X : Scheme.{u}} (s : B ⟶ X) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (SupportedConstantNormalization.supported A true s)

/-- The exact inverse image identification of base constants, with its scalar unit.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def constantPull {B' B : Scheme.{u}} (g : B' ⟶ B) :
    (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj
      (etaleConstant A B) ≅ etaleConstant A B' :=
  ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlusSingleFunctor 0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (SupportedConstantNormalization.unitIso A false g)

/-- Exact closed direct image, with its canonical derived computation comparison.
Source: Stacks Tags 04CA and 0D6E; blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def closedSingle {B X : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s] :
    (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) s).obj
      (etaleConstant A B) ≅ etaleSupported A s :=
  (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
    (Etale.lowerStar (ModuleCat.{u + 1} A) s)).app (etaleConstant A B) ≪≫
      ((Etale.lowerStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlusSingleFunctor 0).app _

/-- The normalized proper/open family of the recorded coherence theorem.
Its section normalization determines its maps uniquely.
Source: Stacks Tag 0F7B (blueprint: lem-pur-section-compact-source-exchange). -/
def interchange [Finite A] : Etale.ProperOpenDerivedFamily A :=
  fun {B₁ B₂ B₃ B₄} k i r p _ _ _ _ w ↦
    (Etale.properOpenInterchangeCoherence A).choose_spec.choose
      (A := B₁) (B := B₂) (C := B₃) (D := B₄) k i r p w

/-- The normalized direct-image compositor of the recorded coherence theorem.
Source: Stacks Tag 0D6E (blueprint: lem-pur-section-compact-source-exchange). -/
def compositor {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (fg : Y ⟶ W) (w : fg = f ≫ g) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) fg ≅
      Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f ⋙
        Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g :=
  (Functor.rightDerivedFunctorPlusCompIso'
    (Etale.lowerStar (ModuleCat.{u + 1} A) f)
    (Etale.lowerStar (ModuleCat.{u + 1} A) g)
    (Etale.lowerStarComp (ModuleCat.{u + 1} A) f g fg w)).symm

/-- The identity comparison from the same normalized direct-image family.
Source: Stacks Tag 0D6E (blueprint: lem-pur-section-compact-source-exchange). -/
def directIdentity (B : Scheme.{u}) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) (𝟙 B) ≅ 𝟭 _ :=
  Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} A) B

/-- The specified etale source, constructed as the inverse of
Rp_*j_!s_*A ≅ Rp_*R(js)_*A ≅ R(pjs)_*A ≅ A.
The first comparison is exactly the normalized proper/open interchange.
Source: Stacks Tags 0F7B and 0D6E; blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def etaleSource [Finite A] {B X : Scheme.{u}} {h : X ⟶ B}
    (c : Compactification h) (s : B ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ h = 𝟙 B) :
    etaleConstant A B ≅
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj
        (etaleSupported A s) := by
  let wq : (s ≫ c.i) ≫ c.g = 𝟙 B :=
    (Category.assoc _ _ _).trans ((congrArg (fun f ↦ s ≫ f) c.comm).symm.trans hs)
  letI : IsProper ((s ≫ c.i) ≫ c.g) := wq.symm ▸ inferInstance
  letI : IsProper (s ≫ c.i) := IsProper.of_comp (s ≫ c.i) c.g
  let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 B))
  let openId : J ≅ 𝟭 _ := Adjunction.leftAdjointIdIso
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 B))
    (Etale.upperStarId (ModuleCat.{u + 1} A) B)
  let e := (interchange A (𝟙 B) c.i s (s ≫ c.i)
    (Category.id_comp _)).app (etaleConstant A B)
  let e' := e ≪≫
    (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) (s ≫ c.i)).mapIso
      ((Functor.mapDerivedCategoryPlusNatIso openId ≪≫
        Functor.mapDerivedCategoryPlusIdIso _).app (etaleConstant A B))
  let w : 𝟙 B = (s ≫ c.i) ≫ c.g := hs.symm.trans
    ((congrArg (fun f ↦ s ≫ f) c.comm).trans (Category.assoc _ _ _).symm)
  exact ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).mapIso
    (closedSingle A s).symm ≪≫
    (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) c.g).mapIso e' ≪≫
    (compositor A (s ≫ c.i) c.g (𝟙 B) w).symm.app (etaleConstant A B) ≪≫
    (directIdentity A B).app (etaleConstant A B)).symm

/-- The comparison of constants, including the scalar unit.
Source: Stacks Tags 099R and 095L
(blueprint: lem-pur-section-compact-source-exchange). -/
def compareConstant (B : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.obj
      (etaleConstant A B) ≅ proConstant A B :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B) 0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (SupportedConstantNormalization.compareUnit A B)

/-- The degree-zero descent of the canonical supported-constant counit mate.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def compareSupported {B X : Scheme.{u}} (s : B ⟶ X) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
      (etaleSupported A s) ⟶ proSupported A s :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) 0).hom.app _ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      (SupportedConstantNormalization.gamma A s)

/-- The actual compact-support site comparison with its supported-constant endpoint.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def sourceComparison [Finite A] {B X : Scheme.{u}} {h : X ⟶ B}
    (c : Compactification h) (s : B ⟶ X) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj
        (etaleSupported A s)) ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj
        (proSupported A s) :=
  (ProEtale.compactSupportSiteComparisonPlus A c).hom.app (etaleSupported A s) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map
      (compareSupported A s)

/-- Transport of the specified etale source with identity on the base constant.
This definition applies on arbitrary bases, including non-Noetherian B'.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def proSource [Finite A] {B X : Scheme.{u}} {h : X ⟶ B}
    (c : Compactification h) (s : B ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ h = 𝟙 B) :
    proConstant A B ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj
        (proSupported A s) :=
  (compareConstant A B).inv ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.map
      (etaleSource A c s hs).hom ≫ sourceComparison A c s

/-- Exact pro-etale pullback on constants with its scalar-preserving unit.
Source: Stacks Tag 095L (blueprint: lem-pur-section-compact-source-exchange). -/
def proConstantPull {B' B : Scheme.{u}} (g : B' ⟶ B) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj
      (proConstant A B) ≅ proConstant A B' :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g) 0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (SupportedConstantNormalization.unitIso A true g)

/-- The canonical supported-constant exchange in degree zero, on the etale site.
Source: Stacks Tag 0F7F (blueprint: lem-pur-section-compact-source-exchange). -/
def etaleBeta {B' B X' X : Scheme.{u}}
    {g : B' ⟶ B} {s' : B' ⟶ X'} {s : B ⟶ X} {v : X' ⟶ X}
    (sq : ChosenCartesianSquare g s' s v) :
    (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj
      (etaleSupported A s) ⟶ etaleSupported A s' :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (Etale.upperStar (ModuleCat.{u + 1} A) v) 0).hom.app _ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      (SupportedConstantNormalization.exchange A false sq)

/-- The canonical supported-constant exchange in degree zero, on the pro-etale site.
Source: Stacks Tag 0F7F and its site transport
(blueprint: lem-pur-section-compact-source-exchange). -/
def proBeta {B' B X' X : Scheme.{u}}
    {g : B' ⟶ B} {s' : B' ⟶ X'} {s : B ⟶ X} {v : X' ⟶ X}
    (sq : ChosenCartesianSquare g s' s v) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj
      (proSupported A s) ⟶ proSupported A s' :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (ProEtale.upperStar (ModuleCat.{u + 1} A) v) 0).hom.app _ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      (SupportedConstantNormalization.exchange A true sq)

/-- The actual pro-etale compactification exchange on D+, using the fully faithful
inclusion to express the existing ambient mate with exact inverse images.
Source: blueprint thm-cbc-finite-level-proetale, specified transported exchange
(blueprint: lem-pur-section-compact-source-exchange). -/
def proExchange [Finite A] {X' X B' B : Scheme.{u}}
    {v : X' ⟶ X} {h' : X' ⟶ B'} {h : X ⟶ B} {g : B' ⟶ B}
    (sq : IsPullback v h' h g) (c : Compactification h)
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj
      ((ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) c).obj M) ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj M) :=
  DerivedCategory.Plus.ι.preimage
    ((Functor.mapDerivedCategoryPlusCompatibility
      (ProEtale.upperStar (ModuleCat.{u + 1} A) g)).hom.app _ ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app M) ≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) g).inv.app _ ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app M.obj ≫
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) v).hom.app M.obj ≫
          (Functor.mapDerivedCategoryPlusCompatibility
      (ProEtale.upperStar (ModuleCat.{u + 1} A) v)).inv.app M) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).inv.app _)

/-- The exact closed-source normalization for the proper compactification (id,s).
Source: Stacks Tags 0F7J and 095L
(blueprint: lem-pur-section-compact-source-exchange). -/
def proClosedSingle {B X : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s]
    [IsNoetherian X] :
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper s)).obj (proConstant A B) ≅ proSupported A s := by
  have hc : IsCompl (Set.range s.base) (Set.range s.openComplement.ι.base) := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement]
    exact isCompl_compl
  letI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl
    (R := A) s s.openComplement.ι hc
  exact (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctorPlus.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso
        (Adjunction.leftAdjointIdIso
          (ProEtale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (𝟙 B))
          (ProEtale.upperStarId (ModuleCat.{u + 1} A) B)) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _).app (proConstant A B)) ≪≫
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) s)).app (proConstant A B) ≪≫
    (Functor.mapDerivedCategoryPlusSingleFunctor
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) s) 0).app _

/-- The specified composition inverse on a finite-type base, computed on any
compatible compactification tower, with the exact closed and identity normalizations.
Source: blueprint thm-sf-comp-composition and rank-one Thom proof, Step 3
(blueprint: lem-pur-section-compact-source-exchange). -/
def proCompositionInverse [Finite A] {B X : Scheme.{u}}
    [IsNoetherian B] [IsNoetherian X] {h : X ⟶ B}
    (c : Compactification h) (s : B ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ h = 𝟙 B) (T : Compactification.Triangle s h) :
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} A) c).obj (proSupported A s) ⟶ proConstant A B :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).map (proClosedSingle A s).inv ≫
  ProEtale.finiteCompactSiteCompositionAtWitness A (Compactification.ofIsProper s) c
    ((Compactification.ofIsProper (𝟙 B)).copy hs) T
    (etaleConstant A B) (proConstant A B) (compareConstant A B) ≫
  (ProEtale.finiteCompactSiteIdentityProPlus A B).hom.app (proConstant A B)

/-- The usual size lift of the prescribed finite coefficient quotient.
Source: blueprint rank-one Thom proof, finite-level convention
(blueprint: lem-pur-section-compact-source-exchange). -/
abbrev Coefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) : Type (u + 1) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)

/-- Finiteness of the prescribed quotient, transported through the standard size lift.
Source: def-weil-l-adic-coefficient-extension, finite quotient clause
(blueprint: lem-pur-section-compact-source-exchange). -/
instance coefficientFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Coefficient l E n) :=
  Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n (Fact.out))

```

## New

The declarations above, verbatim, occur in `Sheaf.Paper.SectionCompactSourceMaps`.
`Sheaf.Paper.SectionCompactSourceExchange` publicly imports that module. Thus every existing
importer receives the same declarations and defining terms through the same old import.
The original public imports are retained in both files.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionCompactSourceExchange | H7 | Publicly reexports all unchanged maps; proves the final conjunction from components. |
| Sheaf.Paper.LineZeroClassExchange | unclaimed in queue | Same public import interface and identical defining terms; no adaptation. |
| Sheaf.Paper.LineKummerFieldRealization | unclaimed in queue | Same public import interface and identical defining terms; no adaptation. |
| Sheaf.Paper.SectionSourceEtaleExchange | new, H7 | States the etale exchange component using the extracted maps. |
| Sheaf.Paper.SectionSourceProExchange | new, H7 | States the transport component using the extracted maps. |
| Sheaf.Paper.SectionSupportedComparisonIso | new, H7 | Supplies invertibility of the supported-constant comparison. |
| Sheaf.Paper.SectionSupportedProExchangeIso | new, H7 | Supplies invertibility of pro-etale supported exchange. |

The two existing rows are the complete direct-importer set found by searching both Lean
roots for imports of the item module. Transitive importers receive the same public API.
No target statement or meaning changes, and no consumer needs an adaptation.

## Status

landed 20261025T180738-L-4026443 2026-10-25 (merge of deliver/H7/Sheaf.Paper.SectionCompactSourceExchange)
