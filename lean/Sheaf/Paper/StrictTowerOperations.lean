/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.CompletedRlimFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Canonical operations on strict module towers

Source: blueprint completed-exchange-coherence, first two proof sentences;
Stacks 07A7 and 0D6D (blueprint: def-weil-pbc-strict-tower-operations).

## Main definitions

* `exchangeTowerPull`, `exchangeTowerPush`: strict diagram derived functors.
* `exchangeTowerAdjunction`: the derived termwise normalized module adjunction.
* `StrictTowerRingedSquare.exchangeTowerSquare`: canonical pullback composition.
* `StrictTowerRingedSquare.exchangeTowerMate`: its specified adjunction mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Coefficient sheaves and their compatible inverse-image identifications on a square.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
structure StrictTowerRingedSquare
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) where
  RY : Sheaf (ProEt.topology Y) CommRingCat.{t + 1}
  RX : Sheaf (ProEt.topology X) CommRingCat.{t + 1}
  RY' : Sheaf (ProEt.topology Y') CommRingCat.{t + 1}
  RX' : Sheaf (ProEt.topology X') CommRingCat.{t + 1}
  cf : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj RY ≅ RX
  cg : (proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj RY ≅ RY'
  cg' : (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).obj RX ≅ RX'
  cf' : (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).obj RY' ≅ RX'
  coherent : HEq (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
    (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf')

/-- Strict towers over an arbitrary coefficient sheaf on the original small site.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowers (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  ℕᵒᵖ ⥤ proEtaleRingModules T R

/-- Standard localization of strict towers, with the actual two site universes retained.
Source: strict normalization, paragraph 2
(blueprint: def-weil-pbc-strict-tower-operations). -/
instance exchangeTowers_hasDerived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    HasDerivedCategory (exchangeTowers T R) := HasDerivedCategory.standard _

/-- Constant coefficients on the small pro-etale site, in the sheaf-value universe.
Source: strict normalization, paragraph 2; Stacks 00YV
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeConstantRing (T : Scheme.{t}) (A : Type (t + 1)) [CommRing A] :=
  adicLisseConstantRing T A

/-- Inverse image preserves the specific constant-section comparison for every ring.
Source: Stacks 00VC, 07A7; strict normalization, paragraph 2
(blueprint: def-weil-pbc-strict-tower-operations).
Proof: the constant sheaf is inverse image from sets. Composition of inverse images
identifies inverse image of a constant sheaf with the same constant sheaf. On constant
sections this comparison is the sheafification adjunct defining the recorded map.
Thus that particular map is invertible; no finiteness of A is required. -/
theorem exchangeConstantComparison_isIso {U V : Scheme.{t}} (f : U ⟶ V)
    (A : Type (t + 1)) [CommRing A] :
    IsIso ((proEtaleConstantComparison f).app (CommRingCat.of A)) := by
  let B := CommRingCat.of A
  let T := ⊤_ V.ProEt
  let hT := terminalIsTerminal (C := V.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let adjY := constantSheafAdj (ProEt.topology V) CommRingCat.{t + 1} hT
  let adjX := constantSheafAdj (ProEt.topology U) CommRingCat.{t + 1} hGT
  let adj := (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{t + 1})).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{t + 1} (ProEt.topology V) (ProEt.topology U) (op T))
  have he : (proEtaleConstantComparison f).app B =
      (adj.leftAdjointUniq adjX).hom.app B := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{t + 1})).homEquiv _ _
      ((proEtaleConstantComparison f).app B) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((proEtaleSheafAdjunction f CommRingCat.{t + 1}).homEquiv _ _
        (((proEtaleSheafAdjunction f CommRingCat.{t + 1}).homEquiv _ _).symm
          (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} B))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{t + 1} hT).comp
      (sheafificationAdjunction (ProEt.topology V) CommRingCat.{t + 1})).homEquiv _ _
        (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} B) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{t + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{t + 1}).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology V) CommRingCat.{t + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 B ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The constant coefficient identification, fixed by the constant-section map.
Source: strict normalization, paragraph 2; Stacks 00VC
(blueprint: def-weil-pbc-strict-tower-operations). -/
def exchangeConstantIso {U V : Scheme.{t}} (f : U ⟶ V)
    (A : Type (t + 1)) [CommRing A] :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj (exchangeConstantRing V A) ≅
      exchangeConstantRing U A :=
  @asIso _ _ _ _ ((proEtaleConstantComparison f).app (CommRingCat.of A))
    (exchangeConstantComparison_isIso f A)

variable {U V : Scheme.{t}} (f : U ⟶ V)
  (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
  (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)

/-- Termwise inverse image of strict module towers with identified coefficients.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerModulePull : exchangeTowers V R ⥤ exchangeTowers U S :=
  (Functor.whiskeringRight _ _ _).obj (proEtaleRingModulePullback f R S c)

/-- Termwise direct image, including all transition maps.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerModulePush : exchangeTowers U S ⥤ exchangeTowers V R :=
  (Functor.whiskeringRight _ _ _).obj (proEtaleRingModuleDirectImage f R S c)

/-- Exactness of termwise inverse image on the whole strict diagram category.
Source: strict normalization, proof step 1; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations).
Proof: kernels and cokernels in the functor category are pointwise. The ordinary
identified-coefficient module inverse image preserves both, since its coefficient
map is an isomorphism. Evaluation at every index proves both preservation claims. -/
theorem exchangeTowerModulePull_exact :
    PreservesFiniteLimits (exchangeTowerModulePull f R S c) ∧
      PreservesFiniteColimits (exchangeTowerModulePull f R S c) := by
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Left exactness on strict towers. Source: strict normalization, proof step 1
(blueprint: def-weil-pbc-strict-tower-operations). -/
instance exchangeTowerModulePull_finiteLimits :
    PreservesFiniteLimits (exchangeTowerModulePull f R S c) :=
  (exchangeTowerModulePull_exact f R S c).1

/-- Right exactness on strict towers. Source: strict normalization, proof step 1
(blueprint: def-weil-pbc-strict-tower-operations). -/
instance exchangeTowerModulePull_finiteColimits :
    PreservesFiniteColimits (exchangeTowerModulePull f R S c) :=
  (exchangeTowerModulePull_exact f R S c).2

/-- Exact termwise inverse image descends to the localization of strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerPull : DerivedCategory (exchangeTowers V R) ⥤
    DerivedCategory (exchangeTowers U S) :=
  (exchangeTowerModulePull f R S c).mapDerivedCategory

/-- Total right derived termwise direct image, using K-injective strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerPush : DerivedCategory (exchangeTowers U S) ⥤
    DerivedCategory (exchangeTowers V R) :=
  (exchangeTowerModulePush f R S c).rightDerivedFunctor

/-- The ordinary adjunction on strict towers is the termwise normalized module adjunction.
Source: strict normalization, proof step 1; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
def exchangeTowerModuleAdjunction :
    exchangeTowerModulePull f R S c ⊣ exchangeTowerModulePush f R S c :=
  (proEtaleRingModuleAdjunction f R S c).whiskerRight ℕᵒᵖ

/-- The derived adjunction uses precisely the termwise normalized module adjunction.
Source: strict normalization, proof step 1; Stacks 0DVC
(blueprint: def-weil-pbc-strict-tower-operations). -/
def exchangeTowerAdjunction :
    exchangeTowerPull f R S c ⊣ exchangeTowerPush f R S c :=
  (exchangeTowerModuleAdjunction f R S c).mapDerivedCategoryRightDerivedAdjunction

/-- Sectionwise normalization of the ordinary composition comparison. Its right-adjoint
conjugate is exactly the canonical fibre-product pasting map on every section.
Source: Stacks 03D8 and 0D6D
(blueprint: def-weil-pbc-strict-tower-operations). -/
def ExchangeModuleCompositionNormalized {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ)
    (a : proEtaleRingModulePullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingModulePullback k RV RW ck ⋙ proEtaleRingModulePullback h RW RZ ch) :
    Prop :=
  ∀ (N : proEtaleRingModules Z RZ) (U : V.ProEt)
    (m : ((proEtaleRingModuleDirectImage h RW RZ ch ⋙
      proEtaleRingModuleDirectImage k RV RW ck).obj N).val.obj (op U)),
    ((conjugateIsoEquiv
        ((proEtaleRingModuleAdjunction k RV RW ck).comp
          (proEtaleRingModuleAdjunction h RW RZ ch))
        (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
          (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)) a).hom.app N).val.app
            (op U) m =
      N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m

/-- There is a unique composition comparison with the sectionwise canonical conjugate.
Source: Stacks 03D8 and 0D6D
(blueprint: def-weil-pbc-strict-tower-operations).
Proof: proEtaleRingDerivedPullbackComposition supplies ordinary adjunctions whose
units are the canonical tensor-unit sections, a sectionwise pasting isomorphism of
right adjoints, and its conjugate ordinary pullback comparison. These adjunctions
agree with proEtaleRingModuleAdjunction: the units agree on every section, hence
agree as natural transformations, and determine the adjunction. Thus its comparison
satisfies this normalization. Sectionwise equality determines the direct-image
natural transformation uniquely. The conjugate-isomorphism equivalence is bijective,
so the pullback comparison is unique as well. -/
theorem exchangeModuleComposition_existsUnique {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ) :
    ∃! a : proEtaleRingModulePullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingModulePullback k RV RW ck ⋙ proEtaleRingModulePullback h RW RZ ch,
      ExchangeModuleCompositionNormalized h k RV RW RZ ck ch a := by
  obtain ⟨adjk, adjh, adjhk, _, _, _, d, hd, _⟩ :=
    proEtaleRingDerivedPullbackComposition h k RV RW RZ ck ch
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl
  let e := conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction k RV RW ck).comp
      (proEtaleRingModuleAdjunction h RW RZ ch))
    (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch))
  refine ⟨e.symm d, ?_, ?_⟩
  · change ∀ N U m, ((e (e.symm d)).hom.app N).val.app (op U) m = _
    rw [e.apply_symm_apply]
    exact hd
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    exact (ha N U.unop m).trans (hd N U.unop m).symm

/-- The ordinary canonical pullback composition, fixed by its sectionwise conjugate
and the existing tensor-unit-normalized module adjunctions.
Source: Stacks 03D8 and 0D6D
(blueprint: def-weil-pbc-strict-tower-operations). -/
def exchangeModuleComposition {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ) :
    proEtaleRingModulePullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingModulePullback k RV RW ck ⋙ proEtaleRingModulePullback h RW RZ ch :=
  (exchangeModuleComposition_existsUnique h k RV RW RZ ck ch).choose

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- The two coefficient paths agree over the equality of composite scheme maps.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations).
Proof: the commutative scheme square identifies f' followed by g with g' followed
by f. The coefficient coherence field, in the reverse direction, identifies the
isomorphism components over that equality. Dependent-pair extensionality gives
the displayed equality, so transport does not choose any additional ring map. -/
theorem StrictTowerRingedSquare.exchangeCoefficients_eq (r : StrictTowerRingedSquare sq) :
    (⟨f' ≫ g, proEtaleRingCompositeCoefficients f' g r.RY r.RY' r.RX' r.cg r.cf'⟩ :
      Σ q : X' ⟶ Y,
        (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj r.RY ≅ r.RX') =
      ⟨g' ≫ f, proEtaleRingCompositeCoefficients g' f r.RY r.RX r.RX' r.cf r.cg'⟩ := by
  exact Sigma.ext sq.w.symm r.coherent.symm

/-- The canonical module pullback comparison around the chosen ringed square.
Source: strict normalization, paragraph 2; Stacks 07A7, 0D6D
(blueprint: def-weil-pbc-strict-tower-operations). -/
def StrictTowerRingedSquare.exchangeModuleSquare (r : StrictTowerRingedSquare sq) :
    proEtaleRingModulePullback g r.RY r.RY' r.cg ⋙
        proEtaleRingModulePullback f' r.RY' r.RX' r.cf' ≅
      proEtaleRingModulePullback f r.RY r.RX r.cf ⋙
        proEtaleRingModulePullback g' r.RX r.RX' r.cg' := by
  let a := (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf').symm
  let b := exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg'
  let F := fun z : (Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj r.RY ≅ r.RX') ↦
    proEtaleRingModulePullback z.1 r.RY r.RX' z.2
  have hfun := congrArg F r.exchangeCoefficients_eq
  let a' :
      proEtaleRingModulePullback g r.RY r.RY' r.cg ⋙
          proEtaleRingModulePullback f' r.RY' r.RX' r.cf' ≅
        proEtaleRingModulePullback (g' ≫ f) r.RY r.RX'
          (proEtaleRingCompositeCoefficients g' f r.RY r.RX r.RX' r.cf r.cg') :=
    a ≪≫ eqToIso hfun
  exact a' ≪≫ b

/-- The strict square is obtained by termwise application before localization.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
def StrictTowerRingedSquare.exchangeTowerSquare (r : StrictTowerRingedSquare sq) :
    exchangeTowerPull g r.RY r.RY' r.cg ⋙ exchangeTowerPull f' r.RY' r.RX' r.cf' ≅
      exchangeTowerPull f r.RY r.RX r.cf ⋙ exchangeTowerPull g' r.RX r.RX' r.cg' :=
  (Functor.mapDerivedCategoryCompIso
    (exchangeTowerModulePull g r.RY r.RY' r.cg)
    (exchangeTowerModulePull f' r.RY' r.RX' r.cf')).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (F := exchangeTowerModulePull g r.RY r.RY' r.cg ⋙
      exchangeTowerModulePull f' r.RY' r.RX' r.cf')
    (G := exchangeTowerModulePull f r.RY r.RX r.cf ⋙
      exchangeTowerModulePull g' r.RX r.RX' r.cg')
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso r.exchangeModuleSquare) ≪≫
  Functor.mapDerivedCategoryCompIso
    (exchangeTowerModulePull f r.RY r.RX r.cf)
    (exchangeTowerModulePull g' r.RX r.RX' r.cg')

/-- The canonical mate in the derived category of strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
def StrictTowerRingedSquare.exchangeTowerMate (r : StrictTowerRingedSquare sq) :
    exchangeTowerPush f r.RY r.RX r.cf ⋙ exchangeTowerPull g r.RY r.RY' r.cg ⟶
      exchangeTowerPull g' r.RX r.RX' r.cg' ⋙ exchangeTowerPush f' r.RY' r.RX' r.cf' :=
  mateEquiv (exchangeTowerAdjunction f r.RY r.RX r.cf)
    (exchangeTowerAdjunction f' r.RY' r.RX' r.cf') r.exchangeTowerSquare.hom


end AlgebraicGeometry.Scheme
