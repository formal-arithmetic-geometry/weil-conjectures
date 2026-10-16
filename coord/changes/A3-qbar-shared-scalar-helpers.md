# CategoryTheory.Mod.tensorπ_leftUnitor_hom

## Reason

Repair the return of head 96fd00dc8. Four private helper lemmas were copied into
`CondensedQbarScalarBasisPushforward` under a `qbar_` prefix. Their propositions
are identical to the existing source lemmas. Directly importing `Compatibility`
would create a cycle: that module already imports `CondensedQbarScalarBasis`.

Move the original four proved lemmas, under their original names and with their
unchanged hypotheses and proof bodies, into the lower support module
`Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward`. Make them public
there, remove the four old private declarations from `Compatibility`, and add a
proof-only support import there. Both consumers use the one shared declaration.
`Compatibility` is unclaimed in the current claims snapshot; this is the explicit
unclaimed-module adaptation permitted by the brief. The private scalar data definitions in the consumer are additionally changed to
abbreviations of the identical constructions in the support module; no target statement
or mathematical construction changes. All existing public declarations of `Compatibility` keep their signatures.
The support module is new relative to the landing base and has no existing consumers.
The private map/restriction and inverse-image scalar pipeline in the consumer is removed
because its only remaining result is supplied by the shared proved direct-image theorem.

## Old

In `Compatibility`, with the original variable contexts (the unitor statements have
`C`, `S`, the abelian monoidal hypotheses and the omitted assumptions exactly as in
that source file; the center statements have arbitrary categories `A` and `B`):

```lean
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma tensorπ_leftUnitor_hom (M : Mod C S) :
    tensorObjπ (regular S) M ≫ (λ_ M).hom.hom = γ[S,M.X] := by
  change coequalizer.π _ _ ≫
    ((_root_.Bimod.whiskerRight (toBimodRegularIso (R := S)).hom
        ((toBimod S).obj M)).hom ≫
      _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M)) = _
  rw [← Category.assoc]
  dsimp only [_root_.Bimod.whiskerRight]
  change (colimit.ι _ WalkingParallelPair.one ≫ colimMap _) ≫ _ = _
  rw [ι_colimMap]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom, id_whiskerRight]
  change (𝟙 (S ⊗ M.X) ≫ coequalizer.π _ _) ≫
    _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M) = _
  rw [Category.id_comp]
  dsimp only [_root_.Bimod.LeftUnitorBimod.hom]
  exact coequalizer.π_desc _ _

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma leftUnitor_inv_hom (M : Mod C S) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[S] ▷ M.X ≫ tensorObjπ (regular S) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [← comp_hom', Iso.inv_hom_id, id_hom']
  simp only [Category.assoc]
  rw [tensorπ_leftUnitor_hom, one_act, Iso.inv_hom_id]


include adj in
private lemma map_center_rightAdjoint
    (hF : ∀ X, F.map (τA.app X) = τB.app (F.obj X)) (Y : B) :
    G.map (τB.app Y) = τA.app (G.obj Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, hF]
  rw [adj.counit_naturality]
  exact τB.naturality (adj.counit.app Y)


private lemma map_center_of_iso (e : F ≅ G) (τA : CatCenter A) (τB : CatCenter B)
    (hG : ∀ X, G.map (τA.app X) = τB.app (G.obj X)) (X : A) :
    F.map (τA.app X) = τB.app (F.obj X) := by
  apply (cancel_mono (e.hom.app X)).1
  rw [e.hom.naturality, hG]
  exact τB.naturality _
```

The retained, unlanded support module had the same four lemmas privately named
`qbar_tensorπ_leftUnitor_hom`, `qbar_leftUnitor_inv_hom`,
`qbar_map_center_rightAdjoint`, and `qbar_map_center_of_iso`.

The consumer's five old private data definitions were:

```lean
private noncomputable def scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C S) : M ⟶ M :=
  (λ_ M).inv ≫ (regularLift (regular S) b ▷ M) ≫ (λ_ M).hom

private noncomputable def scalarNatEndo (b : 𝟙_ C ⟶ S) :
    𝟭 (Mod C S) ⟶ 𝟭 (Mod C S) where
  app M := scalarEndo b M
  naturality M N f := by
    apply hom_ext
    simp only [CategoryTheory.Functor.id_map, comp_hom', scalarEndo_hom]
    rw [leftUnitor_inv_naturality_assoc f.hom, whisker_exchange_assoc, ← act_hom]
    simp only [Category.assoc]

private noncomputable def complexCenter (τ : CatCenter A) :
    CatCenter (CochainComplex A ℤ) where
  app K :=
    { f i := τ.app (K.X i)
      comm' i j _ := by simpa using (τ.naturality (K.d i j)).symm }
  naturality K L f := by
    ext i
    exact τ.naturality (f.f i)

private noncomputable def homotopyCenter (τ : CatCenter A) :
    CatCenter (HomotopyCategory A (.up ℤ)) where
  app K := (HomotopyCategory.quotient A (.up ℤ)).map ((complexCenter τ).app K.as)
  naturality K L f := by
    let f' : K.as ⟶ L.as := (HomotopyCategory.quotient A (.up ℤ)).preimage f
    have hf : (HomotopyCategory.quotient A (.up ℤ)).map f' = f :=
      (HomotopyCategory.quotient A (.up ℤ)).map_preimage f
    simp only [CategoryTheory.Functor.id_map]
    rw [← hf, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (HomotopyCategory.quotient A (.up ℤ)).map
      ((complexCenter τ).naturality f')

private noncomputable def derivedCenter (τ : CatCenter A) : CatCenter (DerivedCategory A) :=
  (homotopyCenter τ).localization DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
```

The old finite-field freeness proof was:

```lean
private theorem padicSubfield_isFree (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Mod.IsFree (continuousMapRingObj.{u} E)
      ((Mod.comap (padicSubfieldRingObjMap ℓ h)).obj
        (Mod.regular (continuousMapRingObj F))) := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ℚ_[ℓ] F := F.2
  have : FiniteDimensional E F := FiniteDimensional.right ℚ_[ℓ] E F
  let b := Module.finBasis E F
  refine ⟨Module.finrank E F, ⟨continuousBasisSheafIso
    (continuous_subtype_val.subtype_mk _) _ b ?_⟩⟩
  intro i
  exact ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
```

## New

The following declarations live once, in the exposed public section of
`CondensedQbarScalarBasisPushforward`, with the same original variable contexts.
Their proofs are the original proofs; source docstrings are added.

```lean
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
lemma tensorπ_leftUnitor_hom (M : Mod C S) :
    tensorObjπ (regular S) M ≫ (λ_ M).hom.hom = γ[S,M.X] := by
  change coequalizer.π _ _ ≫
    ((_root_.Bimod.whiskerRight (toBimodRegularIso (R := S)).hom
        ((toBimod S).obj M)).hom ≫
      _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M)) = _
  rw [← Category.assoc]
  dsimp only [_root_.Bimod.whiskerRight]
  change (colimit.ι _ WalkingParallelPair.one ≫ colimMap _) ≫ _ = _
  rw [ι_colimMap]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom, id_whiskerRight]
  change (𝟙 (S ⊗ M.X) ≫ coequalizer.π _ _) ≫
    _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M) = _
  rw [Category.id_comp]
  dsimp only [_root_.Bimod.LeftUnitorBimod.hom]
  exact coequalizer.π_desc _ _

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
lemma leftUnitor_inv_hom (M : Mod C S) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[S] ▷ M.X ≫ tensorObjπ (regular S) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [← comp_hom', Iso.inv_hom_id, id_hom']
  simp only [Category.assoc]
  rw [tensorπ_leftUnitor_hom, one_act, Iso.inv_hom_id]


include adj in
lemma map_center_rightAdjoint
    (hF : ∀ X, F.map (τA.app X) = τB.app (F.obj X)) (Y : B) :
    G.map (τB.app Y) = τA.app (G.obj Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, hF]
  rw [adj.counit_naturality]
  exact τB.naturality (adj.counit.app Y)


lemma map_center_of_iso (e : F ≅ G) (τA : CatCenter A) (τB : CatCenter B)
    (hG : ∀ X, G.map (τA.app X) = τB.app (G.obj X)) (X : A) :
    F.map (τA.app X) = τB.app (F.obj X) := by
  apply (cancel_mono (e.hom.app X)).1
  rw [e.hom.naturality, hG]
  exact τB.naturality _
```

`Compatibility` removes these four local declarations and adds:

```lean
import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward
```

Its existing proof references keep the original names. The support module removes
the four prefixed names and uses the original names in its scalar and adjunction
calculations. No consumer can depend on the old private names outside their module.

The consumer keeps its five private names as abbreviations of the shared data:

```lean
private noncomputable abbrev scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C S) : M ⟶ M :=
  CategoryTheory.Mod.qbar_scalarEndo b M

private noncomputable abbrev scalarNatEndo (b : 𝟙_ C ⟶ S) :
    𝟭 (Mod C S) ⟶ 𝟭 (Mod C S) :=
  CategoryTheory.Mod.qbar_scalarNatEndo b

private noncomputable abbrev complexCenter (τ : CatCenter A) :
    CatCenter (CochainComplex A ℤ) :=
  CategoryTheory.qbar_complexCenter τ

private noncomputable abbrev homotopyCenter (τ : CatCenter A) :
    CatCenter (HomotopyCategory A (.up ℤ)) :=
  CategoryTheory.qbar_homotopyCenter τ

private noncomputable abbrev derivedCenter (τ : CatCenter A) : CatCenter (DerivedCategory A) :=
  CategoryTheory.qbar_derivedCenter τ
```

The localized center `qbar_derivedCenter` is `@[no_expose]` and its computation
lemma `qbar_derivedCenter_Qh` is public. The consumer's private duplicate
`derivedCenter_Qh` is removed, and its caller rewrites with the shared public lemma.
The support module additionally constructs the scalar-unit leg as `qbar_scalarUnitLeg`,
with a non-exposed body and the proved equation `qbar_scalarUnitLeg_eq`. The unit theorem
uses that compact morphism name; the assigned proof rewrites its equation. Rewriting
gives the previous full statement, with exactly the same hypotheses and conclusion.
No scalar or adjunction construction changes mathematically.

Its existing `scalarEndo_hom` delegates to `qbar_scalarEndo_hom`, and
`lowerStar_derivedScalarEndo_of_eq` delegates to `qbar_lowerStar_derivedScalarEndo_of_eq`.
The now-unused private declarations `map_scalarEndo`, `map_derivedCenter`,
`comap_scalarEndo`, `extendIso_scalarEndo`, `upperStar_scalarEndo`, and
`lowerStar_derivedScalarEndo` are pruned. All of these old private interfaces have no
external callers, as verified by `tools/downstream.py --uses` for all eleven names.
The public-interface comparison reports no changed declarations. The public consumer
statements and all field/coefficient constructions are unchanged. None of the five private
scalar data names occurs in a target statement or its defining coefficient objects.

Additional performance repair in this delivery: `qbar_complexCenter` and
`qbar_homotopyCenter` have non-exposed bodies with the proved equations
`qbar_complexCenter_app_f` and `qbar_homotopyCenter_app`. The consumer rewrites these
characterizations at its two termwise calculations. The ordinary finite-basis unit
property is named by the private definition `Mod.BasisUnitIsIso`; its body is precisely
the old `hX`/`hY` field formula. The finite-basis record uses this name for its fields.
The fields have the identical meaning, and the construction and elimination use definitional
conversion. No public signature changes.

The finite-field freeness proof now specializes a generic, proved finite-dimensional
continuous-coordinate lemma. Its chosen finite basis is destructured before the sheaf
comparison is instantiated, so no large chosen-basis construction is repeatedly unfolded.
The original canonical field, module, topology, coefficient maps and finite basis theorem
are used. Every choice here comes from a proved theorem. The code remains in the original
module; no file or proof is split to meet the compile limit.

The finite-field specialization now uses this proved generic argument:

```lean
/-- Finite-dimensional continuous coordinates give a free condensed scalar module. -/
private theorem isFree_continuousMapRingObj
    {K R S : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    [ContinuousSMul K R] [ContinuousSMul K S] [FiniteDimensional K S]
    (ha : Continuous (algebraMap R S)) :
    Mod.IsFree (continuousMapRingObj.{u} R)
      ((Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (continuousMapRingSheafMap (algebraMap R S) ha))).obj
            (Mod.regular (continuousMapRingObj S))) := by
  have : FiniteDimensional R S := FiniteDimensional.right K R S
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R S) :=
    ⟨_, ⟨Module.finBasis R S⟩⟩
  refine ⟨n, ⟨continuousBasisSheafIso ha n b ?_⟩⟩
  intro i
  exact ((b.coord i).restrictScalars K).continuous_of_finiteDimensional

private theorem padicSubfield_isFree (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Mod.IsFree (continuousMapRingObj.{u} E)
      ((Mod.comap (padicSubfieldRingObjMap ℓ h)).obj
        (Mod.regular (continuousMapRingObj F))) := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ℚ_[ℓ] F := F.2
  exact isFree_continuousMapRingObj (K := ℚ_[ℓ])
    (continuous_subtype_val.subtype_mk _)
```

The compact finite-basis property is defined in a braided category, which is all
the ordinary extension unit requires. This avoids comparing two presentations of
the same symmetric-category braiding while inferring commutativity of concrete rings.

```lean
section BasisUnitProperty
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The ordinary extension unit is a scalar-basis decomposition. Naming the property
keeps concrete module structures folded in the finite-basis record. -/
private def BasisUnitIsIso {I : Type*} [Finite I] (τ : I → CatCenter (Mod C S)) : Prop :=
  ∀ M : Mod C R, IsIso (biproduct.desc fun i ↦
    (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map ((τ i).app _))
end BasisUnitProperty
```

The two private record fields use this property at the coefficient maps for Y and X.
Unfolding it gives their original formulas, with exactly the same inferred structures.

The transported finite basis is abstracted through the following **proved** existence
statement inside the explicit finite-basis constructor. This is classical choice from a
complete proof of existence, not from an admitted theorem. It prevents later scalar-unit
matching from unfolding the whole pullback/basis transport at each use.

```lean
  let htransport : ∃ eX :
      (Mod.comap (coefficientMap a X)).obj (Mod.regular (condensedRingObj Λ' X)) ≅
        Mod.finiteFree (condensedRingObj Λ X) n,
      ∀ i : Fin n, η[condensedRingObj Λ X] ≫ (biproduct.ι _ i ≫ eX.inv).hom =
        CategoryTheory.Functor.LaxMonoidal.ε P ≫ P.map (bY i) ≫ s.hom := by
    refine ⟨Mod.freeRestrictedRegularIsoOfRingIso (P.map (coefficientMap a Y))
      (coefficientMap a X) r s hsquare n eP, ?_⟩
    intro i
    exact Mod.mappedRingIsoBasisVector
      (C := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (D := Sheaf (ProEt.topology X) Ab.{u + 1})
      (R := condensedRingObj Λ Y) (S := condensedRingObj Λ' Y)
      P (coefficientMap a Y) (coefficientMap a X) r s hsquare n eY i
  let eX := Classical.choose htransport
  have hb := Classical.choose_spec htransport
  let bX (i : Fin n) : 𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶
      condensedRingObj Λ' X :=
    η[condensedRingObj Λ X] ≫ (biproduct.ι _ i ≫ eX.inv).hom
```

The finite-basis record is checked with transparency respected. Its two calculation proofs
retain the original transparency setting; they use the characterizing lemmas rather than
expanding derived-functor and transported-basis definitions. The private finite-basis transport
constructors are locally irreducible after their computation lemmas. No public declaration's
signature or body is replaced by a private helper.

The regular-module scalar endomorphism and its natural transformation are also
non-exposed explicit definitions. The existing `qbar_scalarEndo_hom` formula and new,
proved `qbar_scalarNatEndo_app` component equation replace body unfolding in consumers.
The original definition bodies are unchanged. The finite-unit proofs simplify only by
that component equation before applying the existing basis-unit theorem.

The fifteen existing private finite-basis and continuous-coordinate construction bodies
are marked `@[no_expose]` without changing their terms or written signatures. Their proved
characterizations remain available; the only external uses are the unchanged calls to
`continuousBasisSheafIso` and `mapFreeRestrictedRegularIso` in
`Sheaf.Paper.CondensedFlatCoefficientCalculus`. Those callers use the declared isomorphism
types, not their implementations.

Targets using the relocated scalar data require the normal definition review. The
constructor bodies are unchanged, their public computation equations are proved, and
the proposition-name identity was checked by applying the new theorem at its old full type.

The repair also removes the redundant anonymous example at the end of the consumer.
The old code, in its existing `Push` context, was:

```lean
variable [HasCompactification f]

/-- **(Shriek)** is an isomorphism for a finite extension `F/E`, on all unbounded objects. -/
example {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjMap ℓ h) f) :=
  inferInstance
```

The new code omits this anonymous demonstration and the variable used only by it.
No named declaration, instance, or public signature is removed. The retained profile
attributed 24.6 seconds to linting this final concrete command. The full consumer without
it compiled in 46.1 seconds, versus 58.7 seconds in the immediately preceding complete
exporting compile with it. This prunes a redundant check; no proof file is split and
no compilation limit is increased.

## Users

`tools/downstream.py` reports 93 downstream modules of `Compatibility`. Exact-name
searches find all original uses inside `Compatibility` only. Every downstream module
is listed below with its current holder. They need no edits: the moved helpers were
private, every existing public signature and definition is unchanged, and the added
import is proof-only. The three new sandbox modules use the shared support API.

Compilation exposed the large derived elaborations. The two scalar-basis
statement modules locally keep `Mod.derivedExtendMapDerivedCategoryAdjunction`,
`upperStarFromPoint`, and `ProEtale.upperStar` folded. In `Compatibility`, the shared
scalar constructions are locally semireducible for its finite-basis computation, then
folded after that computation. The continuous-basis isomorphisms are also kept folded once
constructed; downstream proofs use their isomorphism API. The canonical comparison definitions remain locally folded
for the bounded push proof. These are ordinary permitted reducibility attributes; no unsafe
reducibility option is used. A profiling run and command timings are retained in
`scratchpad/consumer-profile.log` and `scratchpad/consumer-times.log`; the initial consumer
compile exceeded 60 seconds. No compile limit is increased.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | Share four helpers, scalar constructions, and the derived-center characterization; remove duplicate private pipelines. Public signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No adaptation; existing public API unchanged. |
| TargetsCheck | unclaimed | No adaptation; existing public API unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation; existing public API unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No adaptation; existing public API unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No adaptation; existing public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward | unclaimed | One shared helper proof per proposition; explicit scalar-unit construction and characterizing equations. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit | unclaimed | Same unit proposition using compact scalar-unit morphism name. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis | A3 | Same proposition under an exposed definition; use scalar-unit equation in proof. |

## Status

landed 20261016T173551-L-1931163 2026-10-16 (merge of deliver/A3/Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis)
