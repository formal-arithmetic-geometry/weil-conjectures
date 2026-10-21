# Condensed lisse evaluation data ownership

## Reason

Use the current restored module and prove its evaluation/equivalence
argument. The separated realization and comparison lemmas need its canonical
functors in their signatures. Keeping those functors in the theorem module
would create an import cycle. Move the thirty existing data declarations to
`Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel` and publicly import it
from `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation`.

Names, types, universes, attributes and bodies of the moved declarations stay
verbatim; only their documentation blueprint labels change to the new owner.
No target statement or mathematical definition changes. The original theorem
also retains its exact signature. This is an ownership extraction, not a
replacement construction or a weakening of the statement.

## Old

The following definitions were declared in the current restored
`Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation`:

```lean
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  [(J.W (A := Ab.{u + 1})).IsMonoidal]
  (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]

/-- The actual commutative section-ring sheaf, reconstructed from the coefficient object.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
abbrev ringSheaf : Sheaf J CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J O

/-- The ordinary unbounded derived category, with ordinary relative derived tensor.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
abbrev D := DerivedCategory (Mod (Sheaf J Ab.{u + 1}) O)

/-- The section ring at the terminal site object, rather than an auxiliary ring parameter.
Source: HRS Lemma 4.1 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
abbrev A (U : C) : CommRingCat.{u + 1} := (ringSheaf J O).obj.obj (op U)

/-- The constant-section homomorphism is the actual constant-sheaf adjunction counit.
Source: HRS (3.2) (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def scalarMap (U : C) (hU : IsTerminal U) : realizationRing J (A J O U) ⟶ ringSheaf J O :=
  (constantSheafAdj J CommRingCat.{u + 1} hU).counit.app (ringSheaf J O)

/-- The standard localization size for modules over the constant coefficient sheaf.
Source: Stacks 05RU (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
instance constantHasDerived (U : C) :
    HasDerivedCategory.{u + 2} (realizationModules J (A J O U)) :=
  HasDerivedCategory.standard _

/-- The standard localization size for sectionwise coefficient modules.
Source: Stacks 05RU (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
instance sectionHasDerived : HasDerivedCategory.{u + 2}
    (SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ringSheaf J O))) := HasDerivedCategory.standard _

/-- The universal derived coefficient extension, with its fixed K-flat counit.
Source: HRS (3.2), Stacks 06YY
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def extensionModel (U : C) (hU : IsTerminal U) :=
  SheafOfModules.canonicalDerivedChangeOfRingsModel (scalarMap J O U hU)

/-- The canonical functor Q ↦ O tensor over constant A with constant Q.
Source: HRS (3.2) and Remark 3.2
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def F (U : C) (hU : IsTerminal U) :
    DerivedCategory (ModuleCat.{u + 1} (A J O U)) ⥤ D J O :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  letI := Functor.additive_of_preserves_binary_products e.inverse
  commutativeSiteDerivedConstantModuleFunctor J (A J O U) ⋙
    (extensionModel J O U hU).T ⋙ e.inverse.mapDerivedCategory

/-- Actual module evaluation after the sectionwise/internal equivalence.
Source: HRS Lemma 4.1 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def sections (U : C) : Mod (Sheaf J Ab.{u + 1}) O ⥤ ModuleCat.{u + 1} (A J O U) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O).functor ⋙
    SheafOfModules.evaluation _ (op U)

/-- Module evaluation is additive because it preserves sums of maps on every section.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
instance sectionsAdditive (U : C) : (sections J O U).Additive :=
  letI := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O).functor
  letI : (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ringSheaf J O)) (op U)).Additive :=
    inferInstanceAs ((SheafOfModules.forget _ ⋙
      PresheafOfModules.evaluation _ (op U))).Additive
  inferInstanceAs ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    J O).functor ⋙ SheafOfModules.evaluation _ (op U)).Additive

/-- Derived global sections are the right derived functor of actual module evaluation.
Source: HRS Lemma 4.1 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def G (U : C) : D J O ⥤ DerivedCategory (ModuleCat.{u + 1} (A J O U)) :=
  (sections J O U).rightDerivedFunctor

/-- The full subcategory of dualizable objects, using both triangle identities.
Source: HRS Definition 3.3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def lisse : ObjectProperty (D J O) := fun K ↦ IsDualizable K

/-- The full subcategory defined by bounded finite projective representatives.
Source: HRS Lemma 4.1 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def perfect (U : C) : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} (A J O U))) :=
  fun Q ↦ DerivedCategory.IsPerfectRingComplex Q

/-- Preservation of the ordinary Koszul braiding by the strong monoidal realization.
Source: HRS (3.1) (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def strongSymmetric (U : C) (hU : IsTerminal U) : Prop :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} (A J O U))
  letI := DerivedCategory.braidedCategory' (Mod (Sheaf J Ab.{u + 1}) O)
  Nonempty (F J O U hU).Braided

/-- The complete evaluation claim on the fixed canonical functors. Exact means
triangulated; it imposes no t-exactness. Both natural identifications specify the
restriction of F and its inverse G on the two actual full subcategories.
Source: HRS Lemma 4.1(1)--(2)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def Statement (U : C) (hU : IsTerminal U) : Prop :=
  Nonempty (F J O U hU).FullyFaithful ∧
  (∃ (_ : (F J O U hU).CommShift ℤ), (F J O U hU).IsTriangulated) ∧
  strongSymmetric J O U hU ∧
  ∃ e : (perfect J O U).FullSubcategory ≌ (lisse J O).FullSubcategory,
    Nonempty (e.functor ⋙ (lisse J O).ι ≅ (perfect J O U).ι ⋙ F J O U hU) ∧
    Nonempty (e.inverse ⋙ (perfect J O U).ι ≅ (lisse J O).ι ⋙ G J O U)

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restriction to the genuine profinite slice site, with finite jointly surjective covers.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
abbrev profiniteCoefficient (S : Profinite.{u}) :=
  ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).obj Λ

/-- The restricted coefficient multiplication and unit are induced by restriction.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
instance profiniteCoefficientMon (S : Profinite.{u}) : MonObj (profiniteCoefficient Λ S) :=
  ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).monObjObj Λ

/-- Restriction preserves commutativity of the condensed ring.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
instance profiniteCoefficientComm (S : Profinite.{u}) :
    IsCommMonObj (profiniteCoefficient Λ S) :=
  Functor.isCommMonObj_obj

/-- The ring of sections of the restricted coefficient is canonically Λ(S).
The comparison uses the monoidal restriction isomorphism, preserving multiplication and unit.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def profiniteSectionRingIso (S : Profinite.{u}) :
    (condensedSectionRing Λ).obj.obj (op S) ≅
      Evaluation.A ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ S) (Over.mk (𝟙 S)) := by
  let J := coherentTopology Profinite.{u}
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (Over.forget S) Ab.{u + 1} (J.over S) J
  let z := ((Functor.mapCommMonCompIso (F := sheafToPresheaf J Ab.{u + 1})
      (G := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj (Over.forget S).op)).symm ≪≫
    Functor.mapCommMonNatIso e ≪≫
    Functor.mapCommMonCompIso (F := J.overPullback Ab.{u + 1} S)
      (G := sheafToPresheaf (J.over S) Ab.{u + 1})).app (CommMon.mk Λ)
  let w := (Monoidal.commMonFunctorCategoryEquivalence (Over S)ᵒᵖ Ab.{u + 1}).functor.mapIso z
  exact InternalAbelianSheafModule.commMonToRing.mapIso (w.app (op (Over.mk (𝟙 S))))

/-- The scalar restriction R → Γ(S,Λ) is restriction along the unique map S → *.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def profiniteScalarMap (S : Profinite.{u}) : condensedScalarRing Λ →+*
    Evaluation.A ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ S) (Over.mk (𝟙 S)) :=
  ((condensedSectionRing Λ).obj.map (terminal.from S).op ≫
    (profiniteSectionRingIso Λ S).hom).hom

/-- Realization from R on the profinite slice uses restriction of the actual realization
on the point. All module operations are induced by the coefficient inverse image.
Source: HRS Definition 3.5 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def profiniteScalarRealization (S : Profinite.{u}) :
    DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤
      Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ S) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  letI := Functor.additive_of_preserves_binary_products e.inverse
  let f := ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).mapMod Λ
  letI := Functor.additive_of_preserves_binary_products f
  commutativeSiteDerivedConstantModuleFunctor (coherentTopology Profinite.{u})
      (condensedScalarRing Λ) ⋙
    (condensedScalarExtensionModel Λ).T ⋙ e.inverse.mapDerivedCategory ⋙ f.mapDerivedCategory

/-- The natural scalar associativity formula on a profinite slice, on all unbounded complexes.
Source: HRS Remark 3.2 (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def profiniteScalarClause (S : Profinite.{u}) : Prop :=
  Nonempty (profiniteScalarRealization Λ S ≅
    RingDerivedScalarExtension.moduleDerivedExtension (profiniteScalarMap Λ S) ⋙
      Evaluation.F ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ S)
        (Over.mk (𝟙 S)) Over.mkIdTerminal)

/-- The relative test functor characterized by the recorded component universal property.
Its value and all projections are unique up to their unique compatible isomorphism.
Source: HRS (4.1) (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def componentTests (T : Scheme.{u}) [IsAffine T] :
    Over (affineComponentSpace T) ⥤ T.ProEt :=
  Classical.choose (component_relative_profinite_site T)

/-- The actual inverse image: left Kan extension along the relative tests and sheafification.
Source: HRS (4.1) (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def componentInverse (T : Scheme.{u}) [IsAffine T]
    [(componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)] :
    Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback (componentTests T) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)

section ComponentPullback

variable (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

/-- Coefficient transport is restriction along the inverse of the specified ring isomorphism.
Source: HRS Proposition 4.3(3)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
abbrev componentModules
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) :
    Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      (profiniteCoefficient Λ (affineComponentSpace T)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) :=
  (componentInverse T).mapMod (profiniteCoefficient Λ (affineComponentSpace T)) ⋙
    Mod.comap α.inv.hom

/-- The component module pullback is additive, being exact on its underlying abelian sheaves.
Source: HRS (4.1) (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
instance componentModulesAdditive
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : (componentModules Λ T α).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The component inverse image on ordinary unbounded derived categories is induced termwise.
Source: HRS (4.1) (blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def componentDerived
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) :
    Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) ⥤
      Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ T) :=
  (componentModules Λ T α).mapDerivedCategory

/-- The symmetric monoidal assertion refers to the ordinary Koszul derived braidings.
Source: HRS Proposition 4.3(3)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def componentSymmetric
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : Prop :=
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      (profiniteCoefficient Λ (affineComponentSpace T)))
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
  Nonempty (componentDerived Λ T α).Braided

/-- The actual pullback induces the lisse equivalence and commutes with section-ring
realization after scalar transport along the coefficient comparison.
Source: HRS Proposition 4.3(3)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def componentComparisons
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : Prop :=
  (∃ (_ : (componentDerived Λ T α).CommShift ℤ),
    (componentDerived Λ T α).IsTriangulated) ∧
  componentSymmetric Λ T α ∧
  Nonempty ((componentDerived Λ T α).obj
      (𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T)))) ≅
    𝟙_ (Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ T))) ∧
  (∃ e : (Evaluation.lisse
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T))).FullSubcategory ≌
      (Evaluation.lisse (Scheme.ProEt.topology T) (condensedRingObj Λ T)).FullSubcategory,
    Nonempty (e.functor ⋙ (Evaluation.lisse (Scheme.ProEt.topology T)
        (condensedRingObj Λ T)).ι ≅
      (Evaluation.lisse ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))).ι ⋙ componentDerived Λ T α)) ∧
  ∃ a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T))) ≅
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T) (Scheme.ProEt.mk (𝟙 T)),
    Nonempty (Evaluation.F ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal ⋙ componentDerived Λ T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T)) (MorphismProperty.Over.mkIdTerminal
            @AlgebraicGeometry.WeaklyEtale T)) ∧
    Nonempty (profiniteScalarRealization Λ (affineComponentSpace T) ⋙ componentDerived Λ T α ≅
      condensedScalarRealization Λ T) ∧
    Nonempty (condensedScalarRealization Λ T ≅
      RingDerivedScalarExtension.moduleDerivedExtension
          (a.hom.hom.comp (profiniteScalarMap Λ (affineComponentSpace T))) ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T))

end ComponentPullback

/-- All structure asserted here is on the fixed relative-test inverse image, not on an
auxiliary functor. The coefficient isomorphism is an isomorphism of ring objects.
Source: HRS (4.1) and Proposition 4.3(3)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation). -/
def componentClause (T : Scheme.{u}) [IsAffine T] : Prop :=
  ∃ (_ : (componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)),
    ∃ (_ : (componentInverse T).Braided)
      (_ : PreservesFiniteLimits (componentInverse T))
      (_ : PreservesFiniteColimits (componentInverse T)),
      ∃ α : (componentInverse T).mapMon.obj
          (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
          Mon.mk (condensedRingObj Λ T),
        (∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
              (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T,
          NatTrans.IsMonoidal β.hom ∧ α.hom.hom = β.hom.app Λ) ∧
        componentComparisons Λ T α

end AlgebraicGeometry.ProEtale.CondensedRing
```

## New

The complete Lean block in `## Old` occurs unchanged in
`lean/Sheaf/AlgebraicGeometry/CondensedLisseEvaluationModel.lean`, with each
`(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation)` changed to
`(blueprint: def-zl-condensed-lisse-evaluation-model)` in documentation only.
All thirty declarations retain precisely the definitions printed above. The
original module publicly re-exports the block with:

```lean
public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
```

The original node retains its theorem attachment; the new definition node owns
the moved data declarations. The theorem's statement and the old node's
mathematical statement and statement dependencies are unchanged.

## Users

A fresh search of both `lean/` roots finds the following original importers.
The item and both consumers have now been restored to the current library.
No consumer refers directly to a moved data declaration outside the item. Both consumers below import this module privately for their proofs and
still obtain the identical theorem, names and public import closure.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels` | no local claim found; restored | Its private import resolves to the restored theorem module. No signature or definition changes. |
| `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity` | no local claim found; restored | Its private import resolves to the restored theorem module. No signature or definition changes. |
| `Sheaf.Paper.TAdmissibleDualizableTruncations` | not edited | Transitive consumer through the two restored importers; identical public data and theorem; no adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation` | S1 | Current theorem publicly re-exports the same definitions and imports their new owner. |
| `Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction` | new in this delivery | Uses the moved canonical functors in its signature. |
| `Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation` | new in this delivery | Uses the moved data and proves the equivalence from the adjunction. |
| `Sheaf.AlgebraicGeometry.CondensedComponentInverseImage` | new in this delivery | Proves continuity, exactness and braidedness for the fixed construction. |
| `Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility` | new in this delivery | States the coefficient and scalar comparison squares for the fixed component construction. |
| `Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility` | new in this delivery | States scalar associativity for the fixed profinite realization. |

No source-library module changes. No consumer adaptation is required. No target
meaning changes, so this extraction introduces no new mathematical target-review
obligation; the independent reader can verify the verbatim block comparison.

## Status

landed 20261021T061639-L-1805080 2026-10-21 (merge of deliver/S1/Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation)
