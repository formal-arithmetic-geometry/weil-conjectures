# completedCechModulesEquiv and the completed small-site transport

## Reason

Separate the existing, proved site construction from the theorem that uses it.
The coefficient-only and tensor-transport lemmas both need the actual site and
coefficient functors. Moving the definitions downward avoids an import cycle.
No existing name, signature, body, instance, or mathematical object changes.
The original module publicly re-exports the extracted construction. A new map
`completedCechCoefficientUnit` is constructed by the regular-module section 1.
No target definition or statement changes meaning.

## Old

The following block was in `Sheaf.Paper.WeilCompletedKoszulRoosComparison`:

```lean
/-- The pro-etale category with its morphisms lifted to the coefficient universe.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechSite := AsSmall.{0} X.ProEt

/-- The canonical equivalence with the category whose Hom universe has been lifted.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechSiteEquiv : X.ProEt ≌ completedCechSite X := AsSmall.equiv

/-- The topology induced along the inverse of the canonical site equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechTopology :=
  (completedCechSiteEquiv X).inverse.inducedTopology (ProEt.topology X)

/-- The actual completed ring sheaf pulled to the canonical small site.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
abbrev completedCechRing : Sheaf (completedCechTopology X) CommRingCat.{u + 1} :=
  ((completedCechSiteEquiv X).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
    (completedCechTopology X) (ProEt.topology X)).obj (pbcAdicCompletion X d)

/-- The module-sheaf equivalence induced by the canonical ringed-site equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechModulesEquiv :
    pbcModules X (pbcAdicCompletion X d) ≌ ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
      ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d)) := by
  let e := completedCechSiteEquiv X
  let J := ProEt.topology X
  let K := completedCechTopology X
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (pbcAdicCompletion X d)
  let R' : Sheaf K RingCat.{u + 1} :=
    (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R
  let φ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R' :=
    ⟨Functor.whiskerRight (NatTrans.op e.unitInv) R.obj⟩
  let ψ : R' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R := 𝟙 _
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) R'.obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.inverse.map (e.counit.app U.unop)).op =
      R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op
    rw [e.unitInv_app_inverse]
  have h₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) R.obj = 𝟙 R.obj := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.unitInv.app U.unop).op ≫
      (𝟙 _ ≫ R.obj.map (e.unit.app U.unop).op) = 𝟙 _
    rw [Category.id_comp, ← R.obj.map_comp, ← op_comp, e.unitIso.hom_inv_id_app]
    exact R.obj.map_id _
  exact (SheafOfModules.pushforwardPushforwardEquivalence.{u + 1} e φ ψ h₁ h₂).symm

/-- The standard derived category in the original ambient derived universe.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
instance : HasDerivedCategory.{u + 2} (ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
    ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (completedCechRing X d))) := HasDerivedCategory.standard _

/-- The exact module equivalence is additive because it preserves products and zero.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
instance : (completedCechModulesEquiv X d).functor.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- The equivalence induced on unbounded derived categories by the module equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechDerivedEquiv : PbcCompletedDerived X d ≌
    ringedSiteDerived.{u + 1, u + 2} (completedCechRing X d) :=
  (completedCechModulesEquiv X d).mapDerivedCategory

/-- The compatible-residue scalar map, followed by the fixed coefficient comparison.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechScalarMap :
    (Functor.const (completedCechSite X)ᵒᵖ).obj (CommRingCat.of A) ⟶
      (completedCechRing X d).obj :=
  Functor.whiskerLeft (completedCechSiteEquiv X).inverse.op
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (adicDatumScalar X (intrinsicPresentationDatum d)).hom ≫
        (pbcCompletedComparison X d).hom.hom)

/-- The actual compatible-residue scalar as a global section on the canonical small site.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedCechScalar (a : A) :
    ((completedCechRing X d).obj ⋙ CategoryTheory.forget CommRingCat.{u + 1}).sections := by
  refine ⟨fun U ↦ (completedCechScalarMap X d).app U a, ?_⟩
  intro U V f
  exact congrArg (fun g ↦ g a) ((completedCechScalarMap X d).naturality f).symm


/-- The strict-tower derived category in the same ambient universe.
Source: Stacks, Tag 0941
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
instance : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤
    ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
      ((sheafCompose (completedCechTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d))) := HasDerivedCategory.standard _
```

## New

The same block is in `Sheaf.Paper.WeilCompletedKoszulSite`, with its blueprint
annotations attached to `def-weil-pbc-completed-cech-site-transport`.
`Sheaf.Paper.WeilCompletedKoszulRoosComparison` publicly imports that module.
All original public imports remain in the original module. Its consumers see
the same declaration names and bodies. The new coefficient-unit map is:

```lean
def completedCechCoefficientUnit :
    SheafOfModules.unit ((sheafCompose (completedCechTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (completedCechRing X d)) ⟶
    (intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor).obj
      (SheafOfModules.unit ((adicLisseForget X).obj
        (adicDatumRing X (intrinsicPresentationDatum d)))) := by
  refine (SheafOfModules.unitHomEquiv _).symm ?_
  refine ⟨fun U ↦ (1 : (adicDatumRing X (intrinsicPresentationDatum d)).obj.obj
    ((completedCechSiteEquiv X).inverse.op.obj U)), ?_⟩
  intro U V f
  exact (adicDatumRing X (intrinsicPresentationDatum d)).obj.map
    ((completedCechSiteEquiv X).inverse.op.map f) |>.hom.map_one


```

## Users

The direct importers are CompletedConstantCoefficientEquivalence,
CompletedConstantPresentationTransport, CompletedKoszulConstantTransport and
WeilCompletedKoszulProductComparison. No consumer changes are necessary.
The table includes every textual user of a moved declaration in either library
root, including transitive users detected by `tools/downstream.py --uses`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.CompletedConstantCoefficientEquivalence | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.CompletedKoszulQuotientComparison | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.PbcCompletedPullbackActual | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.QuotientCompletedCompositorUnit | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedCechComparison | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedKoszulLimitComparison | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedKoszulProductComparison | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedKoszulRepresentativeComparison | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedKoszulRoosComparison | B8 | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedTensorReflector | unclaimed | Same publicly re-exported names and bodies; no adaptation. |
| Sheaf.Paper.WeilCompletedKoszulSite | new in B8 packet | Defines the moved declarations and the actual section-1 unit. |
| Sheaf.Paper.WeilCompletedKoszulCoefficientComparison | new in B8 packet | Uses the extracted site and unit. |
| Sheaf.Paper.WeilCompletedTensorTransport | new in B8 packet | Uses the extracted site and unit. |

## Status

landed 20261025T162026-L-211085 2026-10-25 (merge of deliver/B8/Sheaf.Paper.WeilCompletedKoszulRoosComparison)
