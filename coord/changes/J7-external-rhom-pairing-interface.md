# AlgebraicGeometry.Etale.ExternalRHom: shared evaluation interface

## Reason

The cochain-model, restriction and signed-cone obligations must import the
construction that their statements use. Keeping those definitions beside the
assembly theorem would create an import cycle. Move the existing interface to
`Sheaf.Paper.ExternalRHomConePairingDefs` and publicly re-export it from the
original module. All existing fully qualified names remain available there.
The statement of `external_rhom_cone_pairing` is verbatim unchanged. The three
generic evaluation factories move to `ExternalRHomEvaluationNaturality`, publicly
re-exported by the interface, with their fully qualified names, signatures and
bodies preserved. `constantPullbackIso` names the original comparison composite.

The original and intermediate interface variants exceeded the single-file
compiler limit. Profiling isolated expensive definitional comparisons involving
total tensors and the scalar-realization additivity proof. The interface now
shares the native structure arguments, gives the external-model arrow its
explicit type, restores transparency checks, and checks the left-derived counit at abstract
categories before specialization. The Hom cochain construction is retained
verbatim at its original concrete category, preserving the reduction behavior
needed by V6's subsequently landed chain-evaluation proofs. The tensor-inclusion and complex-tensor helpers use preadditivity and a zero
object directly, avoiding conversion through the larger abelian structure.
The original scalar-realization additivity proof is retained. No mathematical datum is chosen from an unfinished existence theorem.

`globalHom` is now a definition with the same body, instead of an abbreviation.
The chain evaluation composites are applications of the same generic evaluation
maps at complex categories. `externalPulledEvaluationOf` composes both pulled
evaluations and their external tensor before specialization, so the concrete
chain pairing does not repeatedly check the same total-complex tensor data.
It retains the original `Functor.Monoidal.μIso.hom` maps and the same cached
monoidal instances, including their specified tensor constraints. The inlined constant-pullback comparison is exactly
the body of `derivedConstantPullbackIso`, retaining its canonical orientation.
The total tensor, differential, Koszul interchange and all comparison maps are
unchanged. `HasKoszulBraiding` now invokes `NativeBraidingAt` at the coefficient
category. That predicate is exactly the native localization tensor/braiding
equation, written once with its coefficient category abstract; its complete
proof is `external_rhom_derived_braiding`. Its ordinary and derived braidings,
tensor constraints and localization functor are the same canonical ones that
were previously expanded at the concrete sheaf category inside `IsBraidedAt`.
The two K-flat premises and their quantifiers are unchanged. Naming the equation
avoids expanding chosen colimit data throughout its concrete morphism formula.
No theorem or existence witness is used to define this proposition.

Likewise `IsNatural` retains every original quantified object, bounded-flat-model
premise, bounded-below premise and morphism. Its equation is named as
`GenericExternal.NaturalityAt` at the three native derived sheaf categories.
This predicate uses exactly the same composite constant/sections and tensor/Hom
adjunctions, evaluations, canonical inverse-image tensor constraints, constant
pullback comparisons and derived constant tensor comparison. The generic
`pairing_eq_pairingOf` theorem, proved by reflexivity, checks the generic pairing
against the same factory used by the original `pairing`. GenericTranspose.tr and
ev are the original composite Hom equivalence and counit formulas; global Hom's
contravariant map is `sections.map (MonoidalClosed.pre f)` and its covariant map
is `sections.map ((ihom E).map k)`, as in the original homMap. This is the same
four-variance square, with its coefficient categories abstract while the equation
is checked. It is not an assumption of functoriality. The generic theorem proves
it by adjunction naturality, evaluation naturality, tensor naturality and the
Koszul interchange. Specialization supplies the native naturality proof.
`transpose`, `evaluation`, `globalAdjunction`, `homMap` and `pairing` retain their
original bodies. This is an interface and elaboration repair, not a weakened statement.
It changes definitions used by the target closure, so their meanings are open
for the independent statement review.

The broad public coefficient and Künneth imports are removed; the precise
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` import supplies
the flatness instance needed by the canonical pullback tensor constraint.

Unchanged definitions move verbatim, apart from docstrings pointing to the new
interface node. The following are the changed existing declarations.

## Old

```lean
noncomputable instance complexesMonoidal (X : Scheme.{u}) : MonoidalCategory (Complexes A X) :=
  inferInstance
```

```lean
noncomputable abbrev globalHom (X : Scheme.{u}) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule A X ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  internalHom A X ⋙ (Functor.whiskeringRight _ _ _).obj (sections A X)
```

```lean
noncomputable def homComplex {X : Scheme.{u}} (E I : Complexes A X) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ where
  X n := ModuleCat.of A (CochainComplex.HomComplex.Cochain E I n)
  d n m := ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom A E I n m)
  shape n m h := ModuleCat.hom_ext (LinearMap.ext
    (fun z ↦ CochainComplex.HomComplex.δ_shape n m h z))
  d_comp_d' n m k _ _ := ModuleCat.hom_ext (LinearMap.ext
    (fun z ↦ CochainComplex.HomComplex.δ_δ n m k z))
```

```lean
noncomputable def tensorInclusionOf
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K L' : CochainComplex C ℤ) (r q n : ℤ) (h : r + q = n) :
    K.X r ⊗ L'.X q ⟶ (K ⊗ L').X n :=
  HomologicalComplex.ιTensorObj K L' r q n h
```

```lean
noncomputable def tensorComplexSection {X : Scheme.{u}} (K L' : Complexes A X)
    (r q n : ℤ) (h : r + q = n) (W : X.Etaleᵒᵖ)
    (x : (K.X r).obj.obj W) (y : (L'.X q).obj.obj W) :=
  ((tensorInclusionOf K L' r q n h).hom.app W)
    (tensorSection A (K.X r) (L'.X q) W x y)
```

```lean
noncomputable def constantModel (X : Scheme.{u})
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (constant A X).obj
      ((moduleQ A).obj U) ⟶ (siteQ A X).obj ((constantComplex A X).obj U) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ _).obj U)
```

```lean
noncomputable def pullModel {X P : Scheme.{u}} (a : P ⟶ X) (E : Complexes A X) :
    (pull A a).obj ((siteQ A X).obj E) ⟶
      (siteQ A P).obj
        (((upperStar (ModuleCat.{u + 1} A) a).mapHomologicalComplex (.up ℤ)).obj E) :=
  (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ _).obj E)
```

```lean
noncomputable def pulledEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (E K : DerivedCategoryModule A X) :
    (constant A P).obj
      (((globalHom A X).obj (op E)).obj K) ⊗
        (pull A a).obj E ⟶
      (pull A a).obj K :=
  pullEvaluationOf (pull A a) (constant A X) (constant A P)
    (derivedConstantPullbackIso (ModuleCat.{u + 1} A) a)
    (fun E' H' ↦ (pullTensorIso A a E' H').hom) E K
    (((globalHom A X).obj (op E)).obj K) (evaluation A E K)
```

```lean
noncomputable def externalModel {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) :=
  tensorModelOf (siteQ A P) ((pullComplex A a).obj E) ((pullComplex A b).obj H)
    ((pull A a).obj ((siteQ A X).obj E)) ((pull A b).obj ((siteQ A Y).obj H))
    (pullModel A a E) (pullModel A b H)
```

```lean
noncomputable def pulledChainEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (E N : Complexes A X)
    (u : chainEvaluationSource A X U E ⟶ N) :
    chainEvaluationSource A P U ((pullComplex A a).obj E) ⟶ (pullComplex A a).obj N :=
  pullComplexEvaluationOf (upperStar (ModuleCat.{u + 1} A) a)
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).symm E N U u
```

```lean
noncomputable def chainPairEvaluation {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (U V : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (E N : Complexes A X) (H M : Complexes A Y) (J : Complexes A P)
    (u : chainEvaluationSource A X U E ⟶ N)
    (v : chainEvaluationSource A Y V H ⟶ M)
    (i : externalComplex A a b N M ⟶ J) :
    chainEvaluationSource A P (U ⊗ V) (externalComplex A a b E H) ⟶ J :=
  externalComplexEvaluationOf (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
    U V ((pullComplex A a).obj E) ((pullComplex A b).obj H)
    ((pullComplex A a).obj N) ((pullComplex A b).obj M) J
    (pulledChainEvaluation A a U E N u) (pulledChainEvaluation A b V H M v) i
```

```lean
def HasKoszulBraiding : Prop :=
  ∀ (X : Scheme.{u}) (E H : Complexes A X),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj E) →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj H) →
    IsBraidedAt (siteQ A X) E H
```

```lean
def IsNatural : Prop :=
  ∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (E E' K K' : DerivedCategoryModule A X) (H H' L' L'' : DerivedCategoryModule A Y),
    HasBoundedFlatModel A E → HasBoundedFlatModel A E' →
    HasBoundedFlatModel A H → HasBoundedFlatModel A H' →
    IsPlus A K → IsPlus A K' → IsPlus A L' → IsPlus A L'' →
    IsPlus A (external A a b K L') → IsPlus A (external A a b K' L'') →
    ∀ (f : E' ⟶ E) (g : H' ⟶ H) (k : K ⟶ K') (l : L' ⟶ L''),
      (homMap A f k ⊗ₘ homMap A g l) ≫ pairing A a b E' K' H' L'' =
        pairing A a b E K H L' ≫
          homMap A ((pull A a).map f ⊗ₘ (pull A b).map g)
            ((pull A a).map k ⊗ₘ (pull A b).map l)
```

## New

```lean
noncomputable instance complexesMonoidal (X : Scheme.{u}) : MonoidalCategory (Complexes A X) :=
  complexesMonoidalOf (Modules A X)
```

```lean
noncomputable def globalHom (X : Scheme.{u}) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule A X ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  internalHom A X ⋙ (Functor.whiskeringRight _ _ _).obj (sections A X)
```

`homComplex` retains the original concrete `where` construction shown in
Old, verbatim. An earlier packet wrapped `homComplexOf A E I` here; that
additional definition boundary made V6's newly landed evaluation proofs exceed
60 seconds. Restoring the original body lets those proofs compile unchanged
against the extracted interface (56.0 seconds for the complete module).


```lean
noncomputable def tensorInclusionOf
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K L' : CochainComplex C ℤ) (r q n : ℤ) (h : r + q = n) :
    K.X r ⊗ L'.X q ⟶ (K ⊗ L').X n :=
  HomologicalComplex.ιTensorObj K L' r q n h
```

```lean
noncomputable def tensorComplexSection {X : Scheme.{u}} (K L' : Complexes A X)
    (r q n : ℤ) (h : r + q = n) (W : X.Etaleᵒᵖ)
    (x : (K.X r).obj.obj W) (y : (L'.X q).obj.obj W) :
    ((K ⊗ L').X n).obj.obj W :=
  ((tensorInclusionOf K L' r q n h).hom.app W)
    (tensorSection A (K.X r) (L'.X q) W x y)
```

```lean
noncomputable def constantModel (X : Scheme.{u})
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (constant A X).obj
      ((moduleQ A).obj U) ⟶ (siteQ A X).obj ((constantComplex A X).obj U) :=
  leftDerivedModelOf (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) U
```

```lean
noncomputable def pullModel {X P : Scheme.{u}} (a : P ⟶ X) (E : Complexes A X) :
    (pull A a).obj ((siteQ A X).obj E) ⟶
      (siteQ A P).obj
        (((upperStar (ModuleCat.{u + 1} A) a).mapHomologicalComplex (.up ℤ)).obj E) :=
  leftDerivedModelOf (upperStar (ModuleCat.{u + 1} A) a) E
```

```lean
noncomputable def pulledEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (E K : DerivedCategoryModule A X) :
    (constant A P).obj
      (((globalHom A X).obj (op E)).obj K) ⊗
        (pull A a).obj E ⟶
      (pull A a).obj K :=
  pullEvaluationOf (pull A a) (constant A X) (constant A P)
    (constantPullbackIso A a)
    (fun E' H' ↦ (pullTensorIso A a E' H').hom) E K
    (((globalHom A X).obj (op E)).obj K) (evaluation A E K)
```

```lean
noncomputable def externalModel {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) :
    (pull A a).obj ((siteQ A X).obj E) ⊗ (pull A b).obj ((siteQ A Y).obj H) ⟶
      (siteQ A P).obj (externalComplex A a b E H) :=
  tensorModelOf (siteQ A P) ((pullComplex A a).obj E) ((pullComplex A b).obj H)
    ((pull A a).obj ((siteQ A X).obj E)) ((pull A b).obj ((siteQ A Y).obj H))
    (pullModel A a E) (pullModel A b H)
```

```lean
noncomputable def pulledChainEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (E N : Complexes A X)
    (u : chainEvaluationSource A X U E ⟶ N) :
    chainEvaluationSource A P U ((pullComplex A a).obj E) ⟶ (pullComplex A a).obj N :=
  pullEvaluationOf (pullComplex A a) (constantComplex A X) (constantComplex A P)
    (Functor.mapHomologicalComplexCompIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a) (.up ℤ)).symm
    (fun E' H' ↦ (Functor.Monoidal.μIso (pullComplex A a) E' H').hom) E N U u
```

```lean
noncomputable def chainPairEvaluation {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (U V : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (E N : Complexes A X) (H M : Complexes A Y) (J : Complexes A P)
    (u : chainEvaluationSource A X U E ⟶ N)
    (v : chainEvaluationSource A Y V H ⟶ M)
    (i : externalComplex A a b N M ⟶ J) :
    chainEvaluationSource A P (U ⊗ V) (externalComplex A a b E H) ⟶ J :=
  externalPulledEvaluationOf (pullComplex A a) (pullComplex A b)
    (constantComplex A X) (constantComplex A Y) (constantComplex A P)
    (Functor.mapHomologicalComplexCompIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a) (.up ℤ)).symm
    (Functor.mapHomologicalComplexCompIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) b) (.up ℤ)).symm
    (fun E' H' ↦ (Functor.Monoidal.μIso (pullComplex A a) E' H').hom)
    (fun E' H' ↦ (Functor.Monoidal.μIso (pullComplex A b) E' H').hom)
    (Functor.OplaxMonoidal.δNatTrans (constantComplex A P))
    U V E N H M J u v i
```

```lean
def HasKoszulBraiding : Prop :=
  ∀ (X : Scheme.{u}) (E H : Complexes A X),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj E) →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj H) →
    NativeBraidingAt (Modules A X) E H
```

```lean
def IsNatural : Prop :=
  ∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (E E' K K' : DerivedCategoryModule A X) (H H' L' L'' : DerivedCategoryModule A Y),
    HasBoundedFlatModel A E → HasBoundedFlatModel A E' →
    HasBoundedFlatModel A H → HasBoundedFlatModel A H' →
    IsPlus A K → IsPlus A K' → IsPlus A L' → IsPlus A L'' →
    IsPlus A (external A a b K L') → IsPlus A (external A a b K' L'') →
    ∀ (f : E' ⟶ E) (g : H' ⟶ H) (k : K ⟶ K') (l : L' ⟶ L''),
      letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) a
      letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) b
      GenericExternal.NaturalityAt
        (constantSectionsAdjunction A X) (constantSectionsAdjunction A Y)
        (constantSectionsAdjunction A P) (pull A a) (pull A b)
        (constantPullbackIso A a) (constantPullbackIso A b)
        (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedTensorComparison
        f g k l
```

Additional public helpers in the interface are `complexesMonoidalOf`,
`leftDerivedModelOf`, `homComplexOf`, `coefficientComplexMonoidal`,
`complexesBraiding`, `siteDerivedMonoidal`, `siteDerivedClosed`,
`siteLocalizationMonoidal`, `constantComplexOplax` and `pullComplexMonoidal`; `constantPullbackIso` names the existing comparison.
They construct or name native data, with no holes. The module uses these caches
locally; the original public `modulesMonoidal` and `complexesMonoidal` instances
remain available. Their complete definitions are in the delivered interface
and attached to `def-pur-external-rhom-pairing-interface`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExternalRHomConePairing | J7 | Re-exports the interface and proves the unchanged assembly theorem from the current human split. |
| Sheaf.Paper.ExternalEvaluationTransposeNatural | unclaimed | Direct importer. Replaces the item import with its definitions module, preserving the complete unrestricted theorem signature. Adds the proved bounded-domain generic naturality specialization at this existing node. |
| Sheaf.Paper.GlobalHomEvaluationFlatLift | V5 at returned head; claim since released | Direct importer. Replaces line 8 with the definitions import to break the source cycle. In the current V5 proof, line 212 unfolds leftDerivedModelOf alongside pullModel so the existing counit IsIso instance applies; every signature and all remaining proof lines are retained. |
| Sheaf.Paper.LiftedExternalEvaluationChainModel | V6 at returned head; claim since released | Direct importer. Only line 18 changes: replaces the item import with its definitions module to break the source cycle. All six existing theorem signatures and bodies remain. |
| Sheaf.Paper.CoefficientPointFlatKFlatComparison | unclaimed (landed by V5) | New direct consumer. Only line 8 changes to the shared definitions import; preserves every signature and proof and breaks its source cycle through GlobalHomEvaluationFlatLift. |
| Sheaf.Paper.EtaleScalarFlatKFlatComparison | unclaimed (landed by V5) | New direct consumer. Only line 8 changes to the shared definitions import; preserves every signature and proof and breaks its source cycle through GlobalHomEvaluationFlatLift. |
| Sheaf.Paper.GlobalHomChainEvaluation | unclaimed (landed by V5) | New direct consumer. Only line 8 changes to the shared definitions import; preserves every signature and proof and breaks its source cycle through GlobalHomEvaluationFlatLift. |
| Sheaf.Paper.GlobalHomEvaluationModel | unclaimed (landed by V5) | New direct consumer. Only line 8 changes to the shared definitions import; preserves every signature and proof and breaks its source cycle through GlobalHomEvaluationFlatLift. |
| Sheaf.Paper.ExternalRHomConePairingDefs | new, J7 | Retains the concrete interface and publicly re-exports the generic factories. |
| Sheaf.Paper.ExternalRHomAdjunctionNaturality | new, J7 | Proves composite-adjunction and evaluation naturality. |
| Sheaf.Paper.ExternalRHomEvaluationNaturality | new, J7 | Retains the original generic factories and proves their four-variable equation. |
| Sheaf.Paper.ExternalRHomDerivedBraiding | new, J7 | Proves the canonical localization braiding equation. |
| Sheaf.Paper.ExternalRHomSignedCones | new, J7 | States only native coefficient-cone transport for a given normalized S; imports the existing four source results. |

The current direct-import search gives the seven existing consumers above,
including V5's four newly landed supporting modules. SupportedProductLocalization and KunnethSupported are
not importers of the current item and are removed from this list. Textual uses
of globalHom occur in the item, ExternalEvaluationTransposeNatural and
GlobalHomEvaluationFlatLift. The other changed interface declarations occur only
in the item and these three consumers. The consumers' statements retain their
original objects, normalization formulas and canonical comparisons. The whole
packet is compiled together in dependency order; no source-library file changes.

The import changes break a real source cycle: the item now imports the existing
three source lemmas, whose statements use only the shared definitions.
ExternalEvaluationTransposeNatural is unclaimed. GlobalHomEvaluationFlatLift
was held by V5 and LiftedExternalEvaluationChainModel was held by V6 at the
returned head; both have since landed their proofs and released their claims.
Their complete current proofs are preserved. These are
forced adaptations. V6 retains only the public import substitution. V5 also
needs its existing pullback comparison proof to unfold the extracted
leftDerivedModelOf helper alongside pullModel (line 212); without it, line 213
fails to synthesize IsIso (leftDerivedModelOf (f)^*[ModuleCat A] T). This is the
same canonical counit and uses the same existing instance. Its other proof
lines are verbatim retained. Restoring
either original closes a source import cycle through ExternalRHomSignedCones;
restoring LiftedExternalEvaluationChainModel also closes its direct cycle with
the assembly module. The exact lcompile.py source-cycle diagnostics, changed
line numbers and necessity are recorded in report.md, under Forced adaptations.
Their previous option/local-instance edits and the extra private import have
been removed because they were not necessary. Apart from that single V5 unfolding step, all other lines in these two
consumers and the four new supporting consumers are verbatim identical to the
current source. The current GlobalHomEvaluationFlatLift proof imports these
four modules, so each old assembly import closes an additional source cycle.
They need only the shared interface and receive the same import substitution. Local canonical
instances remain enabled only in the unclaimed transpose consumer.

## Repair of C-72ecd

The returned cochain-model and restriction modules/nodes were never landed.
They are omitted from the repaired packet, rather than withdrawn from the library.
The returned native-naturality node is likewise omitted: its complete generic
specialization now belongs to lem-pur-external-evaluation-transpose-natural.
The existing unrestricted theorem is retained verbatim, including all five
conjuncts, and the item uses its fourth and fifth conjuncts directly.

The cone obligation is narrowed from an existential shift-and-cones result to
`external_rhom_coefficient_cones A S hs`. Its S is the existing
`lifted_external_evaluation_derived_hom_shift` witness. It neither reconstructs
that witness nor restates either existing chain shift square. The remaining
assertion concerns distinguished triangles in the native ordinary-etale
encoding with this fixed S; the chain-square theorem concerns ordinary complexes
in the constant-ring module-sheaf encoding. The transport and native exactness
are a separate result, with the complete argument recorded in its node/docstring.

## Status

landed 20261021T214812-L-1858322 2026-10-21 (merge of deliver/J7/Sheaf.Paper.ExternalRHomConePairing)

Repair retry, 2026-10-22: current-source comparison verifies the two forced
adaptations above (V5: lines 8 and 212; V6: line 18). The default compiler route
failed because its local mirror lacks Mathlib.olean. A subsequent dependency-order
compile with lcompile.py's documented LCOMPILE_NO_LOCAL=1 option succeeded for
all thirteen modules against the project server's published build. In particular
the adapted V5 module took 16.7 s, the cone lemma 6.3 s and the assembly 15.7 s.
No source change or launcher edit was needed for this compiler-route correction.
Two subsequent required deliver3.py submissions terminated with exit code 143
(SIGTERM) and no diagnostic or DELIVERED result. This record remains open and
the verified packet is retained for submission when that tool failure is resolved.

Current repair verification, 2026-10-22: rechecked every delivered source against
the current shared source. The V5 adaptation is still exactly lines 8 and 212;
the V6 adaptation is still exactly line 18. Their original holders V5 and V6,
source-cycle failures and the V5 counit instance error remain recorded above
and in the report's Forced adaptations section. All thirteen packet modules
passed a fresh dependency-order server compile with no diagnostics. The record
stays open pending delivery and the maintainer's independent/global checks.
