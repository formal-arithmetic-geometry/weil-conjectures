# Integral comparison private proof compilation

## Reason

The unchanged direct consumer exceeded the 60-second limit (63 seconds), and
profiling against the original library and the delivered modules also exceeded
it (71 and 77 seconds). Independent generic scalar, K-flat and normalized descent
arguments are expensive to elaborate together with concrete quotient systems.
Extract their complete proofs and retain the original private theorem signatures.
The fixed-model scalar adjunction normalization is proved generically, avoiding
the expensive rewrite of a concrete model equality. The resolution witness uses
explicit flatness and good-representative proofs. No public declaration signature,
public definition body, instance, attribute or public import changes.

## Old

The original complete private scalar and derived proofs lived in this consumer.
Its generic unary-whiskering construction used projection extension and diagonal
restriction. The fixed-model adjunction proof transported a scalar package by a
model equality in the concrete sequence context. Its resolving witness used
`refine ⟨K, r, ⟨hK, ?_⟩, hr⟩`. Scalar composition and identity used
`simpa only [sequenceTensorSection_eq] using h`.

Original retained private signatures, verbatim:

```lean
private theorem scalarPackageExists
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃ A : SheafOfModules.SystemScalarModel φ, A.model = D

private theorem scalarCompositionUnique
    {R S T : Sheaf J CommRingCat.{sw}} {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (A : SheafOfModules.SystemScalarModel φ) (B : SheafOfModules.SystemScalarModel ψ)
    (D : SheafOfModules.SystemScalarModel γ) :
    ∃! a : A.model.E ⋙ B.model.E ≅ D.model.E,
      ∀ P U (c : T.obj.obj U) (b : S.obj.obj U) (x : P.val.obj U),
        (a.hom.app P).val.app U
          (SheafOfModules.systemModelTmul B.model (A.model.E.obj P) U c
            (SheafOfModules.systemModelTmul A.model P U b x)) =
          SheafOfModules.systemModelTmul D.model P U (c * (ψ.hom.app U) b) x

private theorem scalarUnitUnique
    {R : Sheaf J CommRingCat.{sw}} {φ : R ⟶ R} (hφ : φ = 𝟙 R)
    (A : SheafOfModules.SystemScalarModel φ) :
    ∃! a : A.model.E ≅ 𝟭 _, ∀ P U (s : R.obj.obj U) (x : P.val.obj U),
      (a.hom.app P).val.app U (SheafOfModules.systemModelTmul A.model P U s x) =
        s • x

private theorem modelTmul_eq
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (N : SheafOfModules.{sw} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (eqToHom (D.obj_eq N).symm).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      SheafOfModules.systemModelTmul D N U s x

private theorem kflatWhiskering
    {D : Type e} [Category.{f} D]
    {C : Type a} [Category.{b} C] [EssentiallySmall.{c} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{c} RingCat.{c})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{c}]
    [HasSheafify J AddCommGrpCat.{c}]
    (R : Sheaf J CommRingCat.{c})
    [HasDerivedCategory.{d} (SheafOfModules.{c}
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj R))] :
    let A := SheafOfModules.{c}
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj R)
    let P : ObjectProperty (CochainComplex A ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (R := R)
    Nonempty (((whiskeringLeft P.FullSubcategory (DerivedCategory A) D).obj
      (P.ι ⋙ DerivedCategory.Q)).FullyFaithful)

private theorem derivedComparison
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {C : Type e} [Category.{f} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type g} [Category.{h} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (p : A ⥤ B) [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (q : C ⥤ D) [q.Additive] [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (s : A ⥤ C) [s.Additive] (t : B ⥤ D) [t.Additive]
    (LS : DerivedCategory A ⥤ DerivedCategory C)
    (LT : DerivedCategory B ⥤ DerivedCategory D)
    (εS : DerivedCategory.Q ⋙ LS ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εT : DerivedCategory.Q ⋙ LT ⟶ t.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : p ⋙ t ≅ s ⋙ q) (R good : ObjectProperty (CochainComplex A ℤ))
    (ff : ((whiskeringLeft R.FullSubcategory (DerivedCategory A) (DerivedCategory D)).obj
      (R.ι ⋙ DerivedCategory.Q)).FullyFaithful)
    (hgood : ∀ X, good X → R X)
    (hres : ∀ X, R X → ∃ (Y : CochainComplex A ℤ) (r : Y ⟶ X), good Y ∧ QuasiIso r)
    (hS : ∀ X, R X → IsIso (εS.app X))
    (hT : ∀ X, good X → IsIso (εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X))) :
    ∃! a : p.mapDerivedCategory ⋙ LT ≅ LS ⋙ q.mapDerivedCategory,
      ∀ X, R X →
        LT.map (p.mapDerivedCategoryFactors.hom.app X) ≫
          εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app X) =
        a.hom.app (DerivedCategory.Q.obj X) ≫ q.mapDerivedCategory.map (εS.app X) ≫
          q.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj X)

private theorem sequenceScalarAdjunction (X : Scheme.{t}) :
    ∃ adj : (integralComparisonSequenceScalarModel l E L ι X).E ⊣
      SheafOfModules.restrictScalars ((sheafCompose
        (coefficientSequenceTopology (ProEt.topology X)) (forget₂ CommRingCat RingCat)).map
          (integralComparisonSequenceScalarMap l E L ι X)),
      ∀ (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
        (x : N.val.obj U),
        (adj.unit.app N).val.app U x =
          (eqToHom ((integralComparisonSequenceScalarModel l E L ι X).obj_eq N).symm).val.app U
            ((toSheafify (coefficientSequenceTopology (ProEt.topology X))
              (SheafOfModules.changeOfRingsPresheaf
                (integralComparisonSequenceScalarMap l E L ι X) N).presheaf).app U
                  ((1 : (coefficientSequenceCommRingSheaf l L X).obj.obj U)
                    ⊗ₜ[(coefficientSequenceCommRingSheaf l E X).obj.obj U,
                      ((integralComparisonSequenceScalarMap l E L ι X).hom.app U).hom] x))

```

Additional retained private signatures, verbatim:

```lean
private theorem sequenceConstantMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
      coefficientProEtaleDirectRingMap.{t, u} f B =
    coefficientProEtaleDirectRingMap.{t, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a)

private theorem sequenceDirectComp_apply {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) (M : coefficientSequenceModules l E Z)
    (U : (ℕ × V.ProEt)ᵒᵖ)
    (x : ((integralComparisonSequenceDirectImage l E h ⋙
      integralComparisonSequenceDirectImage l E k).obj M).val.obj U) :
    ((sequenceDirectComp l E h k).hom.app M).val.app U x =
      M.val.map (Prod.mkHom (𝟙 U.unop.1)
        ((MorphismProperty.Over.pullbackComp h k).hom.app U.unop.2)).op x

private theorem sequenceDirectId_apply (Y : Scheme.{t})
    (M : coefficientSequenceModules l E Y) (U : Y.ProEt) (n : ℕ)
    (x : M.val.obj (op (n, U))) :
    ((sequenceDirectId l E Y).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)).op x
```

The old proof import was:

```lean
import Sheaf.Paper.AmbientPullbackTensorCoherence
```

## New

The original four scalar proofs move verbatim to `SequenceScalarConstruction`
in `SystemScalarPackageExists`, `SystemScalarCompositionUnique`,
`SystemScalarUnitUnique`, and `SystemScalarTensorSection`. Their original private
signatures remain as wrappers. The K-flat restriction proof moves to
`SequenceComparisonConstruction.kflatWhiskering` in `KFlatUnaryWhiskering`.
Its unary step uses the complete explicit projection/diagonal inverse in
`CategoryTheory.Functor.unaryWhiskeringOfProduct`. The generic normalized derived
comparison and its complete private helpers move to
`NormalizedDerivedComparisonDescent`; the consumer keeps its original private
signature as a wrapper. No arbitrary witness is introduced. `FixedScalarCompositionUnique` and
`FixedScalarUnitUnique` transport the package comparison to fixed abstract models.
The consumer applies them directly after normalizing its tensor-section target,
so the three concrete model equality rewrites no longer occur there.

`sequenceScalarAdjunction` applies the complete generic
`SequenceScalarConstruction.scalarOrdinaryAdjunction`, which transports the
normalized adjunction before specializing the cochain model. The same equality
and unit normalization are used; concrete quotient systems are not unfolded.
The resolving witness is assembled with typed `hflat` and `hgood`, followed by
`exact ⟨K, r, hgood, hr⟩`. Scalar comparison normalization simplifies the target
and then applies `h`, instead of invoking `simpa` across the large goal.

The new ambient proof import is:

```lean
import Sheaf.Paper.AmbientPullbackTensorData
```

Only actual site and normalized tensor constructions are used; the final
coherence theorem is unused. Removed direct proof imports now live in the
extracted proof modules: SystemScalarCoherence, SystemScalarGenerators,
CochainHomotopyComparison, CochainAdjunctionCompatibility,
SheafRingDerivedHomComparison, SheafRingCoefficientOrdinaryAdjunction, and
ResolvingRepresentativeWhiskering. The private constant-map naturality proof now applies the identical theorem
already proved in AmbientPullbackSiteData, through a proof-only `import all`.
The inverse composition and identity section calculations move to
AmbientPushforwardCompositionSections and AmbientPushforwardIdentitySections,
where they apply on either ambient site. Their old private signatures are retained
as direct applications at none. This avoids concrete quotient-system type changes.
The consumer node records the generic
arguments and the exact ambient site/tensor construction dependencies. Its
statement and Lean attachments are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Public API and data bodies unchanged; private proofs extracted (private normalizedComparisonDescent kept verbatim). |
| Sheaf.Paper.FiniteQuotientPullbackDescent | importer (`import all`) | Uses private normalizedComparisonDescent; compiles unchanged. |
| Sheaf.CategoryTheory.UnaryWhiskeringOfProduct | G2, new | Complete projection/diagonal inverse. |
| Sheaf.CategoryTheory.KFlatUnaryWhiskering | G2, new | Complete K-flat restriction proof. |
| Sheaf.CategoryTheory.NormalizedDerivedComparisonDescent | G2, new | Complete generic descent argument. |
| Sheaf.CategoryTheory.SystemScalarPackageExists | G2, new | Original complete scalar package construction. |
| Sheaf.CategoryTheory.SystemScalarCompositionUnique | G2, new | Original complete normalized composition proof. |
| Sheaf.CategoryTheory.SystemScalarUnitUnique | G2, new | Original complete scalar identity proof. |
| Sheaf.CategoryTheory.SystemScalarTensorSection | G2, new | Original complete tensor section calculation. |
| Sheaf.CategoryTheory.FixedScalarCompositionUnique | G2, new | Complete fixed-model composition comparison. |
| Sheaf.CategoryTheory.FixedScalarUnitUnique | G2, new | Complete fixed-model identity comparison. |
| Sheaf.Paper.AmbientPushforwardCompositionSections | G2, new | Complete inverse composition section formula. |
| Sheaf.Paper.AmbientPushforwardIdentitySections | G2, new | Complete inverse identity section formula. |
| Sheaf.CategoryTheory.SystemScalarOrdinaryAdjunction | G2, new | Complete fixed-model unit normalization. |

All public imports, signatures, data bodies, instances and attributes in the
consumer stay verbatim. There is no downstream interface change. No source-library
file is changed. No hole is added by these compilation repairs.

The final consumer and both ambient inverse-section helpers compile successfully
under the enforced per-file limit, without warnings.

## Status

landed 20261027T205959-L-1641374 2026-10-27 (merge of deliver/G2/Sheaf.Paper.AmbientPullbackTensorCoherence)

Repair after importer recheck 0cddc22b9: restore the reviewed proof import of
AmbientPullbackTensorCoherence in place of AmbientPullbackTensorData. Retain the
complete generic proof simplifications and all public signatures and definitions.

Reviewer fix (2026-10-27, packets 0cddc22b and c03e3912): the private theorem
`WeilConjectures.SequenceDerivedProof.normalizedComparisonDescent` stays in
`IntegralComparisonSequenceSystems`, with its original signature and body verbatim. The
`import all` user `Sheaf.Paper.FiniteQuotientPullbackDescent` (line 88) calls it,
and that module failed with `Unknown identifier` when the theorem was removed. The
generic copy in `NormalizedDerivedComparisonDescent` is private and not visible there.
The re-delivery c03e3912 dropped this restoration again; it is re-applied on top of the
restored `import Sheaf.Paper.AmbientPullbackTensorCoherence`. With it, the consumer and
FiniteQuotientPullbackDescent compile (31.6 s and 23.3 s), and so does StrictPullbackAdjointConstructor (18.4 s).
