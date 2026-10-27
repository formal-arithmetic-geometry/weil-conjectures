# WeilConjectures.ProperCoefficientDescent comparison definitions

## Reason

The integral scalar-square subargument must be stated in its own module. It uses
PreservesProjections and InducedOnFullTower, which were declared together with the
parent theorem. Move the unchanged definitions and their existing prerequisites to
Sheaf.Paper.ProperCoefficientDescentData. The original module publicly imports this
module, so importing the original module still exposes the same declarations.
No definition body, signature, namespace, universe or existing attribute is changed.
The data module compiled on the remote service within the single-file limit.

## Old

The following declarations were in Sheaf.Paper.ProperCoefficientDescent:

```lean
/-- Applying ordinary derived direct image to the sectionwise identity open map.
Source: blueprint first paragraph (blueprint: lem-weil-proper-coefficient-descent). -/
def finiteIdentity {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (A : Type u) [CommRing A] [Finite A] :
    sfAmbientCompactSupportCandidate A (Compactification.ofIsProper f) ≅
      proEtaleConstantDerivedDirectImage f A :=
  isoWhiskerRight
      (sfIntrinsicDerivedOpenId A X)
      (proEtaleConstantDerivedDirectImage f A) ≪≫
    Functor.leftUnitor _

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The specified ordinary projection adjunct, transported through the normalized
strict reconstruction. It is not a freely chosen reduction arrow.
Source: blueprint first paragraph; Bhatt--Scholze 6.5.9
(blueprint: lem-weil-proper-coefficient-descent). -/
def ordinaryReduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l (Coefficient.{u} l Ω E) Y n).obj
        (((D.integral E).image.obj K).obj) ⟶
      sfFiniteDerivedDirectImage l (Coefficient.{u} l Ω E) f K.obj n :=
  ((derivedScalarExtensionRestrictionAdjunction l (Coefficient.{u} l Ω E) Y n).choose.homEquiv
    _ _).symm
    ((D.integral E).reconstruction.inv.app K ≫
      (sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E) f).map
        ((sfDerivedReductionUnit l (Coefficient.{u} l Ω E) X n).app K.obj) ≫
      (sfDerivedRestrictionComparison l (Coefficient.{u} l Ω E) f n).hom.app
        ((scalarReductionDerivedExtension l (Coefficient.{u} l Ω E) X n).obj K.obj))

/-- Identity open extension, derived before taking any quotient evaluation.
The input module isomorphisms are constrained on all sections in InducedOnFullTower.
Adjoint uniqueness and functorial derivation fix the entire derived map, including
its action on strict systems and total derived limits.
Source: blueprint first paragraph (blueprint: lem-weil-proper-coefficient-descent). -/
def completedIdentity (E : Index l Ω) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (a : proEtaleRingModuleDirectImage (𝟙 X)
      ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
      ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
      ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull (𝟙 X)) ≅ 𝟭 _)
    (b : proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring Y)
      ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
      ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull f) ≅
      sfCompletedModuleDirectImage l (Coefficient.{u} l Ω E) f) :
    PurCompactSupport.image (PurCompactSupport.completed l (Coefficient.{u} l Ω E))
        (Compactification.ofIsProper f) ≅
      sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E) f :=
  letI := sfCompletedModuleDirectImage_additive l (Coefficient.{u} l Ω E) f
  isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        ((PurCompactSupport.openAdjunction
          (PurCompactSupport.completed l (Coefficient.{u} l Ω E)) (𝟙 X)).leftAdjointIdIso
          ((proEtaleRingModuleAdjunction (𝟙 X)
            ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
            ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
            ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull (𝟙 X))).leftAdjointIdIso
            a)) ≪≫ Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _ ≪≫ Functor.rightDerivedFunctorNatIso b

section Descent
variable (B : FiniteFieldDatum.{u}) (hl : l ≠ B.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of B.k))] [Y.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))] [IsSeparated (Y ↘ Spec (.of B.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of B.k))] [IsProper f]

/-- The recorded finite integral compact-support action at the identity compactification.
The prime-unit proof is the published consequence of the finite-field datum.
Source: blueprint first paragraph (blueprint: lem-weil-proper-coefficient-descent). -/
abbrev compactIntegral (E : Index l Ω) :=
  sfCompactSupportFiniteIntegralFunctor l B.k (PurCompactSupport.coefficientPrimeUnit l B hl)
    (Compactification.ofIsProper f) (Coefficient.{u} l Ω E)

/-- The projection condition on the supplied integral comparison. Every index n denotes
exponent n+1; the finite map is ordinary direct image of the identity open comparison.
The compact projection is the actual adjunct of its chosen Roos projection, and the
ordinary projection is transported through the normalized strict reconstruction.
Source: blueprint first paragraph (blueprint: lem-weil-proper-coefficient-descent). -/
def PreservesProjections
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (θ : ∀ E : Index l Ω, compactIntegral l Ω B hl f E ≅ (D.integral E).image) : Prop :=
  ∀ (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (n : ℕ),
    (scalarReductionDerivedExtension l (Coefficient.{u} l Ω E) Y n).map
        ((θ E).hom.app K).hom ≫ ordinaryReduction l Ω f D E K n =
      (sfCompactSupportFiniteReductionIso l B.k (PurCompactSupport.coefficientPrimeUnit l B hl)
        (Compactification.ofIsProper f) (Coefficient.{u} l Ω E) K n).hom ≫
      (finiteIdentity f (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E) (n + 1))).hom.app
        ((scalarReductionDerivedExtension l (Coefficient.{u} l Ω E) X n).obj K.obj)

/-- The given comparison is induced by the section-normalized identity open map.
The first coordinate change is restriction along the canonical identity base change;
the second leaves the underlying direct-image sections unchanged. Deriving these
ordinary maps before applying the normalized reconstructions retains the full tower
map, rather than imposing equations only after separate finite evaluations.
Source: blueprint first paragraph (blueprint: lem-weil-proper-coefficient-descent). -/
def InducedOnFullTower
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (θ : ∀ E : Index l Ω, compactIntegral l Ω B hl f E ≅ (D.integral E).image) : Prop :=
  ∀ E : Index l Ω,
    ∃ (a : proEtaleRingModuleDirectImage (𝟙 X)
        ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
        ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
        ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull (𝟙 X)) ≅ 𝟭 _)
      (b : proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring Y)
        ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
        ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull f) ≅
        sfCompletedModuleDirectImage l (Coefficient.{u} l Ω E) f),
      (∀ (M : scalarReductionSource l (Coefficient.{u} l Ω E) X) (U : X.ProEt)
        (x : ((proEtaleRingModuleDirectImage (𝟙 X)
          ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
          ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
          ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull (𝟙 X))).obj M).val.obj
            (op U)),
        (a.hom.app M).val.app (op U) x =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op x) ∧
      (∀ (M : scalarReductionSource l (Coefficient.{u} l Ω E) X) (U : Y.ProEt)
        (x : ((proEtaleRingModuleDirectImage f
          ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring Y)
          ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).ring X)
          ((PurCompactSupport.completed l (Coefficient.{u} l Ω E)).pull f)).obj M).val.obj
            (op U)),
        HEq ((b.hom.app M).val.app (op U) x) x) ∧
      ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X,
        ((θ E).hom.app K).hom =
          (sfQcqsCompactSupportRealization l (Coefficient.{u} l Ω E) B.k
            (PurCompactSupport.coefficientPrimeUnit l B hl)
            (Compactification.ofIsProper f)).inv.app K ≫
          (completedIdentity l Ω E f a b).hom.app K.obj ≫
          (D.integral E).reconstruction.hom.app K

```

## New

The identical declarations above are in
`lean/Sheaf/Paper/ProperCoefficientDescentData.lean`, with their original public
prerequisites. The original module has this public import:

```lean
public import Sheaf.Paper.ProperCoefficientDescentData
```

The parent theorem's signature remains verbatim. New scalar-square statements import
the data module, and the parent imports them only for its proof. The new data node
records the moved definitions; the original node retains the parent declaration.

## Users

`python3 tools/downstream.py Sheaf.Paper.ProperCoefficientDescent` returned zero
current Lean importers. This is an interface-preserving move, not a withdrawal:
the parent node and all its DAG parents stay in place.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperCoefficientDescent | U1 | Publicly reexports the same definitions; proves the original theorem from the integral scalar square and rational descent. |
| Sheaf.Paper.ProperIntegralScalarSquare | U1 (new) | Uses the shared normalization data without importing the parent theorem. |
| Sheaf.Paper.ProperRationalScalarSquare | U1 (new) | Uses the shared notation and integral comparison types. |

## Status

landed 20261025T203314-L-2802271 2026-10-25 (merge of deliver/U1/Sheaf.Paper.ProperCoefficientDescent)
