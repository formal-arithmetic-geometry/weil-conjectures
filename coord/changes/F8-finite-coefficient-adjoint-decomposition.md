# FiniteCoefficientAdjoints interface relocation and decomposition

## Reason

Expose the existing interfaces independently of the assembly theorem, so three strictly smaller
geometric obligations can import them without an import cycle. This relocation is required by
the proof dependency direction; it is not a way to evade a compilation limit.

## Old

`Sheaf.Paper.FiniteCoefficientAdjointComparisons` contained 38 interface/arithmetic declarations
and one unproved system-existence theorem. The arithmetic nodes incorrectly cited that theorem
as a statement dependency, although their statements use only stages and arrows.

The original declarations, unchanged by relocation, have these signatures:

```lean
structure Stage (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
abbrev Stage.integers (s : Stage l E)
def Stage.parameter (s : Stage l E) : s.integers
def Stage.ideal (s : Stage l E) : Ideal s.integers
abbrev Stage.ring (s : Stage l E)
def baseStage (n : ℕ+) : Stage l E
def baseCoefficientEquiv (n : ℕ+) : (baseStage (l := l) (E := E) n).ring ≃+* Padic.coefficientExtensionRing l E (n : ℕ)
theorem stageFinite (s : Stage l E) : Finite s.ring
structure Arrow (s t : Stage l E)
theorem Arrow.ideal_le {s t : Stage l E} (a : Arrow s t) : s.ideal ≤ t.ideal.comap (strictEtaleIntegerMap l a.embedding)
def Arrow.ringMap {s t : Stage l E} (a : Arrow s t) : s.ring →+* t.ring
def Arrow.IsFiniteFree {s t : Stage l E} (a : Arrow s t) : Prop
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
abbrev ctf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
abbrev tensor {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
abbrev nu (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
abbrev rnu (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
abbrev lower (A : Type (u + 1)) [CommRing A] (c : Compactification f)
theorem etaleLeftAdjoint (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsLeftAdjoint
def etaleUpper (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherian X] [IsNoetherian Y] (c : Compactification f)
def etaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ etaleUpper A c
def upper (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) : D A Y ⥤ D A X
def restrict {A B : Type (u + 1)} [CommRing A] [CommRing B] {T U : Scheme.{u}} (F : D A T ⥤ D B U) (h : ∀ K, ctf A T K → ctf B U (F.obj K))
structure AdjointDatum (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherian X] [IsNoetherian Y] (c : Compactification f)
abbrev AdjointDatum.unit {c : Compactification f} (d : AdjointDatum A c) (K : (ctf A X).FullSubcategory)
abbrev AdjointDatum.counit {c : Compactification f} (d : AdjointDatum A c) (K : (ctf A Y).FullSubcategory)
def projectionAtWitness (φ : A →+* B) (c : Compactification f) (K : (ctf A X).FullSubcategory) (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩) (hB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj w.complex.obj)) : (tensor φ Y).obj ((lower A c).obj K.obj) ⟶ (lower B c).obj ((tensor φ X).obj K.obj)
structure Change (φ : A →+* B) (c : Compactification f) (dA : AdjointDatum A c) (dB : AdjointDatum B c)
def refinementAtWitness [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {c d : Compactification f} (r : c.Refinement d) (K : (ctf A X).FullSubcategory) (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩) : (lower A c).obj K.obj ⟶ (lower A d).obj K.obj
structure RefinementDatum [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {c d : Compactification f} (r : c.Refinement d) (dc : AdjointDatum A c) (dd : AdjointDatum A d)
theorem Arrow.ringMap_id {s : Stage l E} (a : Arrow s s) (h : a.embedding = AlgHom.id (Padic l) s.field) : a.ringMap = RingHom.id s.ring
theorem Arrow.ringMap_comp {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding) : ab.ringMap = b.ringMap.comp a.ringMap
structure System (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
theorem finiteTypeNoetherian (k : Type u) [Field k] (T : Scheme.{u}) [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] : IsNoetherian T
theorem finiteTypeMorphismProperties (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] : IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f
def FiniteTypeSystem (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
theorem stage_ramification (s : Stage l E) : ∃ (e : ℕ+) (z : s.integersˣ), s.parameter = (z : s.integers) * Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧ (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n = Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧ ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ)
theorem stage_finiteFree {s t : Stage l E} (a : Arrow s t) (h : s.exponent = t.exponent) : a.IsFiniteFree
```

The original theorem signature is retained verbatim in its module:

```lean
theorem finite_coefficient_adjoint_comparisons
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∃ (S : FiniteTypeSystem l E k f),
      (∀ (s : Stage l E) (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
        ctf s.ring X K.obj → ctf s.ring Y ((lower s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
        ctf s.ring Y K.obj → ctf s.ring X ((upper s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) (c : Compactification f),
        Nonempty {d : (restrict (lower s.ring c) (S.datum s c).lower_preserves ⊣
            restrict (upper s.ring c) (S.datum s c).upper_preserves) //
          d = (S.datum s c).adjunction}) ∧
      (∀ (s : Stage l E) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        DerivedCategory.TStructure.t.plus
          ((etaleUpper s.ring c).obj ((rnu s.ring Y).obj K.obj))) ∧
      (∀ (s : Stage l E) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        ((S.datum s c).adjunction.counit.app K).hom =
          (ProEtale.compactSupportSiteComparison s.ring c).hom.app
              ⟨(etaleUpper s.ring c).obj ((rnu s.ring Y).obj K.obj),
                (S.datum s c).etaleBound K.obj K.property⟩ ≫
            (nu s.ring Y).map ((etaleAdjunction s.ring c).counit.app
              ((rnu s.ring Y).obj K.obj)) ≫
            (ProEtale.derivedComparisonAdjunction
              (ModuleCat.{u + 1} s.ring) Y).counit.app K.obj) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        ctf s.ring X K.obj → ctf t.ring X ((tensor a.ringMap X).obj K.obj)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        ctf s.ring Y K.obj → ctf t.ring Y ((tensor a.ringMap Y).obj K.obj)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
        Nonempty {q : ((ctf s.ring X).ι ⋙ lower s.ring c ⋙ tensor a.ringMap Y ≅
            (ctf s.ring X).ι ⋙ tensor a.ringMap X ⋙ lower t.ring c) //
          q = (S.change a c).projection}) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
        Nonempty {b : ((ctf s.ring Y).ι ⋙ upper s.ring c ⋙ tensor a.ringMap X ≅
            (ctf s.ring Y).ι ⋙ tensor a.ringMap Y ⋙ upper t.ring c) //
          b = (S.change a c).mate}) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory)
          (w : Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩),
        DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension a.ringMap X).obj w.complex.obj)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory)
          (w : Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩),
        (S.change a c).projection.hom.app K =
          projectionAtWitness a.ringMap c K w
            ((S.change a c).etale_tensor_bound K w)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        (lower t.ring c).map ((S.change a c).mate.hom.app K) ≫
            (S.datum t c).counit
              ⟨(tensor a.ringMap Y).obj K.obj,
                (S.change a c).tensor_preserves_Y K.obj K.property⟩ =
          (S.change a c).projection.inv.app
              ⟨(upper s.ring c).obj K.obj,
                (S.datum s c).upper_preserves K.obj K.property⟩ ≫
            (tensor a.ringMap Y).map ((S.datum s c).counit K)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        (tensor a.ringMap X).map ((S.datum s c).unit K) ≫
            (S.change a c).mate.hom.app
              ⟨(lower s.ring c).obj K.obj,
                (S.datum s c).lower_preserves K.obj K.property⟩ ≫
            (upper t.ring c).map ((S.change a c).projection.hom.app K) =
          (S.datum t c).unit
            ⟨(tensor a.ringMap X).obj K.obj,
              (S.change a c).tensor_preserves_X K.obj K.property⟩) ∧
      (∀ (s : Stage l E) (K : (ctf s.ring X).FullSubcategory),
        ∃ w : Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩,
          w = S.origin_X s K) ∧
      (∀ (s : Stage l E) (K : (ctf s.ring Y).FullSubcategory),
        ∃ w : Scheme.FixedEtaleOriginWitness Y s.ring ⟨K.obj, K.property.plus⟩,
          w = S.origin_Y s K) ∧
      (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
          (h : ab.embedding = b.embedding.comp a.embedding) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        (tensor b.ringMap Y).map ((S.change a c).projection.hom.app K) ≫
            (S.change b c).projection.hom.app
              ⟨(tensor a.ringMap X).obj K.obj,
                (S.change a c).tensor_preserves_X K.obj K.property⟩ ≫
            (lower v.ring c).map
              ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
                a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
          (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
              a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
                ((lower s.ring c).obj K.obj) ≫
            (S.change ab c).projection.hom.app K) ∧
      (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
          (h : ab.embedding = b.embedding.comp a.embedding) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        (tensor b.ringMap X).map ((S.change a c).mate.hom.app K) ≫
            (S.change b c).mate.hom.app
              ⟨(tensor a.ringMap Y).obj K.obj,
                (S.change a c).tensor_preserves_Y K.obj K.property⟩ ≫
            (upper v.ring c).map
              ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
                a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
          (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
              a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
                ((upper s.ring c).obj K.obj) ≫
            (S.change ab c).mate.hom.app K) ∧
      (∀ (s : Stage l E) (a : Arrow s s)
          (h : a.embedding = AlgHom.id (Padic l) s.field) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        (S.change a c).projection.hom.app K ≫
            (lower s.ring c).map ((ProEtale.normalizedOriginScalarUnit
              (Scheme.ProEt.topology X) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
          (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
            a.ringMap (Arrow.ringMap_id a h)).hom.app ((lower s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) (a : Arrow s s)
          (h : a.embedding = AlgHom.id (Padic l) s.field) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        (S.change a c).mate.hom.app K ≫
            (upper s.ring c).map ((ProEtale.normalizedOriginScalarUnit
              (Scheme.ProEt.topology Y) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
          (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
            a.ringMap (Arrow.ringMap_id a h)).hom.app ((upper s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) {c d : Compactification f} (r : c.Refinement d),
        Nonempty {z : RefinementDatum r (S.datum s c) (S.datum s d) //
          z = S.refinement s r}) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) {c d : Compactification f}
          (r : c.Refinement d) (K : (ctf s.ring X).FullSubcategory),
        (tensor a.ringMap Y).map ((S.refinement s r).lowerIso.hom.app K) ≫
            (S.change a d).projection.hom.app K =
          (S.change a c).projection.hom.app K ≫
            (S.refinement t r).lowerIso.hom.app
              ⟨(tensor a.ringMap X).obj K.obj,
                (S.change a c).tensor_preserves_X K.obj K.property⟩) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) {c d : Compactification f}
          (r : c.Refinement d) (K : (ctf s.ring Y).FullSubcategory),
        (tensor a.ringMap X).map ((S.refinement s r).upperIso.hom.app K) ≫
            (S.change a c).mate.hom.app K =
          (S.change a d).mate.hom.app K ≫
            (S.refinement t r).upperIso.hom.app
              ⟨(tensor a.ringMap Y).obj K.obj,
                (S.change a c).tensor_preserves_Y K.obj K.property⟩) ∧
      (∀ (s t : Stage l E) (a : Arrow s t),
        s.exponent = t.exponent → a.IsFiniteFree) ∧
      (∀ s : Stage l E, ∃ (e : ℕ+) (z : s.integersˣ),
        s.parameter = (z : s.integers) *
          Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
        (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
          Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
        ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ))
```

## New

The 38 declarations move verbatim, with the same signatures, visibility, bodies, namespaces and
instances, to `Sheaf.Paper.FiniteCoefficientAdjointData`. The original module publicly imports
that module. The original theorem retains its exact signature and is proved by assembly from
three new obligations. Its retained-origin helper is private and proved. No source-library
module changes. Local irreducible attributes only prevent elaboration from expanding generic
chosen adjoints/derived functors; they are not exported and alter no definition or statement.

Four existing Lean attachments follow the moved declarations (the parent attachment now lists
only its own theorem). The two arithmetic nodes cite `def-coef-finite-coefficient-stages` instead
of the system theorem, removing an artificial dependency cycle without changing mathematics.
No target or existing mathematical statement is changed.

## Users

All 38 pre-existing declarations retain their exact signatures and bodies. They remain
available through the original public import, so no consumer source adaptation is required.
New obligations import the extracted interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | J9 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | K9 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | R8 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Z9 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | Y7 | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same exported signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same exported signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | B8 | Same exported signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same exported signatures and definitions; no adaptation. |

## Status

landed 20261025T202009-L-2662190 2026-10-25 (merge of deliver/F8/Sheaf.Paper.FiniteCoefficientAdjointComparisons)
and coherence statements each have a source, complete proof plan, and unique-data conclusion.
