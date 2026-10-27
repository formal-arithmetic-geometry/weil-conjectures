# IntegralModelsStacks coefficient and predicate declarations

## Reason

The proof dependencies need the existing coefficient maps and predicates without
importing the theorem that they prove. Move those declarations, verbatim and with
the same namespace and instances, into IntegralModelsStacksData, and re-export it
from IntegralModelsStacks. The original public imports remain public imports.
No declaration signature, scalar map, predicate, universe or target meaning changes.

## Old

The declarations from `discreteSheaf` through `stacksConstructible` were defined
in `Sheaf.AlgebraicGeometry.IntegralModelsStacks`, before `integral_models_stacks`.
Their complete original source follows.

```lean
/-- The discrete scalar ring on the pro-etale point. Source: Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks). -/
abbrev discreteSheaf (A : Type u) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A)))

/-- Its underlying condensed abelian ring object. Source: Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks). -/
abbrev discreteObj (A : Type u) [CommRing A] :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (discreteSheaf A)

/-- The commutative ring structure comes from the actual constant commutative ring sheaf.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
instance discreteObj_comm (A : Type u) [CommRing A] : IsCommMonObj (discreteObj A) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (discreteSheaf A) (fun U a b ↦
      @mul_comm (((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))).obj.obj U) _ a b)

/-- The scalar map on the point sends an element to its constant continuous function.
Source: blueprint integral-models-stacks, the map from the constant sheaf
(blueprint: det-lem-integral-models-stacks). -/
def constantToContinuous (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteSheaf A ⟶ Profinite.continuousMapRingSheafOfUniverse A :=
  ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} A))).hom ≫
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) RingCat.{u + 1}).homEquiv
    _ _).symm
      { app S := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ContinuousMap.C (α := S.unop)).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) }

/-- A scalar homomorphism induces the actual map between discrete condensed rings.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
def discreteMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    discreteObj A ⟶ discreteObj B :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)))))

/-- The source and target ring structures are the sheafified scalar structures.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
instance discreteMap_mon {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    IsMonHom (discreteMap f) := inferInstanceAs (IsMonHom
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _))

/-- Reconstruct the section-ring map of a map of internal commutative rings.
Source: Stacks Tag 00YV (blueprint: det-lem-integral-models-stacks). -/
def sectionMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf _ Ab.{u + 1}).mapCommMon.map (CommMon.homMk (Mon.ofHom f))))
    InternalAbelianSheafModule.commMonToRing.{u + 1}⟩

/-- The section ring on the equivalent coefficient-sized small pro-etale site.
Source: Stacks Tags 00YV and 09A5 (blueprint: det-lem-integral-models-stacks). -/
abbrev smallRing (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :=
  ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R)

/-- The same reconstructed coefficient homomorphism on the small site.
Source: Stacks Tags 00YV and 09A5 (blueprint: det-lem-integral-models-stacks). -/
def smallMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] : smallRing X R ⟶ smallRing X S :=
  ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).map
    (sectionMap X f)

/-- Sectionwise module transport to the equivalent small site. It preserves sections
and their scalar action. Source: Stacks Tags 00YV and 09A5
(blueprint: det-lem-integral-models-stacks). -/
def smallModules (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      ConstantCompletion.Mod (smallRing X R) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X) R).functor ⋙
    SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _)

/-- Transport a derived object by the sectionwise equivalence, on a localization
representative. This is the exact transport to the identical small ringed topos.
Source: Stacks Tags 00YV, 05RU and 09A5
(blueprint: det-lem-integral-models-stacks). -/
def smallDerivedObject (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    ConstantCompletion.D (smallRing X R) :=
  letI : (smallModules X R).PreservesZeroMorphisms :=
    { map_zero := fun _ _ ↦ rfl }
  (ConstantCompletion.Q _).obj (((smallModules X R).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage K))

/-- The existing completed integral condensed ring, without any finite-field base datum.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
abbrev integersObj (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  (sfbCondensedIntegers l E).X

/-- Commutativity of the continuous-function coefficient ring.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
instance integersObj_comm (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integersObj l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionIntegers l E))
    (fun S a b ↦ @mul_comm
      (ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers l E)) _ a b)

/-- The canonical map from discrete to completed integral coefficients on the point.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
def scalarPointMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    discreteObj (Padic.coefficientExtensionIntegers l E) ⟶ integersObj l E :=
  letI := spectralNorm.normedField (Padic l) E
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (constantToContinuous (Padic.coefficientExtensionIntegers l E))

/-- The scalar map preserves the ring operations by its construction from a ring map.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
instance scalarPointMap_mon (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsMonHom (scalarPointMap l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (constantToContinuous (Padic.coefficientExtensionIntegers l E))

/-- Pull back the specified constant-to-continuous map to X.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
def scalarMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (upperStarFromPoint X).map (scalarPointMap l E)

/-- Monoidality of the site inverse image preserves the specified coefficient map.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
instance scalarMap_mon (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    IsMonHom (scalarMap l E X) := inferInstanceAs
      (IsMonHom ((upperStarFromPoint X).map (scalarPointMap l E)))

/-- The canonical residue coefficient map on X, induced by the actual first quotient.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
def residueMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (upperStarFromPoint X).map
    (discreteMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)))

/-- The residue map is a map of the actual pulled-back commutative ring objects.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
instance residueMap_mon (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    IsMonHom (residueMap l E X) := inferInstanceAs
      (IsMonHom ((upperStarFromPoint X).map
        (discreteMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)))))

/-- Exact, termwise restriction along the canonical map from the constant coefficient ring.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
abbrev restriction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (scalarMap l E X)).mapDerivedCategory

/-- Stacks adic constructibility: local derived completeness for the kernel of the
first residue map, constructible residue cohomology, and finite relative Tor amplitude.
Transport to the equivalent small site is used only for the recorded local completeness
predicate; no hypothesis on the complex is imposed by this transport.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
def stacksConstructible (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))) :=
  fun L ↦
    ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
      (smallDerivedObject X _ L) ∧
    (∀ n : ℤ, IsConstantModelConstructible
      (discreteObj (Padic.coefficientExtensionRing l E 1)) X
        ((DerivedCategory.homologyFunctor _ n).obj
          ((Mod.extendScalars (residueMap l E X)).leftDerivedFunctor.obj L))) ∧
    DerivedCategory.finiteTorAmplitude _
      ((Mod.extendScalars (residueMap l E X)).leftDerivedFunctor.obj L)

```

## New

The data module additionally names the final two conjuncts as `residueCondition`;
its body is their verbatim conjunction, and the original predicate is unchanged.
The proved residueCondition_iso transports its homology and Tor predicates through
the displayed derived extension functor.

The exact declaration block above is in
`lean/Sheaf/AlgebraicGeometry/IntegralModelsStacksData.lean`, under the identical
namespace and options. The original module publicly imports this data module.
Its theorem retains its signature verbatim, with a proof assembled from the
normalized ordinary realization, the cohomological adic criterion and the
complete-object and residue comparisons. New public realization declarations
are in IntegralConstantModelRealization and have real functor constructions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | W6 (this assignment) | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed in this checkout | Same public declarations and definitions through the re-export; no adaptation. |

The consumer search is the transitive import search of tools/downstream.py plus
whole-name uses of the moved declarations. IntegralModels is the direct consumer
of their qualified names. IntegralTensorPullback has textual matches for generic
restriction terminology; its declarations are unaffected. No target statement or
definition body changes, so no semantic target review is reopened.

## Status

landed 20261024T021935-L-2879228 2026-10-24 (merge of deliver/W6/Sheaf.AlgebraicGeometry.IntegralModelsStacks)
