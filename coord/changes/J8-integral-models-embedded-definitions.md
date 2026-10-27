# IntegralModelsEmbedded coefficient definition extraction

## Reason

The three separately proveable coefficient comparisons must use the same actual
embedded scalar maps and predicates as integral_models. Leaving their definitions
in IntegralModels would make the helper modules import the theorem module that
imports them, producing an import cycle. Extract the existing definitions verbatim
into IntegralModelsEmbedded and publicly re-export them. This is a source relocation,
not a slow-file split: the three theorem modules correspond to independent mathematical
comparisons in the unit. No target statement, definition data or public declaration
signature changes. The extracted stacksConstructible body is also kept verbatim.
The new residueConstructible predicate names its original residue conjunction;
it does not replace or weaken that conjunction in stacksConstructible.

Every public import of IntegralModels remains. Proof imports no longer used directly
are removed; their mathematical uses are retained under the appropriate helper nodes.
The private proof comparison modules are not re-exported by IntegralModels.

## Old

In lean/Sheaf/Paper/IntegralModels.lean:

```lean
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

/-- The discrete scalar ring on the pro-etale point. Source: Stacks Tag 09C1
(blueprint: sk-lem-integral-models). -/
abbrev discreteSheaf (A : Type) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A)))

/-- Its underlying condensed abelian ring object. Source: Stacks Tag 09C1
(blueprint: sk-lem-integral-models). -/
abbrev discreteObj (A : Type) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (discreteSheaf A)

/-- The commutative ring structure comes from the actual constant commutative ring sheaf.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
instance discreteObj_comm (A : Type) [CommRing A] : IsCommMonObj (discreteObj.{u} A) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (discreteSheaf A) (fun U a b ↦
      @mul_comm (((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))).obj.obj U) _ a b)

/-- The scalar map on the point sends an element to its constant continuous function.
Source: blueprint integral-models-stacks, the map from the constant sheaf
(blueprint: sk-lem-integral-models). -/
def constantToContinuous (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteSheaf.{u} A ⟶ Profinite.continuousMapRingSheaf.{u} A :=
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
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
def discreteMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    discreteObj.{u} A ⟶ discreteObj.{u} B :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)))))

/-- The source and target ring structures are the sheafified scalar structures.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
instance discreteMap_mon {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    IsMonHom (discreteMap.{u} f) := inferInstanceAs (IsMonHom
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _))

/-- The actual constant-to-continuous scalar map at the point.
Source: blueprint integral-models-stacks, Stacks Tag 09C1
(blueprint: sk-lem-integral-models). -/
def scalarPointMap (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    discreteObj (PadicAlgCl.integers ℓ E.1) ⟶ Profinite.padicIntegersRingObj.{u} ℓ E.1 :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (constantToContinuous (PadicAlgCl.integers ℓ E.1))

/-- The specified scalar map preserves the ring operations.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
instance scalarPointMap_mon (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : IsMonHom (scalarPointMap.{u} ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (constantToContinuous (PadicAlgCl.integers ℓ E.1))

/-- Pullback of the canonical constant-to-continuous scalar map.
Source: blueprint integral-models-stacks (blueprint: sk-lem-integral-models). -/
def scalarMap (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) := (upperStarFromPoint X).map (scalarPointMap ℓ E)

/-- The pulled-back scalar map is a ring-object map.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
instance scalarMap_mon (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) : IsMonHom (scalarMap ℓ E X) := inferInstanceAs
  (IsMonHom ((upperStarFromPoint X).map (scalarPointMap ℓ E)))

/-- The actual residue map between constant ring sheaves, at exponent one.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
def residueMap (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :=
  (upperStarFromPoint X).map
    (discreteMap (Ideal.Quotient.mk ((Ideal.span {π}) ^ (0 + 1))))

/-- The residue map retains its ring-object structure.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
instance residueMap_mon (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) : IsMonHom (residueMap ℓ E π X) :=
  inferInstanceAs (IsMonHom ((upperStarFromPoint X).map
    (discreteMap (Ideal.Quotient.mk ((Ideal.span {π}) ^ (0 + 1))))))

/-- Exact derived restriction along the canonical scalar map.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
abbrev restriction (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (scalarMap ℓ E X)).mapDerivedCategory

/-- The existing completeness predicate on the equivalent small ringed site.
Its kernel is the uniformizer ideal, so it is equivalent to the canonical derived
quotient-tower completion condition; no completeness hypothesis is built into D.
Source: Stacks Tags 099I and 09C1 (blueprint: sk-lem-integral-models). -/
abbrev complete (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (q : R ⟶ S) [IsMonHom q]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) : Prop :=
  ConstantCompletion.IsComplete (IntegralModelsStacks.smallMap X q)
    (IntegralModelsStacks.smallDerivedObject X R K)

/-- Complete completed-coefficient complexes, using their actual first reduction.
Source: Stacks Tags 099I and 09C1 (blueprint: sk-lem-integral-models). -/
abbrev completedComplete (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :=
  complete X (completedCoefficientMap X (completedReduction ℓ E π 0)).hom

/-- Complete constant-coefficient complexes, using the constant first residue map.
Source: Stacks Tags 099I and 09C1 (blueprint: sk-lem-integral-models). -/
abbrev constantComplete (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :=
  complete X (residueMap ℓ E π X)

/-- The Stacks constant-coefficient adic constructible category: completeness,
constructible residue cohomology and finite relative Tor amplitude.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
def stacksConstructible (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X))) := fun L ↦
  constantComplete ℓ E π X L ∧
  (∀ n : ℤ, IsConstantModelConstructible
    (discreteObj (completedResidue ℓ E π 0)) X
      ((DerivedCategory.homologyFunctor _ n).obj
        ((Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor.obj L))) ∧
  DerivedCategory.finiteTorAmplitude _
    ((Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor.obj L)

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

namespace AlgebraicGeometry.ProEtale


/-- The first completed-coefficient reduction is a bounded constructible complex pulled
back from the etale site. The scalar action is transported by the specified continuous
chart, restriction to constant functions, and intrinsic realization. Finiteness and
discreteness of the actual residue ring are conclusions, not extra hypotheses.
Source: blueprint integral models, clause (2) (blueprint: sk-lem-integral-models). -/
def integralModelResidueEtaleOrigin (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) : Prop := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact ∃ (_ : Finite (completedResidue ℓ E π 0))
    (_ : DiscreteTopology (completedResidue ℓ E π 0)),
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible.{u}
        (ULift.{u + 1, u} (ULift.{u, 0} (completedResidue ℓ E π 0))) X) ⋙
      finiteCoefficientIntrinsicDerivedComparison.{u} X
        (ULift.{u, 0} (completedResidue ℓ E π 0))).essImage
      (((integralModelIntrinsicRealization X (completedResidue ℓ E π 0)).rightDerivedFunctor).obj
        ((Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (integralModelReductionMap X ℓ E π 1).hom).leftDerivedFunctor.obj K))

```

## New

The same named definitions are in lean/Sheaf/Paper/IntegralModelsEmbedded.lean.
IntegralModels publicly imports that file. Local irreducibility attributes only
control elaboration; no definition body or instance data is changed. Source and
blueprint tags now point to def-sfb-embedded-integral-model-coefficients.

```lean
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- The discrete scalar ring on the pro-etale point. Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
abbrev discreteSheaf (A : Type) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A)))

/-- Its underlying condensed abelian ring object. Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
abbrev discreteObj (A : Type) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (discreteSheaf A)

/-- The commutative ring structure comes from the actual constant commutative ring sheaf.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
instance discreteObj_comm (A : Type) [CommRing A] : IsCommMonObj (discreteObj.{u} A) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (discreteSheaf A) (fun U a b ↦
      @mul_comm (((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))).obj.obj U) _ a b)

/-- The scalar map on the point sends an element to its constant continuous function.
Source: blueprint integral-models-stacks, the map from the constant sheaf
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
def constantToContinuous (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteSheaf.{u} A ⟶ Profinite.continuousMapRingSheaf.{u} A :=
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
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
def discreteMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    discreteObj.{u} A ⟶ discreteObj.{u} B :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)))))

/-- The source and target ring structures are the sheafified scalar structures.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
instance discreteMap_mon {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    IsMonHom (discreteMap.{u} f) := inferInstanceAs (IsMonHom
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _))

/-- The actual constant-to-continuous scalar map at the point.
Source: blueprint integral-models-stacks, Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
def scalarPointMap (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    discreteObj (PadicAlgCl.integers ℓ E.1) ⟶ Profinite.padicIntegersRingObj.{u} ℓ E.1 :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (constantToContinuous (PadicAlgCl.integers ℓ E.1))

/-- The specified scalar map preserves the ring operations.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
instance scalarPointMap_mon (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : IsMonHom (scalarPointMap.{u} ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (constantToContinuous (PadicAlgCl.integers ℓ E.1))

/-- Pullback of the canonical constant-to-continuous scalar map.
Source: blueprint integral-models-stacks
(blueprint: def-sfb-embedded-integral-model-coefficients).
-/
def scalarMap (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) := (upperStarFromPoint X).map (scalarPointMap ℓ E)

/-- The pulled-back scalar map is a ring-object map.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
instance scalarMap_mon (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) : IsMonHom (scalarMap ℓ E X) := inferInstanceAs
  (IsMonHom ((upperStarFromPoint X).map (scalarPointMap ℓ E)))

/-- The actual residue map between constant ring sheaves, at exponent one.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
def residueMap (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :=
  (upperStarFromPoint X).map
    (discreteMap (Ideal.Quotient.mk ((Ideal.span {π}) ^ (0 + 1))))

/-- The residue map retains its ring-object structure.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
instance residueMap_mon (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) : IsMonHom (residueMap ℓ E π X) :=
  inferInstanceAs (IsMonHom ((upperStarFromPoint X).map
    (discreteMap (Ideal.Quotient.mk ((Ideal.span {π}) ^ (0 + 1))))))

/-- Exact derived restriction along the canonical scalar map.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
abbrev restriction (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (scalarMap ℓ E X)).mapDerivedCategory

/-- The existing completeness predicate on the equivalent small ringed site.
Its kernel is the uniformizer ideal, so it is equivalent to the canonical derived
quotient-tower completion condition; no completeness hypothesis is built into D.
Source: Stacks Tags 099I and 09C1 (blueprint: def-sfb-embedded-integral-model-coefficients). -/
abbrev complete (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (q : R ⟶ S) [IsMonHom q]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) : Prop :=
  ConstantCompletion.IsComplete (IntegralModelsStacks.smallMap X q)
    (IntegralModelsStacks.smallDerivedObject X R K)

/-- Complete completed-coefficient complexes, using their actual first reduction.
Source: Stacks Tags 099I and 09C1 (blueprint: def-sfb-embedded-integral-model-coefficients). -/
abbrev completedComplete (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :=
  complete X (completedCoefficientMap X (completedReduction ℓ E π 0)).hom

/-- Complete constant-coefficient complexes, using the constant first residue map.
Source: Stacks Tags 099I and 09C1 (blueprint: def-sfb-embedded-integral-model-coefficients). -/
abbrev constantComplete (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :=
  complete X (residueMap ℓ E π X)

/-- Constructible cohomology and finite Tor amplitude of the first constant reduction.
Source: Stacks Tag 09C1
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
def residueConstructible (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X))) := fun L ↦
  (∀ n : ℤ, IsConstantModelConstructible
    (discreteObj (completedResidue ℓ E π 0)) X
      ((DerivedCategory.homologyFunctor _ n).obj
        ((Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor.obj L))) ∧
  DerivedCategory.finiteTorAmplitude _
    ((Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor.obj L)


/-- The Stacks constant-coefficient adic constructible category: completeness,
constructible residue cohomology and finite relative Tor amplitude.
Source: Stacks Tag 09C1 (blueprint: def-sfb-embedded-integral-model-coefficients). -/
def stacksConstructible (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X))) := fun L ↦
  constantComplete ℓ E π X L ∧
  (∀ n : ℤ, IsConstantModelConstructible
    (discreteObj (completedResidue ℓ E π 0)) X
      ((DerivedCategory.homologyFunctor _ n).obj
        ((Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor.obj L))) ∧
  DerivedCategory.finiteTorAmplitude _
    ((Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor.obj L)

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar


/-- The first completed-coefficient reduction is a bounded constructible complex pulled
back from the etale site. The scalar action is transported by the specified continuous
chart, restriction to constant functions, and intrinsic realization. Finiteness and
discreteness of the actual residue ring are conclusions, not extra hypotheses.
Source: blueprint integral models, clause (2)
(blueprint: def-sfb-embedded-integral-model-coefficients). -/
def integralModelResidueEtaleOrigin (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) : Prop := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact ∃ (_ : Finite (completedResidue ℓ E π 0))
    (_ : DiscreteTopology (completedResidue ℓ E π 0)),
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible.{u}
        (ULift.{u + 1, u} (ULift.{u, 0} (completedResidue ℓ E π 0))) X) ⋙
      finiteCoefficientIntrinsicDerivedComparison.{u} X
        (ULift.{u, 0} (completedResidue ℓ E π 0))).essImage
      (((integralModelIntrinsicRealization X (completedResidue ℓ E π 0)).rightDerivedFunctor).obj
        ((Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (integralModelReductionMap X ℓ E π 1).hom).leftDerivedFunctor.obj K))

end AlgebraicGeometry.ProEtale
```

## Users

The table includes all 46 transitive consumers reported by downstream.py and the
item module. The only external textual use of the extracted namespace is
IntegralTensorInverseImage; there is no external direct use of
integralModelResidueEtaleOrigin. No consumer needs a source adaptation because
IntegralModels publicly re-exports exactly the same declaration names and bodies.
The public target statements and all definitions they use retain their meanings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralModels | J8 | Re-exports the extracted definitions; theorem proved by the displayed assembly. Signature unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | E5 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | E7 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | Z9 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.RationalTatePullback | C9 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | F6 | Uses completedComplete in IntegralPullbackIsCompleted. Its definition and data are unchanged and re-exported; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | S8 | Definitions and theorem remain publicly available under identical names and types; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Definitions and theorem remain publicly available under identical names and types; no adaptation. |

## Status

landed 20261023T231645-L-3629673 2026-10-23 (merge of deliver/J8/Sheaf.Paper.IntegralModels)
