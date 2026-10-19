/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.IntegralModelsStacks
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.SixFunctors.IntegralModelsGenerators
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit

/-! # Integral models for constructible l-adic complexes

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-integral-models/_section.md and its twelve reviewed proof steps
(blueprint: sk-lem-integral-models).

Coefficients are the existing continuous condensed rings pulled back from the point.
The constant and completed ambient categories remain distinct. Completeness is the
existing local ringed-ideal predicate transported to the equivalent small site; the
constant-completion comparison identifies it with the canonical quotient-tower condition.

## Main definitions and statement

* `IntegralModelsEmbedded`: canonical embedded-coefficient scalar maps and predicates.
* `integralModelResidueEtaleOrigin`: bounded constructible etale origin of the first reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
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
    (X : Scheme.{u}) :
    condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X ⟶
      integralCoefficientObject X ℓ E :=
  (upperStarFromPoint X).map (scalarPointMap ℓ E)

/-- The pulled-back scalar map is a ring-object map.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
instance scalarMap_mon (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) : IsMonHom (scalarMap ℓ E X) := inferInstanceAs
  (IsMonHom ((upperStarFromPoint X).map (scalarPointMap ℓ E)))

/-- The actual residue map between constant ring sheaves, at exponent one.
Source: Stacks Tag 09C1 (blueprint: sk-lem-integral-models). -/
def residueMap (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X ⟶
      condensedRingObj (discreteObj (completedResidue ℓ E π 0)) X :=
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
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :=
  complete X (completedCoefficientMap X (completedReduction ℓ E π 0)).hom

/-- Complete constant-coefficient complexes, using the constant first residue map.
Source: Stacks Tags 099I and 09C1 (blueprint: sk-lem-integral-models). -/
abbrev constantComplete (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X))) :=
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
  letI : Abelian.HasKInjectiveResolutions
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj (completedResidue ℓ E π 0)) X)) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
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
