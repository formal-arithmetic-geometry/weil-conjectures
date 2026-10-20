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
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.Paper.IntegralModelsOperations
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion

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
* `integral_models`: the opening Tor-amplitude equality and all four integral-model clauses.
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

/-- Integral constructible complexes have finite Tor amplitude. Restriction along the
canonical constant-to-completed scalar map identifies complete objects and the two
constructibility conditions. The categories are preserved by inverse image, ambient
uncompleted relative derived tensor, and locally closed extension by zero. Rational
constructible objects are generated by integral lattices under finite cones and shifts,
using one finite coefficient field per algebraic-closure object. The same integral
extension by zero has the stated derived reductions at every positive exponent.

Source: blueprint main-20261015, sk-lem-integral-models, clauses (1)--(4) and opening equality
(blueprint: sk-lem-integral-models).

Proof (the node's twelve steps):
1. det-def-localizing-closure-ctf-equals-bc gives Tor amplitude [r-1,s] for each bounded
constructible integral K with cohomology in [r,s]. The reverse inclusion is definitional.
2. det-prop-integral-criterion-constant-coefficients (1)--(3) gives flatness, all quotient
identifications, the restriction equivalence on complete objects, and reduction comparison.
3. det-lem-integral-models-stacks gives the first equivalence in clause (2), in the two
separate ambient categories; its complete-subcategory equivalence selects those objects.
4. Every module over the constant residue field is flat: choose bases on presheaf sections
and apply lem-pc-sites-modules-sheafification-flat (Stacks 03ET).
5. A bounded residue complex has a bounded good truncation of flat terms; use
lem-pc-bounded-above-flat-kflat-site (Stacks 06YQ) to compute its tensor. Conversely finite
Tor dimension gives boundedness by testing the tensor unit.
6. Unpack the Stacks category. lem-weil-pbc-constant-completion-equivalence identifies the
canonical completion units of arbitrary objects, so completeness is preserved and reflected.
sk-thm-pe-constructible-comparison identifies the residue condition with bounded etale
origin. This proves both directions of the second criterion in clause (2).
7. det-lem-integral-models-operations (1) gives inverse-image preservation;
sk-prop-sfb-cartesian-coefficients identifies exact inverse image with total derived pullback.
8. det-lem-integral-models-operations (2) gives the ambient uncompleted tensor assertion.
9. Apply its clause (3) to the open-then-closed factorization, whose open part is
quasi-compact because all schemes are Noetherian. This gives i_* u_! preservation.
10. det-lem-integral-models-generators (1) gives finite cone-and-shift generation by
integralModelGenerator, the scalar extensions of the specified locally free lattices.
11. Its clause (2) gives the analogous generation over the algebraic closure, with a
single finite subfield chosen before taking the finite triangulated closure.
12. Its clause (3), integralReductionHasEtaleOrigin, gives integral constructibility and
the isomorphism of each derived reduction with a_!(L_0/pi^n), bounded constructible and of
etale origin, for the very same lattice and every n >= 1.
-/
theorem integral_models
    (k : Type u) [Field k] (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    [CharP k p] (hℓp : ℓ ≠ p) (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) :
    ((constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X ⊓
        DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X) ∧
    (∃ e : ObjectProperty.FullSubcategory (IntegralModelsEmbedded.completedComplete ℓ E π X) ≌
        ObjectProperty.FullSubcategory (IntegralModelsEmbedded.constantComplete ℓ E π X),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IntegralModelsEmbedded.constantComplete ℓ E π X) ≅
        ObjectProperty.ι (IntegralModelsEmbedded.completedComplete ℓ E π X) ⋙
          IntegralModelsEmbedded.restriction ℓ E X)) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
        IntegralModelsEmbedded.stacksConstructible ℓ E π X
          ((IntegralModelsEmbedded.restriction ℓ E X).obj K)) ∧
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
        IntegralModelsEmbedded.completedComplete ℓ E π X K ∧
          integralModelResidueEtaleOrigin X ℓ E π K)) ∧
    (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
      [IsNoetherian Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (integralCoefficientObject Y ℓ E))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        ((CondensedRing.moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.1)
          f).obj K)) ∧
    (∀ K M : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        (((CondensedRing.derivedTensor (Profinite.padicIntegersRingObj ℓ E.1) X).obj K).obj M)) ∧
    (∀ (S V : Scheme.{u}) [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
      [IsNoetherian S] [IsNoetherian V] (j : S ⟶ V) (i : V ⟶ X)
      [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.1)
          i).obj (((CondensedRing.openImmersionLowerShriek
            (Profinite.padicIntegersRingObj ℓ E.1) j).mapDerivedCategory).obj L))) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K →
      (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (qlbarCoefficientObject X ℓ)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
      ∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        (sInf {P | qlbarModelGenerator X ℓ E' ≤ P ∧ P.IsTriangulated ∧
          P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ (S V : Scheme.{u}) [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
      [IsNoetherian S] [IsNoetherian V] (j : S ⟶ V) (i : V ⟶ X)
      [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E)),
      CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ →
      integralReductionHasEtaleOrigin X ℓ E π j i L₀) := by
  sorry

end AlgebraicGeometry.ProEtale
