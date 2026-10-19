/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.Paper.EtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat

/-!
# Compatibility of normalized towers with retained étale origins

Source: blueprint, def-weil-pbc-witness-compatibility, order 1352;
Stacks Tags 09C9, 09C2, 06YY and 07A4
(blueprint: def-weil-pbc-witness-compatibility).

All finite coefficient categories use their canonical fixed-ring presentation. The
coefficient realization in def-weil-pbc-proetale-modules identifies them with modules
over the continuous-function coefficient sheaf. All outputs are ambient derived objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The positive quotient at exponent n+1, as a discrete coefficient type.
Source: Stacks 099L (blueprint: def-weil-pbc-witness-compatibility). -/
def PbcQuotient {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :=
  A ⧸ d.ideal ^ (n + 1)

/-- The actual quotient ring structure. Source: Stacks 099L
(blueprint: def-weil-pbc-witness-compatibility). -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    CommRing (PbcQuotient d n) := inferInstanceAs (CommRing (A ⧸ d.ideal ^ (n + 1)))

/-- Finiteness of the quotient coefficient set. Source: Stacks 099L
(blueprint: def-weil-pbc-witness-compatibility). -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    Finite (PbcQuotient d n) := d.quotientFinite n

/-- Each quotient coefficient ring has the discrete topology. Source: Stacks 099L
(blueprint: def-weil-pbc-witness-compatibility). -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    TopologicalSpace (PbcQuotient d n) := ⊥

/-- Discreteness of the quotient topology. Source: Stacks 099L
(blueprint: def-weil-pbc-witness-compatibility). -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    DiscreteTopology (PbcQuotient d n) := ⟨rfl⟩


/-- The published canonical quotient homomorphism at positive coefficient levels.
Source: Stacks 099L, blueprint order 1352
(blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessQuotientMap {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    PbcQuotient d b →+* PbcQuotient d a :=
  Scheme.adicQuotientMap d.ideal (b + 1) (a + 1) (Nat.add_le_add_right h 1)


variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/-- Derived restriction of scalars has a left adjoint for an arbitrary coefficient map.
Source: Stacks 06YY and 06XN (blueprint: def-weil-pbc-witness-compatibility).
Proof: use the canonical equivalence with modules over the constant ring sheaf and
lem-pur-derived-change-of-rings. K-flat resolutions compute scalar extension, whose
ordinary adjunction to restriction descends to the derived categories. Restriction is
exact. The resulting left adjoint is characterized by its universal arrow; neither
flatness of the coefficient map nor boundedness is required. -/
@[instance] theorem pbcRestriction_isRightAdjoint {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (Sheaf.derivedRestrictScalars J φ).IsRightAdjoint := by
  classical
  let E : Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const Cᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  exact (adj.derivedAdjunction.ofNatIsoRight
    U.rightDerivedFunctorIsoMapDerivedCategory).isRightAdjoint

/-- Derived scalar extension, fixed by the adjunction to actual restriction of scalars.
Source: Stacks 06YY (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcFixedScalarExtension {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) := (Sheaf.derivedRestrictScalars J φ).leftAdjoint

/-- The canonical composition comparison of derived scalar extensions, obtained by
conjugating the actual composition identification for restrictions of scalars.
Source: Stacks 06YY (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcFixedScalarExtensionComp {R S V : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    pbcFixedScalarExtension J φ ⋙ pbcFixedScalarExtension J ψ ≅ pbcFixedScalarExtension J χ :=
  Adjunction.leftAdjointCompIso (Adjunction.ofIsRightAdjoint _)
    (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
    (Sheaf.derivedRestrictScalarsCompIso J h)

variable (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

/-- Restriction commutes with comparison inverse image. This is the conjugate of the
sectionwise commutation of comparison restriction with coextension of scalars.
Source: Stacks 03D2 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcComparisonRestrict (φ : R →+* S) :
    comparisonUpperStar (ModuleCat.{u + 1} S) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} R) T :=
  ((conjugateIsoEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} S) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).comp
      (comparisonAdjunction (ModuleCat.{u + 1} R) T))).symm (Iso.refl _)).symm

/-- Exact descent of the preceding canonical restriction comparison.
Source: Stacks 03D2 and 06YY (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcDerivedComparisonRestrict (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pbcComparisonRestrict T φ) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The canonical scalar-extension comparison is the mate of the restriction comparison.
Source: Stacks 07A4 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcComparisonReductionMap (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ⟶
      pbcFixedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv)).natTrans

/-- The canonical mate is invertible, with no flatness condition on the ring map.
Source: Stacks 07A4 and 0G7E (blueprint: def-weil-pbc-witness-compatibility).
Proof: choose K-flat flat-term representatives. Comparison inverse image preserves
these resolutions. On them the mate is the ordinary balancing isomorphism identifying
inverse image of scalar extension with scalar extension of inverse image. Its inverse
is the opposite pure-tensor balancing map. The ordinary adjunction units characterize
these maps, so they compute exactly the displayed mate. Localizing gives invertibility
at every object, hence invertibility of the natural transformation. -/
theorem pbcComparisonReductionMap_isIso (φ : R →+* S) :
    IsIso (pbcComparisonReductionMap T φ) := by
  sorry

/-- The source identification in the witness compatibility equation.
Source: Stacks 07A4 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcComparisonReduction (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ≅
      pbcFixedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  haveI := pbcComparisonReductionMap_isIso T φ
  asIso (pbcComparisonReductionMap T φ)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {A : Type (u + 1)} [CommRing A]

/-- Ambient finite-level pro-étale derived objects, in the canonical fixed-ring
presentation. Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
abbrev PbcWitnessAmbient (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (PbcQuotient d n)))

/-- Ambient finite-level étale derived objects.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
abbrev PbcWitnessEtale (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :=
  DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (PbcQuotient d n)))

/-- Coefficient reduction between consecutive ambient pro-étale levels.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessReduction (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    PbcWitnessAmbient T d (n + 1) ⥤ PbcWitnessAmbient T d n :=
  pbcFixedScalarExtension (Scheme.ProEt.topology T)
    (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))

/-- Coefficient reduction between consecutive ambient étale levels.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessEtaleReduction
    (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    PbcWitnessEtale T d (n + 1) ⥤ PbcWitnessEtale T d n :=
  pbcFixedScalarExtension T.smallEtaleTopology (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))

/-- The bounded constructible input property, transported by the recorded canonical
coefficient realization. Source: blueprint order 1352
(blueprint: def-weil-pbc-witness-compatibility). -/
def pbcWitnessBoundedConstructible (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    ObjectProperty (PbcWitnessAmbient T d n) :=
  fun K ↦ isBoundedConstructibleFiniteCoefficient T (PbcQuotient d n)
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj K)

/-- Reflect the retained origin isomorphism through the canonical realization. This
uses the published retained-pair definition without defining another notion of origin.
Source: blueprint order 1352, displayed witness equation
(blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcFixedOriginAlpha (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus
      ((finiteCoefficientRealization T Λ).mapDerivedCategory.obj K))
    (W : EtaleOriginWitness T Λ
      ⟨(finiteCoefficientRealization T Λ).mapDerivedCategory.obj K, hK⟩) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj W.L.obj ≅ K :=
  (finiteCoefficientRealization T Λ).mapDerivedCategory.preimageIso
    ((Functor.mapDerivedCategoryCompIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
      (finiteCoefficientRealization T Λ)).symm.app W.L.obj ≪≫
        DerivedCategory.Plus.ι.mapIso W.alpha)

/-- A normalized tower with compatible retained origins. Only adjacent normalization
maps are independent data: longer reductions and their maps are the composites of
these, read through the canonical scalar-extension composition comparisons. Thus the
identity and quotient cocycles are built into the encoding.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
structure PbcWitnessedTower (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) where
  /-- The ambient pro-étale levels. -/
  K : ∀ n : ℕ, PbcWitnessAmbient T d n
  /-- Bounded-below membership is proof data, with no chosen numerical bound. -/
  boundedBelow : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (K n))
  /-- The retained pairs are those of the supplied étale-origin interface. -/
  origin : ∀ n : ℕ, EtaleOriginWitness T (PbcQuotient d n)
    ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (K n),
      boundedBelow n⟩
  /-- Input or output normalization at adjacent quotients. -/
  theta : ∀ n : ℕ, (pbcWitnessReduction T d n).obj (K (n + 1)) ≅ K n
  /-- Normalization on the retained étale origins. -/
  beta : ∀ n : ℕ,
    (pbcWitnessEtaleReduction T d n).obj (origin (n + 1)).L.obj ≅ (origin n).L.obj
  /-- The source of the right hand side is identified by the canonical tensor mate. -/
  compatibility : ∀ n : ℕ,
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (beta n).hom ≫
          (pbcFixedOriginAlpha T (PbcQuotient d n) (K n) (boundedBelow n) (origin n)).hom =
      (pbcComparisonReduction T (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
          (origin (n + 1)).L.obj ≫
        (pbcWitnessReduction T d n).map (pbcFixedOriginAlpha T (PbcQuotient d (n + 1)) (K (n + 1))
          (boundedBelow (n + 1)) (origin (n + 1))).hom ≫ (theta n).hom

/-- The comparison isomorphism of a retained origin, in the fixed-ring presentation.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def PbcWitnessedTower.alpha {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.obj
      (P.origin n).L.obj ≅ P.K n :=
  pbcFixedOriginAlpha T (PbcQuotient d n) (P.K n) (P.boundedBelow n) (P.origin n)

/-- Longer reductions are composites of consecutive reductions; length zero is identity.
The canonical composition isomorphism pbcFixedScalarExtensionComp identifies this convention
with direct quotient scalar extension. Source: blueprint order 1352
(blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcIteratedWitnessReduction (T : Scheme.{u})
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    (k : ℕ) → PbcWitnessAmbient T d (n + k) ⥤ PbcWitnessAmbient T d n
  | 0 => 𝟭 _
  | k + 1 => pbcWitnessReduction T d (n + k) ⋙ pbcIteratedWitnessReduction T d n k

/-- The quotient normalization at any length is its iterated composite. Thus the
identity and quotient cocycles impose no further choices beyond adjacent normalizations.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcIteratedWitnessTheta {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) (n : ℕ) :
    (k : ℕ) → (pbcIteratedWitnessReduction T d n k).obj (P.K (n + k)) ≅ P.K n
  | 0 => Iso.refl _
  | k + 1 => (pbcIteratedWitnessReduction T d n k).mapIso (P.theta (n + k)) ≪≫
      pbcIteratedWitnessTheta P n k

/-- A morphism retains both levelwise maps and both normalization compatibilities.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
@[ext] structure PbcWitnessedTowerHom {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P Q : PbcWitnessedTower T d) where
  /-- The underlying ambient maps. -/
  u : ∀ n : ℕ, P.K n ⟶ Q.K n
  /-- The maps on the retained étale origins. -/
  v : ∀ n : ℕ, (P.origin n).L.obj ⟶ (Q.origin n).L.obj
  /-- Compatibility with pro-étale normalizations. -/
  theta_naturality : ∀ n : ℕ,
    (pbcWitnessReduction T d n).map (u (n + 1)) ≫ (Q.theta n).hom =
      (P.theta n).hom ≫ u n
  /-- Compatibility with étale normalizations. -/
  beta_naturality : ∀ n : ℕ,
    (pbcWitnessEtaleReduction T d n).map (v (n + 1)) ≫ (Q.beta n).hom =
      (P.beta n).hom ≫ v n
  /-- The square involving the two retained comparison isomorphisms commutes. -/
  origin_naturality : ∀ n : ℕ,
    (P.alpha n).hom ≫ u n =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (v n) ≫ (Q.alpha n).hom

/-- Identity pairs satisfy the normalization and origin squares.
Source: blueprint order 1352, morphisms of witnessed towers
(blueprint: def-weil-pbc-witness-compatibility).
Proof: functors preserve identities; each square reduces to the identity laws. -/
theorem pbcWitnessedTower_id_laws {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) :
    (∀ n : ℕ, (pbcWitnessReduction T d n).map (𝟙 (P.K (n + 1))) ≫ (P.theta n).hom =
      (P.theta n).hom ≫ 𝟙 (P.K n)) ∧
    (∀ n : ℕ, (pbcWitnessEtaleReduction T d n).map (𝟙 (P.origin (n + 1)).L.obj) ≫
      (P.beta n).hom = (P.beta n).hom ≫ 𝟙 (P.origin n).L.obj) ∧
    (∀ n : ℕ, (P.alpha n).hom ≫ 𝟙 (P.K n) =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (𝟙 (P.origin n).L.obj) ≫ (P.alpha n).hom) := by
  constructor
  · intro n
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  constructor
  · intro n
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · intro n
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The identity has the actual identity map at both kinds of levels.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessedTowerId {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) : PbcWitnessedTowerHom P P where
  u := fun _ ↦ 𝟙 _
  v := fun _ ↦ 𝟙 _
  theta_naturality := (pbcWitnessedTower_id_laws P).1
  beta_naturality := (pbcWitnessedTower_id_laws P).2.1
  origin_naturality := (pbcWitnessedTower_id_laws P).2.2

/-- Composite pairs satisfy the normalization and origin squares.
Source: blueprint order 1352, morphisms of witnessed towers
(blueprint: def-weil-pbc-witness-compatibility).
Proof: expand functoriality on composites and paste the two normalization squares.
Paste the origin squares using associativity. -/
theorem pbcWitnessedTower_comp_laws {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    {P Q V : PbcWitnessedTower T d} (f : PbcWitnessedTowerHom P Q)
    (g : PbcWitnessedTowerHom Q V) :
    (∀ n : ℕ, (pbcWitnessReduction T d n).map (f.u (n + 1) ≫ g.u (n + 1)) ≫
      (V.theta n).hom = (P.theta n).hom ≫ (f.u n ≫ g.u n)) ∧
    (∀ n : ℕ, (pbcWitnessEtaleReduction T d n).map (f.v (n + 1) ≫ g.v (n + 1)) ≫
      (V.beta n).hom = (P.beta n).hom ≫ (f.v n ≫ g.v n)) ∧
    (∀ n : ℕ, (P.alpha n).hom ≫ (f.u n ≫ g.u n) =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (f.v n ≫ g.v n) ≫ (V.alpha n).hom) := by
  constructor
  · intro n
    rw [Functor.map_comp, Category.assoc, g.theta_naturality,
      ← Category.assoc, f.theta_naturality, Category.assoc]
  constructor
  · intro n
    rw [Functor.map_comp, Category.assoc, g.beta_naturality,
      ← Category.assoc, f.beta_naturality, Category.assoc]
  · intro n
    rw [← Category.assoc, f.origin_naturality, Category.assoc,
      g.origin_naturality, ← Category.assoc, ← Functor.map_comp]

/-- Composition has the actual levelwise composites of both maps.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessedTowerComp {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    {P Q V : PbcWitnessedTower T d} (f : PbcWitnessedTowerHom P Q)
    (g : PbcWitnessedTowerHom Q V) : PbcWitnessedTowerHom P V where
  u := fun n ↦ f.u n ≫ g.u n
  v := fun n ↦ f.v n ≫ g.v n
  theta_naturality := (pbcWitnessedTower_comp_laws f g).1
  beta_naturality := (pbcWitnessedTower_comp_laws f g).2.1
  origin_naturality := (pbcWitnessedTower_comp_laws f g).2.2

/-- The specified identity and composition satisfy the category axioms.
Source: blueprint order 1352, functorial transport of witnessed towers
(blueprint: def-weil-pbc-witness-compatibility).
Proof: compare the u and v components, using the left identity, right identity and
associativity laws in the derived categories. The proof fields agree by proof irrelevance. -/
theorem pbcWitnessedTower_category_laws (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) :
    (∀ (P Q : PbcWitnessedTower T d) (f : PbcWitnessedTowerHom P Q),
      pbcWitnessedTowerComp (pbcWitnessedTowerId P) f = f) ∧
    (∀ (P Q : PbcWitnessedTower T d) (f : PbcWitnessedTowerHom P Q),
      pbcWitnessedTowerComp f (pbcWitnessedTowerId Q) = f) ∧
    (∀ (P Q V W : PbcWitnessedTower T d) (f : PbcWitnessedTowerHom P Q)
      (g : PbcWitnessedTowerHom Q V) (h : PbcWitnessedTowerHom V W),
      pbcWitnessedTowerComp (pbcWitnessedTowerComp f g) h =
        pbcWitnessedTowerComp f (pbcWitnessedTowerComp g h)) := by
  constructor
  · intro P Q f
    ext n <;> simp [pbcWitnessedTowerComp, pbcWitnessedTowerId]
  constructor
  · intro P Q f
    ext n <;> simp [pbcWitnessedTowerComp, pbcWitnessedTowerId]
  · intro P Q V W f g h
    ext n <;> simp [pbcWitnessedTowerComp, Category.assoc]

/-- The category of witnessed normalized towers, with levelwise composition of pairs.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable instance (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) :
    Category (PbcWitnessedTower T d) where
  Hom := PbcWitnessedTowerHom
  id := pbcWitnessedTowerId
  comp := pbcWitnessedTowerComp
  id_comp := (pbcWitnessedTower_category_laws T d).1 _ _
  comp_id := (pbcWitnessedTower_category_laws T d).2.1 _ _
  assoc := (pbcWitnessedTower_category_laws T d).2.2 _ _ _ _

/-- The full subcategory of witnessed towers with bounded constructible input levels.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
abbrev PbcWitnessedInputTowers (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) :=
  ObjectProperty.FullSubcategory (fun P : PbcWitnessedTower T d ↦
    ∀ n : ℕ, pbcWitnessBoundedConstructible T d n (P.K n))

/-- The full test subcategory at a consecutive pair of levels. Both the original object
and its reduction must be bounded constructible; no output boundedness is assumed.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
def pbcWitnessReductionDomain (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    ObjectProperty (PbcWitnessAmbient T d (n + 1)) :=
  fun K ↦ pbcWitnessBoundedConstructible T d (n + 1) K ∧
    pbcWitnessBoundedConstructible T d n ((pbcWitnessReduction T d n).obj K)

/-- A normalized bounded constructible tower belongs to the stated test subcategory.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility).
Proof: its next level is bounded constructible by the input condition. Its reduction
is isomorphic, via theta, to the current bounded constructible level. The canonical
realization preserves isomorphisms, and the constructible essential-image property is
closed under isomorphisms. Thus its reduction also belongs to the test category. -/
theorem pbcWitnessedInput_memReductionDomain (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    (P : PbcWitnessedInputTowers T d) (n : ℕ) :
    pbcWitnessReductionDomain T d n (P.obj.K (n + 1)) := by
  refine ⟨P.property (n + 1), ?_⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := P.property n
  exact ⟨L, hL, ⟨e ≪≫
    (finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.mapIso
      (P.obj.theta n).symm⟩⟩

/-- One family carries compatible retained witnesses functorially, with precisely the
normalization prescribed by rho. The family is tested only on the stated full input
subcategory, and rho on longer quotient maps is its iterated composite.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
def PbcFamilyWitnessCompatibility (T S : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    (F : ∀ n : ℕ, PbcWitnessAmbient T d n ⥤ PbcWitnessAmbient S d n) : Prop :=
  ∃ (rho : ∀ n : ℕ,
      (pbcWitnessReductionDomain T d n).ι ⋙ F (n + 1) ⋙ pbcWitnessReduction S d n ≅
        (pbcWitnessReductionDomain T d n).ι ⋙ pbcWitnessReduction T d n ⋙ F n)
    (lift : PbcWitnessedInputTowers T d ⥤ PbcWitnessedTower S d)
    (hobj : ∀ (P : PbcWitnessedInputTowers T d) (n : ℕ),
      (lift.obj P).K n = (F n).obj (P.obj.K n)),
    (∀ (P Q : PbcWitnessedInputTowers T d) (a : P ⟶ Q) (n : ℕ),
      (lift.map a).u n = eqToHom (hobj P n) ≫ (F n).map (a.hom.u n) ≫
        eqToHom (hobj Q n).symm) ∧
    ∀ (P : PbcWitnessedInputTowers T d) (n : ℕ),
      ((lift.obj P).theta n).hom =
        (pbcWitnessReduction S d n).map (eqToHom (hobj P (n + 1))) ≫
          (rho n).hom.app ⟨P.obj.K (n + 1), pbcWitnessedInput_memReductionDomain T d P n⟩ ≫
            (F n).map (P.obj.theta n).hom ≫ eqToHom (hobj P n).symm

/-- The ordinary ambient finite-level derived direct images, with no constructible
output restriction. Source: blueprint order 1352
(blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessDirectImage {T S : Scheme.{u}} (f : T ⟶ S)
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    PbcWitnessAmbient T d n ⥤ PbcWitnessAmbient S d n :=
  (finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory ⋙
    finiteCoefficientDerivedDirectImage f (PbcQuotient d n) ⋙
      (finiteCoefficientUnrealization S (PbcQuotient d n)).mapDerivedCategory

/-- The ordinary ambient finite-level derived pullbacks, computed by exact inverse image.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
noncomputable def pbcWitnessPullback {T S : Scheme.{u}} (g : S ⟶ T)
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    PbcWitnessAmbient T d n ⥤ PbcWitnessAmbient S d n :=
  (finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory ⋙
    finiteCoefficientDerivedPullback T (PbcQuotient d n) g ⋙
      (finiteCoefficientUnrealization S (PbcQuotient d n)).mapDerivedCategory

/-- WIT for the four ambient families of the given cartesian square. It is a compatibility
predicate relative to fixed adic coefficients; it makes no assertion that arbitrary
squares satisfy it and assumes no AMP restriction on outputs.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
def WitnessCompatibility {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (_sq : ChosenCartesianSquare g' f' f g) (d : Scheme.AdicCoefficientDatum A) : Prop :=
  PbcFamilyWitnessCompatibility X Y d (pbcWitnessDirectImage f d) ∧
    PbcFamilyWitnessCompatibility X' Y' d (pbcWitnessDirectImage f' d) ∧
      PbcFamilyWitnessCompatibility Y Y' d (pbcWitnessPullback g d) ∧
        PbcFamilyWitnessCompatibility X X' d (pbcWitnessPullback g' d)

end AlgebraicGeometry.ProEtale
