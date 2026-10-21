/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import Sheaf.CategoryTheory.DerivedInjectiveBoundary
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.ConcreteCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
public import Sheaf.AlgebraicGeometry.SupportTriangleConstruction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.PurSupportExact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # The global boundary of the pro-etale support triangle

Source: Stacks Project, etale-cohomology.tex, Tag 09XP, section-cohomology-support;
derived.tex, Tag 014Z, section-canonical-delta-functor
(blueprint: lem-pur-proetale-support-global-boundary).

## Main statements

* `supportGlobalTriangleComparison` compares all three arrows, using the canonical
  right-derived units and the sectionwise kernel inclusion.
* `supportGlobalBoundaryNormalization` identifies the resulting boundary with the
  natural supported-cohomology boundary, including its cocycle formula with no extra sign.

All coefficients are ordinary constant-ring module sheaves, with no constructibility condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [hA : Finite A]

/-- Evaluation at a specified pro-etale object, using the existing section functor.
Source: Stacks Tag 09XP, section-cohomology-support
(blueprint: lem-pur-proetale-support-global-boundary). -/
abbrev supportGlobalEvaluation {X : Scheme.{u}} (V : X.ProEt) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)

/-- The site arrow for the specified complementary open, rather than a choice of open.
Source: Stacks Tag 09XP, restriction along the complement
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalRestriction {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk j (Category.comp_id j)

/-- The object of X's site underlying the terminal object of the open site.
Source: Stacks Tag 09XP, open-section formula
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenObjectIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        (Scheme.ProEt.mk (𝟙 U)) ≅ Scheme.ProEt.mk j :=
  MorphismProperty.Over.isoMk (Iso.refl U) (by simp)

/-- The canonical section formula `(j^*M)(U) ≅ M(U)`, using the recorded comparison
with open restriction and the identity of the underlying open object.
Source: Stacks Tag 09XP, open-section formula
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenSectionIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).obj
        ((upperStar (ModuleCat.{u + 1} A) j).obj M) ≅
      (supportGlobalEvaluation A (Scheme.ProEt.mk j)).obj M :=
  (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).mapIso
      ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app M) ≪≫
    M.obj.mapIso (supportGlobalOpenObjectIso j).symm.op

/-- Naturality of the canonical open-section formula.
Source: Stacks Tag 09XP (blueprint: lem-pur-proetale-support-global-boundary).
Proof: use naturality of the open-restriction comparison, and naturality of a sheaf
morphism at the isomorphism of the two presentations of the open object. -/
theorem supportGlobalOpenSectionIso_naturality {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)} (f : M ⟶ N) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).map
        ((upperStar (ModuleCat.{u + 1} A) j).map f) ≫
        (supportGlobalOpenSectionIso A j N).hom =
      (supportGlobalOpenSectionIso A j M).hom ≫
        (supportGlobalEvaluation A (Scheme.ProEt.mk j)).map f := by
  sorry

/-- The section formula as an isomorphism of functors, hence also of section complexes.
Source: Stacks Tag 09XP (blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenEvaluationIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} A) j ⋙
        supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U)) ≅
      supportGlobalEvaluation A (Scheme.ProEt.mk j) :=
  NatIso.ofComponents (supportGlobalOpenSectionIso A j)
    (supportGlobalOpenSectionIso_naturality A j)

/-- The natural derived identification `RΓ(U,j^*K) ≅ R(I ↦ I(U))(K)`.
It is constructed from the ordinary section formula and the unique unit-compatible
composition comparison. Exactness identifies `Rj^*` with the recorded termwise `j^*`.
Source: Stacks Tag 09XP (blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenDerivedIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).rightDerivedFunctorPlus ≅
      (supportGlobalEvaluation A (Scheme.ProEt.mk j)).rightDerivedFunctorPlus :=
  letI : (upperStar (ModuleCat.{u + 1} A) j).PreservesInjectiveObjects :=
    ⟨fun {M} hM ↦
      @injective_upperStar_obj_of_weaklyEtale _ _ _ _ _ _ j _ M hM⟩
  Functor.isoWhiskerRight
      (upperStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
      (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).rightDerivedFunctorPlus ≪≫
    Functor.rightDerivedFunctorPlusCompIso' (upperStar (ModuleCat.{u + 1} A) j)
      (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))) (supportGlobalOpenEvaluationIso A j)

/-- The zero composite of supported inclusion and restriction on section functors.
Source: Stacks Tag 09XP, kernel-of-restriction formula
(blueprint: lem-pur-proetale-support-global-boundary).
Proof: at each sheaf this is the defining equation of its sectionwise kernel. -/
theorem supportGlobalRestriction_zero {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (supportGlobalRestriction j) ≫
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        (supportGlobalRestriction j).op = 0 := by
  sorry

/-- The actual row of section complexes: kernel of restriction, sections on X, sections
on U. Its arrows are the kernel inclusion and restriction, not chosen maps.
Source: Stacks Tag 09XP, displayed injective restriction sequence
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalRow {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
  Functor.injectiveBoundaryRow
    (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
      (supportGlobalRestriction j))
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X)))
    (supportGlobalEvaluation A (Scheme.ProEt.mk j))
    (Sheaf.supportedSectionsInclusion _ _ (supportGlobalRestriction j))
    ((sheafSections _ _).map (supportGlobalRestriction j).op)
    (supportGlobalRestriction_zero A j) I

variable {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  [hi : IsClosedImmersion i] [IsOpenImmersion j] [hqc : QuasiCompact j]
  (hPair : IsCompl (Set.range i) (Set.range j))

/-- All three sheaf models used to compute derived global sections are K-injective.
Source: Stacks Tag 09XP, support-injective lemma and restriction sequence
(blueprint: lem-pur-proetale-support-global-boundary).
Proof: the support right adjoint preserves injectives because closed direct image is
exact. Closed and open direct images preserve injectives because their inverse images
are exact. Open restriction preserves injectives because extension by zero is exact.
These additive functors preserve the lower bound. Apply the bounded-below injective
K-injectivity lemma to the resulting complexes. -/
theorem supportGlobalModels_kInjective
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    I.obj.IsKInjective ∧
      (supportedSectionsComplex A i j hPair I.obj).IsKInjective ∧
      CochainComplex.IsKInjective (supportCComplex A j I.obj) := by
  sorry

/-- The canonical inverse derived-unit comparison on a K-injective model.
Source: Stacks Tags 05TI and 05TH, used in Tag 09XP
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalUnitIso
    (J : SupportComplex A X) (hJ : J.IsKInjective) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj
        (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).obj J) :=
  letI := hJ
  (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctorObjQIso J

/-- Derived global sections identify the entire specified support triangle with the
sectionwise supported triangle. The two chain isomorphisms are normalized by inclusion
and restriction; on injectives these determine them uniquely.
Source: Stacks Tag 09XP and Tag 014Z, cone-to-quotient construction
(blueprint: lem-pur-proetale-support-global-boundary).

Proof, following the node's steps 1--5: the supported-kernel comparison and support
exactness give the sheaf row with its actual kernel inclusion. The exact left adjoints
show that its three models are bounded below injective models. Restriction of an
injective module sheaf along the open monomorphism is surjective on sections by the
ringed-site restriction lemma, so the section row is short exact. Sections preserve the
supported kernel, giving a, and the direct-image section formula gives b. The cone has
injective terms since a finite sum of injectives is injective. Therefore the derived
units compute sections on the three models and on the cone. Sections carry its
signed differential matrix, inclusion and negative projection to the identical matrix
and maps of the section cone. Naturality of the unit at the cone quotient identifies
its image with the section quotient. Invert these quasi-isomorphisms. This gives the
triangle isomorphism with precisely the three displayed unit-normalized components,
including the shift comparison in the third-arrow square. -/
theorem supportGlobalTriangleComparison
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    ∃ (hR : (supportGlobalRow A j I).ShortExact)
      (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient A i j hPair I.obj)))
      (hqR : IsIso (DerivedCategory.Q.map
        (CochainComplex.mappingCone.descShortComplex (supportGlobalRow A j I))))
      (a : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
          (supportGlobalRow A j I).X₁)
      (b : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃),
      a.hom ≫ (supportGlobalRow A j I).f =
        ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f ∧
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ b.hom =
        (supportGlobalRow A j I).g ∧
      ∃ e : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctor
          ).mapTriangle.obj (supportModelTriangle A i j hPair I.obj hq)) ≅
            supportSequenceTriangle (supportGlobalRow A j I) hqR,
        e.hom.hom₁ =
          (supportGlobalUnitIso A (supportedSectionsComplex A i j hPair I.obj)
            (supportGlobalModels_kInjective A i j hPair I).2.1).hom ≫
              DerivedCategory.Q.map a.hom ∧
        e.hom.hom₂ = (supportGlobalUnitIso A I.obj
          (supportGlobalModels_kInjective A i j hPair I).1).hom ∧
        e.hom.hom₃ = (supportGlobalUnitIso A (supportCComplex A j I.obj)
          (supportGlobalModels_kInjective A i j hPair I).2.2).hom ≫
            DerivedCategory.Q.map b.hom ∧
        ∀ q : ℤ,
          DerivedCategory.HomologySequence.δ
              (supportSequenceTriangle (supportGlobalRow A j I) hqR) q (q + 1) rfl =
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q).hom.app
                (supportGlobalRow A j I).X₃ ≫
              hR.δ q (q + 1) rfl ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A)
                (q + 1)).inv.app (supportGlobalRow A j I).X₁ := by
  sorry

/-- Naturality of the normalized sectionwise identifications in chain maps of
injective representatives. Together with the natural derived units and the K-injective
Hom bijection, these are the naturality squares for every derived morphism in K.
Source: Stacks Tags 09XP, 014Z and 070I
(blueprint: lem-pur-proetale-support-global-boundary).
Proof: compose the first proposed equality with the monic support inclusion. The two
results agree by naturality of the actual supported inclusion. For the second square,
precompose with the degreewise epic restriction map out of I; both composites are
restriction followed by the given chain map. Cancel that epimorphism. The cone map is
(fb,fa) and commutes with quotient and negative projection. Derived units are natural,
and the K-injective Hom bijection represents every derived map by a chain map modulo
homotopy. All functors preserve homotopies, so the squares descend independently of
the representative and also compare distinct resolutions of one K. -/
theorem supportGlobalComparisonNatural
    (I J : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] (f : I ⟶ J)
    (aI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
        (supportGlobalRow A j I).X₁)
    (aJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair J.obj)) ≅
        (supportGlobalRow A j J).X₁)
    (bI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃)
    (bJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j J.obj)) ≅ (supportGlobalRow A j J).X₃)
    (_haI : aI.hom ≫ (supportGlobalRow A j I).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f)
    (_haJ : aJ.hom ≫ (supportGlobalRow A j J).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).f)
    (_hbI : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ bI.hom =
          (supportGlobalRow A j I).g)
    (_hbJ : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).g ≫ bJ.hom =
          (supportGlobalRow A j J).g) :
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportAMap A i j hPair f.hom) ≫ aJ.hom =
      aI.hom ≫ ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j)).mapHomologicalComplex
          (.up ℤ)).map f.hom ∧
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportCMap A j f.hom) ≫ bJ.hom =
      bI.hom ≫ ((supportGlobalEvaluation A (Scheme.ProEt.mk j)).mapHomologicalComplex
        (.up ℤ)).map f.hom := by
  sorry

include hA hi hqc hPair in
set_option linter.unusedSectionVars false in
/-- The supported cohomology boundary is the global triangle boundary, with the
positive differential-of-a-lift formula in every integer degree, naturally in K.
Source: Stacks Tag 09XP and Tag 014Z
(blueprint: lem-pur-proetale-support-global-boundary).

Proof, following steps 6--8: for a cocycle c choose a lift b by sectionwise
surjectivity. There is a unique a in the support kernel with u(a)=db. Its differential
vanishes since u is monic and d²=0. The section cone cocycle (b,-a) maps to c under
the cone quotient, and the third arrow -projection maps it to a. Thus the triangle
boundary is the snake boundary and sends [c] to [db], with no extra sign. Changing
the lift adds a boundary; changing the cocycle by a boundary does not change its
image. The derived-injective-boundary normalization identifies this with the natural
supported-cohomology boundary of the support long exact sequence. A chain map sends
(b,-a) to (fb,-fa) and commutes with the quotient and projection, so all comparisons
commute with chain maps. Every derived map into a bounded below injective complex is
represented by a chain map uniquely up to homotopy. Additive functors preserve these
homotopies; hence the normalization and identifications are natural for all derived
morphisms and independent of the chosen injective resolution. -/
theorem supportGlobalBoundaryNormalization :
    ∃ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤,
      Sheaf.SupportSequenceExact (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤ δ ∧
      ∀ (I : CochainComplex.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
        [∀ n : ℤ, Injective (I.obj.X n)],
        ∃ hR : (supportGlobalRow A j I).ShortExact,
          (∀ (K : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
            (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ),
            (Sheaf.supportSequenceModelIso _ _
              (supportGlobalEvaluation A (Scheme.ProEt.mk j)) I K e q).hom ≫
                (δ q).app ⟨K, trivial⟩ ≫
                (Sheaf.supportSequenceModelIso _ _
                  (Sheaf.supportedSectionsFunctor _ _ (supportGlobalRestriction j))
                  I K e (q + 1)).inv = hR.δ q (q + 1) rfl) ∧
          (∀ (q : ℤ) (c : (supportGlobalRow A j I).X₃.X q)
            (hc : (supportGlobalRow A j I).X₃.d q (q + 1) c = 0)
            (b : (supportGlobalRow A j I).X₂.X q)
            (_hb : (supportGlobalRow A j I).g.f q b = c),
            ∃ (a : (supportGlobalRow A j I).X₁.X (q + 1))
              (ha : (supportGlobalRow A j I).X₁.d (q + 1) (q + 1 + 1) a = 0),
              (supportGlobalRow A j I).f.f (q + 1) a =
                (supportGlobalRow A j I).X₂.d q (q + 1) b ∧
              hR.δ q (q + 1) rfl
                ((supportGlobalRow A j I).X₃.homologyπ q
                  ((supportGlobalRow A j I).X₃.cyclesMk c (q + 1) (by simp) hc)) =
                (supportGlobalRow A j I).X₁.homologyπ (q + 1)
                  ((supportGlobalRow A j I).X₁.cyclesMk a (q + 1 + 1) (by simp) ha)) := by
  sorry

end AlgebraicGeometry.ProEtale
