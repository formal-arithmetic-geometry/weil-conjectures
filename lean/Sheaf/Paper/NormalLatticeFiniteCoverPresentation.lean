/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.Paper.LatticeSheafLocallyConstant
public import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.ContinuousCoefficientLocalization
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.SecPurity.NormalLocallyConstantFiniteSection

/-!
# Finite-cover presentations of integral lattices on normal schemes

Source: Bhatt--Scholze, Lemma 6.8.2(1),(2), Proposition 6.8.4(6),
Lemma 7.3.9 and proof of Lemma 7.4.10, pp. 59--60, 67--71
(blueprint: lem-a1-normal-lattice-finite-cover-presentation).

The completed ring is the actual limit of positive constant quotient sheaves.
Its localization uses the image of the constant uniformizer. Lattice classes use the
existing presentation by actual pairs, including their rationalization isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Normalization of the integral completion comparison by every positive reduction.
The finite quotient comparison sends each constant to the same constant function.
Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59
(blueprint: lem-a1-normal-lattice-finite-cover-presentation). -/
def normalLatticeCompletionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (i : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      Scheme.finiteCoefficientLimit l X E) : Prop :=
  ∀ n : ℕ, ∃ q : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (Scheme.finiteCoefficientRing l E n) ≅ Scheme.finiteContinuousCoefficientSheaf l X E n,
    (∀ (U : X.ProEtᵒᵖ) (a : Scheme.finiteCoefficientRing l E n) (x : U.unop.left),
      Scheme.finiteContinuousCoefficientValue l E X n U
        (q.hom.hom.app U ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (Scheme.finiteCoefficientRing l E n))).app U a)) x =
        a) ∧
    (∀ (U : X.ProEtᵒᵖ)
      (s : (latticeCoefficientSheaf X (latticeCoefficientIntegers l E)).obj.obj U)
      (x : U.unop.left),
      (Scheme.finiteContinuousCoefficientValue l E X n U
        ((i.hom ≫ limit.π (Scheme.finiteCoefficientTower l X E) (op n) ≫ q.hom).hom.app
          U s) x).down =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          ⟨WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E) (s.down x).val,
            (s.down x).property⟩)

/-- The uniformizer section in the completed ring, transported from the constant function
along the specified completion isomorphism. This is actual section data.
Source: Bhatt--Scholze, Lemma 6.8.2, pp. 58--59
(blueprint: lem-a1-normal-lattice-finite-cover-presentation). -/
def normalLatticeUniformizerSection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (i : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      Scheme.finiteCoefficientLimit l X E) :
    ((Scheme.finiteCoefficientLimit l X E).obj ⋙ forget CommRingCat).sections :=
  (Functor.sectionsFunctor X.ProEtᵒᵖ).map (Functor.whiskerRight i.hom.hom (forget CommRingCat))
    ⟨fun U ↦ ULift.up (ContinuousMap.const U.unop.left
      (⟨(WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)).symm
        (Padic.coefficientExtensionUniformizer l E).val,
        (Padic.coefficientExtensionUniformizer l E).property⟩ : latticeCoefficientIntegers l E)),
      fun _ ↦ rfl⟩

/-- The constant prime section, used for localization at ell.
Source: Bhatt--Scholze, Lemma 6.8.2(2), p. 59
(blueprint: lem-a1-normal-lattice-finite-cover-presentation). -/
def normalLatticePrimeSection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    ((Scheme.finiteCoefficientLimit l X E).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ (l : (Scheme.finiteCoefficientLimit l X E).obj.obj U),
    fun f ↦ map_natCast ((Scheme.finiteCoefficientLimit l X E).obj.map f).hom l⟩

/-- The rational localization of the completed ring at its specified constant uniformizer.
This abbreviates the existing sectionwise localization and sheafification construction.
Source: Bhatt--Scholze, Lemma 6.8.2(2), p. 59
(blueprint: lem-a1-normal-lattice-finite-cover-presentation). -/
abbrev normalLatticeRationalRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (i : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      Scheme.finiteCoefficientLimit l X E) :=
  ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} (Scheme.finiteCoefficientLimit l X E)
    (normalLatticeUniformizerSection l E X i)

/-- The canonical integral-to-rational coefficient map for the completed presentation.
Source: Bhatt--Scholze, Lemma 6.8.2(2), p. 59
(blueprint: lem-a1-normal-lattice-finite-cover-presentation). -/
abbrev normalLatticeCoefficientMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (i : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      Scheme.finiteCoefficientLimit l X E) :=
  ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} (Scheme.finiteCoefficientLimit l X E)
    (normalLatticeUniformizerSection l E X i)

/-- Restrict the rational scalar action through the specified coefficient isomorphism.
Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59--60
(blueprint: lem-a1-normal-lattice-finite-cover-presentation). -/
abbrev normalLatticeContinuousModule (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (i : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      Scheme.finiteCoefficientLimit l X E)
    (e : latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      normalLatticeRationalRing l E X i)
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (normalLatticeRationalRing l E X i))) :=
  (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)).obj L

/-- The normalized coefficient and finite-cover lattice presentation, including rank zero.
Source: Bhatt--Scholze, Lemma 6.8.2(1),(2), Proposition 6.8.4(6), Lemma 7.3.9 and
proof of Lemma 7.4.10, pp. 59--60, 67--71
(blueprint: lem-a1-normal-lattice-finite-cover-presentation).

Proof following the nine DAG steps:
1. Local Noetherianity gives quasi-separatedness. The closed-subset minimum principle
makes every descending closed chain stationary, giving the Noetherian topology.
2. Apply continuous-coefficient-completion. Its projection equations fix every residue
and constant and hence uniquely determine the integral coefficient identification.
3. Apply continuous-coefficient-localization. The DVR factorization ell = u varpi^e,
with e positive, identifies localization at ell and at varpi, fixing integral numerators.
4. Transport each finite local basis through the rational coefficient isomorphism.
5. Apply lattice-sheaf-locally-constant. Its presentation retains the exact intertwining
isomorphism relation and restrictions, and its local constant sets are the right cosets.
6. The identity coset gives the standard integral pair on each rational free chart.
This proves local nonemptiness, also for the zero-rank chart.
7. Apply normal-locally-constant-finite-section, after shrinking the class sheaf to the
site's value universe. Surjectivity of the presentation gives an actual representative.
8. Apply the normalized coefficient comparisons on Y. Profinite-coefficient-inverse-image
identifies the pulled completed ring by all its projections, and the etale continuous
coefficient comparison is the identity on functions. Thus the localized comparison fixes
the integral inclusion; transporting the actual pair gives the displayed B_Y-module and
its rationalization to the canonical inverse image of L.
9. No descent datum is introduced or required. -/
theorem normal_lattice_finite_cover_presentation
    (X : Scheme.{u}) [ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]
    [X.IsSeparated]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (l : ℕ) [Fact l.Prime] (hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    TopologicalSpace.NoetherianSpace X ∧ QuasiSeparatedSpace X ∧
    ∃ i : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
        Scheme.finiteCoefficientLimit l X E,
      normalLatticeCompletionNormalized l E X i ∧
      ∃ e : latticeCoefficientSheaf X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
            normalLatticeRationalRing l E X i,
        integralLatticeCoefficientMap X l E ≫ e.hom =
          i.hom ≫ normalLatticeCoefficientMap l E X i ∧
        (∃ eell : ringedLocalizationRingOfUniverses.{u + 1, u + 1, u}
            (Scheme.finiteCoefficientLimit l X E)
            (normalLatticePrimeSection l E X) ≅ normalLatticeRationalRing l E X i,
          ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u}
              (Scheme.finiteCoefficientLimit l X E) (normalLatticePrimeSection l E X) ≫ eell.hom =
            normalLatticeCoefficientMap l E X i) ∧
        ∀ (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (normalLatticeRationalRing l E X i))), L.IsFiniteLocallyFree →
          ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
            (c : ∀ U : X.ProEt,
              IntegralLatticePair (integralLatticeCoefficientMap X l E)
                (normalLatticeContinuousModule l E X i e L) U → F.obj.obj (op U)),
            IsLatticeClassPresentation (integralLatticeCoefficientMap X l E)
              (normalLatticeContinuousModule l E X i e L) F c ∧
            (∃ (I : Type (u + 1)) (U : I → X.ProEt),
              (Scheme.ProEt.topology X).CoversTop U ∧
              ∀ j : I, ∃ S : Type (u + 2), Nonempty
                ((constantSheaf ((Scheme.ProEt.topology X).over (U j)) (Type (u + 2))).obj
                  S ≅ F.over (U j))) ∧
            (∃ (I : Type (u + 1)) (U : I → X.ProEt),
              (Scheme.ProEt.topology X).CoversTop U ∧
                ∀ j : I, Nonempty (F.obj.obj (op (U j)))) ∧
            (∀ (U : X.ProEt) (r : ℕ)
              (t : (normalLatticeContinuousModule l E X i e L).over U ≅
                latticeFreeSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) U r),
              ∃ k : (constantSheaf ((Scheme.ProEt.topology X).over U) (Type (u + 2))).obj
                (ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) r)) ≅
                  F.over U,
                ∀ (g : Matrix.GeneralLinearGroup (Fin r)
                    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
                  (P : IntegralLatticePair (integralLatticeCoefficientMap X l E)
                    (normalLatticeContinuousModule l E X i e L) U),
                  k.hom.hom.app (op (Over.mk (𝟙 U)))
                    (((toSheafify ((Scheme.ProEt.topology X).over U)
                      ((Functor.const (Over U)ᵒᵖ).obj
                        (ULift.{u + 2} (integralMatrixCosets
                          (latticeCoefficientIntegers l E) r)))).app (op (Over.mk (𝟙 U))))
                      (ULift.up (Quotient.mk _ g))) = c U P ↔
                    ∀ T : (Over U)ᵒᵖ, Set.image (t.hom.val.app T) (P.image T) =
                      matrixLatticeImage X
                        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
                        (latticeCoefficientIntegers l E) U r g T) ∧
            ∃ Y : X.ProEt, IsFinite Y.hom ∧ Etale Y.hom ∧ Surjective Y.hom ∧
              Nonempty (IntegralLatticePair (integralLatticeCoefficientMap X l E)
                (normalLatticeContinuousModule l E X i e L) Y) ∧
              ∃ iY : latticeCoefficientSheaf Y.left (latticeCoefficientIntegers l E) ≅
                  Scheme.finiteCoefficientLimit l Y.left E,
                normalLatticeCompletionNormalized l E Y.left iY ∧
                ∃ cR : (Scheme.proEtaleSheafInverseImage Y.hom CommRingCat.{u + 1}).obj
                    (normalLatticeRationalRing l E X i) ≅ normalLatticeRationalRing l E Y.left iY,
                  (Scheme.proEtaleSheafInverseImage Y.hom CommRingCat.{u + 1}).map
                      (normalLatticeCoefficientMap l E X i) ≫ cR.hom =
                    Scheme.proEtaleProfiniteComparison Y.hom
                        (Scheme.finiteCoefficientRingTower l E) ≫
                      normalLatticeCoefficientMap l E Y.left iY ∧
                  ∃ M : ringedSiteModules.{u + 1}
                      ((sheafCompose (Scheme.ProEt.topology Y.left)
                        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                          (Scheme.finiteCoefficientLimit l Y.left E)),
                    M.IsFiniteLocallyFree ∧ Nonempty
                      (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
                        (normalLatticeCoefficientMap l E Y.left iY) M ≅
                      SheafOfModules.changeOfRings.{u, u + 1, u + 1} cR.hom
                        ((Scheme.proEtaleModuleInverseImage Y.hom
                          (normalLatticeRationalRing l E X i)).obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale
