/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Flat extension and projective Hom models

Source: Stacks Project, More on Algebra, Tags 0A66 and 0GMT; Algebra, Tag 00HD;
Derived Categories, Tag 06XN (blueprint: lem-trf-flat-projective-hom-models).
The canonical module Hom maps below expose the uniquely normalized witnesses of the
existing projective evaluation theorem. No new total Hom or derived Hom is constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CochainComplex

/-- Pre- and post-composition on the recorded product Hom complex. The coordinate
formula in the cited theorem determines this map uniquely.
Source: Stacks 0A66 (blueprint: lem-trf-flat-projective-hom-models). -/
def projectiveHomModelMap (R : Type u) [CommRing R]
    {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P' ⟶ P) (b : N ⟶ N') :
    moduleHomComplex P N ⟶ moduleHomComplex P' N' :=
  Classical.choose (projective_hom_evaluation_model R) a b

/-- The projective Hom comparison fixed by its evaluation/counit square. The existing
projective evaluation theorem determines this isomorphism uniquely by adjunction.
Source: Stacks 0A66 (blueprint: lem-trf-flat-projective-hom-models). -/
def projectiveHomModelIso (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hp : ∀ i : ℤ, Module.Projective R (P.X i))
    (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (moduleHomComplex P N) ≅
      (ordinaryModuleDerivedInternalHom R).obj (op (DerivedCategory.Q.obj P),
        DerivedCategory.Q.obj N) :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec
      (projective_hom_evaluation_model R))).2.2 P hb hp N

end CochainComplex

namespace ModuleCat

/-- Termwise ordinary extension, with S acting on the left tensor factor.
Source: Stacks 0GMT (blueprint: lem-trf-flat-projective-hom-models). -/
abbrev flatExtensionComplex {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :=
  (extendScalars.{u} φ).mapHomologicalComplex (.up ℤ)

/-- Termwise restriction, retaining every degree of an unbounded complex.
Source: Stacks 0GMT (blueprint: lem-trf-flat-projective-hom-models). -/
abbrev flatRestrictionComplex {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :=
  (restrictScalars.{u} φ).mapHomologicalComplex (.up ℤ)

/-- Flat extension preserves cycles, boundaries and their cohomology quotient, computes
its derived functor with the universal K-flat normalization, and carries bounded-above
projective Hom models to the corresponding derived internal Hom models.
Source: Stacks 00HD, 06XN, 0GMT, 0A66
(blueprint: lem-trf-flat-projective-hom-models).

Proof:
1. Apply flat tensor exactness to the cycle/boundary and boundary/cohomology short
   exact sequences (lem-weil-pbc-flat-tensor-exact). Their injection and quotient maps
   give z, b and h below; functoriality of these sequences gives naturality.
2. The cohomology comparison identifies H(Ff) with F(Hf), so F preserves every
   quasi-isomorphism, without bounds (def-weil-abstract-derived-category).
3. Exact-functor derived factorization and the universal scalar-resolution comparison
   identify the counit with the natural isomorphism c. On any K-flat resolution k,
   naturality gives c_C = LF(Qk)^{-1} c_K Q(Fk). Comparing two or three resolutions
   cancels these factors (lem-trf-ringed-scalar-universal-resolution-comparison).
4. Transport the normalized coefficient adjunction from the singleton site
   (lem-pur-sheaf-ring-derived-coefficient-adjunction and
   lem-weil-pbc-singleton-site-module-comparison). Resolve a complex by a flat-term
   K-flat complex (lem-pc-kflat-resolution), use naturality, and cancel its localized
   augmentation. The unit is 1 tensor x and the counit is scalar multiplication.
5. Extension preserves the upper support bound and projectivity of each term
   (lem-trf-local-projective-tensor-base-change); finite generation is unnecessary.
6. Apply lem-pod-projective-hom-evaluation-model over R and S. Equivalently apply
   Hom(P,-) to a K-injective resolution as in 0A66. The resulting quasi-isomorphism
   identifies the product Hom with def-pur-derived-internal-hom. Use c_P,c_N in the
   second comparison, contravariantly in P and covariantly in N.
7. The evaluation/counit square fixes the comparisons and gives mixed naturality.
   Quasi-isomorphisms in the target become invertible. Chain-homotopic source maps
   induce chain-homotopic Hom maps via T(f)=(-1)^|f| f h; localization removes this
   ambiguity (lem-pc-ring-derived-map-representative). Apply the same R-model with
   target U(FN). At no point is N or its total Hom assumed bounded or K-flat. -/
theorem flat_projective_hom_models {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) :
    (∃ z : ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (extendScalars φ).obj (C.cycles i) ≅ ((flatExtensionComplex φ).obj C).cycles i,
      ∃ b : ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
          (extendScalars φ).obj (image (C.d (i - 1) i)) ≅
            image (((flatExtensionComplex φ).obj C).d (i - 1) i),
        ∃ h : ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
            (extendScalars φ).obj (C.homology i) ≅
              ((flatExtensionComplex φ).obj C).homology i,
          (∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
            (z C i).hom ≫ ((flatExtensionComplex φ).obj C).iCycles i =
              (extendScalars φ).map (C.iCycles i)) ∧
          (∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
            (b C i).hom ≫ image.ι (((flatExtensionComplex φ).obj C).d (i - 1) i) =
              (extendScalars φ).map (image.ι (C.d (i - 1) i))) ∧
          (∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
            (extendScalars φ).map (factorThruImage (C.d (i - 1) i)) ≫ (b C i).hom =
              factorThruImage (((flatExtensionComplex φ).obj C).d (i - 1) i)) ∧
          (∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
            (z C i).hom ≫ ((flatExtensionComplex φ).obj C).homologyπ i =
              (extendScalars φ).map (C.homologyπ i) ≫ (h C i).hom) ∧
          (∀ (C D : CochainComplex (ModuleCat.{u} R) ℤ) (f : C ⟶ D) (i : ℤ),
            (extendScalars φ).map (HomologicalComplex.cyclesMap f i) ≫ (z D i).hom =
              (z C i).hom ≫
                HomologicalComplex.cyclesMap ((flatExtensionComplex φ).map f) i) ∧
          (∀ (C D : CochainComplex (ModuleCat.{u} R) ℤ) (f : C ⟶ D) (i : ℤ),
            (extendScalars φ).map (HomologicalComplex.homologyMap f i) ≫ (h D i).hom =
              (h C i).hom ≫
                HomologicalComplex.homologyMap ((flatExtensionComplex φ).map f) i)) ∧
    (∀ (C D : CochainComplex (ModuleCat.{u} R) ℤ) (f : C ⟶ D),
      QuasiIso f → QuasiIso ((flatExtensionComplex φ).map f)) ∧
    (∃ c : DerivedCategory.Q ⋙ ordinaryDerivedExtendScalars φ ≅
        flatExtensionComplex φ ⋙ DerivedCategory.Q,
      c.hom = (ordinaryDerivedChangeOfRings φ).counit ∧
      (∀ (K C : CochainComplex (ModuleCat.{u} R) ℤ) (k : K ⟶ C),
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K →
        ∀ [QuasiIso k],
          (c.app C).hom =
            (ordinaryDerivedExtendScalars φ).map (asIso (DerivedCategory.Q.map k)).inv ≫
              (c.app K).hom ≫ DerivedCategory.Q.map ((flatExtensionComplex φ).map k)) ∧
      (∀ (K L C : CochainComplex (ModuleCat.{u} R) ℤ) (k : K ⟶ C) (l : L ⟶ C),
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K →
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat L →
        ∀ [QuasiIso k] [QuasiIso l],
          (c.app K).inv ≫ (ordinaryDerivedExtendScalars φ).map
              (DerivedCategory.Q.map k ≫ (asIso (DerivedCategory.Q.map l)).inv) ≫
            (c.app L).hom ≫ DerivedCategory.Q.map ((flatExtensionComplex φ).map l) =
              DerivedCategory.Q.map ((flatExtensionComplex φ).map k)) ∧
      (∀ (K L M C : CochainComplex (ModuleCat.{u} R) ℤ)
        (k : K ⟶ C) (l : L ⟶ C) (m : M ⟶ C),
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K →
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat L →
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M →
        ∀ [QuasiIso k] [QuasiIso l] [QuasiIso m],
          ((c.app K).inv ≫ (ordinaryDerivedExtendScalars φ).map
              (DerivedCategory.Q.map k ≫ (asIso (DerivedCategory.Q.map l)).inv) ≫
            (c.app L).hom) ≫
          ((c.app L).inv ≫ (ordinaryDerivedExtendScalars φ).map
              (DerivedCategory.Q.map l ≫ (asIso (DerivedCategory.Q.map m)).inv) ≫
            (c.app M).hom) =
          (c.app K).inv ≫ (ordinaryDerivedExtendScalars φ).map
              (DerivedCategory.Q.map k ≫ (asIso (DerivedCategory.Q.map m)).inv) ≫
            (c.app M).hom) ∧
      (∃ a : ordinaryDerivedExtendScalars φ ⊣ derivedRestrictScalars φ,
        (∀ C : CochainComplex (ModuleCat.{u} R) ℤ,
          a.unit.app (DerivedCategory.Q.obj C) ≫
              (derivedRestrictScalars φ).map (c.app C).hom ≫
              (restrictScalars φ).mapDerivedCategoryFactors.hom.app
                ((flatExtensionComplex φ).obj C) =
            DerivedCategory.Q.map
              (((extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).unit.app C)) ∧
        (∀ Y : CochainComplex (ModuleCat.{u} S) ℤ,
          a.counit.app (DerivedCategory.Q.obj Y) =
            (ordinaryDerivedExtendScalars φ).map
                ((restrictScalars φ).mapDerivedCategoryFactors.hom.app Y) ≫
              (c.app ((flatRestrictionComplex φ).obj Y)).hom ≫
              DerivedCategory.Q.map
                (((extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).counit.app Y))) ∧
      (∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
        (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
        (hp : ∀ i : ℤ, Module.Projective R (P.X i)),
        ∃ (hbS : ∃ n : ℤ, ∀ i : ℤ, n < i →
            IsZero (((flatExtensionComplex φ).obj P).X i))
          (hpS : ∀ i : ℤ, Module.Projective S (((flatExtensionComplex φ).obj P).X i)),
          ∀ N : CochainComplex (ModuleCat.{u} R) ℤ,
            ∃ eS : DerivedCategory.Q.obj
                (CochainComplex.moduleHomComplex ((flatExtensionComplex φ).obj P)
                  ((flatExtensionComplex φ).obj N)) ≅
              (ordinaryModuleDerivedInternalHom S).obj
                (op ((ordinaryDerivedExtendScalars φ).obj (DerivedCategory.Q.obj P)),
                  (ordinaryDerivedExtendScalars φ).obj (DerivedCategory.Q.obj N)),
              eS.hom ≫
                  (MonoidalClosed.pre (c.app P).inv).app
                    ((ordinaryDerivedExtendScalars φ).obj (DerivedCategory.Q.obj N)) ≫
                  (ihom (DerivedCategory.Q.obj ((flatExtensionComplex φ).obj P))).map
                    (c.app N).hom =
                (CochainComplex.projectiveHomModelIso S
                  ((flatExtensionComplex φ).obj P) hbS hpS
                  ((flatExtensionComplex φ).obj N)).hom ∧
              (∃ eR : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P N) ≅
                  (ordinaryModuleDerivedInternalHom R).obj
                    (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj N),
                eR = CochainComplex.projectiveHomModelIso R P hb hp N) ∧
              (∃ eU : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P
                    ((flatRestrictionComplex φ).obj ((flatExtensionComplex φ).obj N))) ≅
                  (ordinaryModuleDerivedInternalHom R).obj (op (DerivedCategory.Q.obj P),
                    DerivedCategory.Q.obj
                      ((flatRestrictionComplex φ).obj ((flatExtensionComplex φ).obj N))),
                eU = CochainComplex.projectiveHomModelIso R P hb hp
                  ((flatRestrictionComplex φ).obj ((flatExtensionComplex φ).obj N))))) ∧
    (∀ (P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ)
      (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
      (hp : ∀ i : ℤ, Module.Projective R (P.X i))
      (hb' : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P'.X i))
      (hp' : ∀ i : ℤ, Module.Projective R (P'.X i)) (a : P' ⟶ P) (b : N ⟶ N'),
      DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap R a b) ≫
          (CochainComplex.projectiveHomModelIso R P' hb' hp' N').hom =
        (CochainComplex.projectiveHomModelIso R P hb hp N).hom ≫
          (ordinaryModuleDerivedInternalHom R).map
            ((DerivedCategory.Q.map a).op, DerivedCategory.Q.map b)) ∧
    (∀ (P P' N N' : CochainComplex (ModuleCat.{u} S) ℤ)
      (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
      (hp : ∀ i : ℤ, Module.Projective S (P.X i))
      (hb' : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P'.X i))
      (hp' : ∀ i : ℤ, Module.Projective S (P'.X i)) (a : P' ⟶ P) (b : N ⟶ N'),
      DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap S a b) ≫
          (CochainComplex.projectiveHomModelIso S P' hb' hp' N').hom =
        (CochainComplex.projectiveHomModelIso S P hb hp N).hom ≫
          (ordinaryModuleDerivedInternalHom S).map
            ((DerivedCategory.Q.map a).op, DerivedCategory.Q.map b)) ∧
    (∀ (P N N' : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i)) →
      (∀ i : ℤ, Module.Projective R (P.X i)) →
      ∀ (b : N ⟶ N'), QuasiIso b →
        IsIso (DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap R (𝟙 P) b))) ∧
    (∀ (P P' N : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i)) →
      (∀ i : ℤ, Module.Projective R (P.X i)) →
      (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P'.X i)) →
      (∀ i : ℤ, Module.Projective R (P'.X i)) →
      ∀ (a a' : P' ⟶ P), DerivedCategory.Q.map a = DerivedCategory.Q.map a' →
        DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap R a (𝟙 N)) =
          DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap R a' (𝟙 N))) ∧
    (∀ (P N N' : CochainComplex (ModuleCat.{u} S) ℤ),
      (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i)) →
      (∀ i : ℤ, Module.Projective S (P.X i)) →
      ∀ (b : N ⟶ N'), QuasiIso b →
        IsIso (DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap S (𝟙 P) b))) ∧
    (∀ (P P' N : CochainComplex (ModuleCat.{u} S) ℤ),
      (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i)) →
      (∀ i : ℤ, Module.Projective S (P.X i)) →
      (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P'.X i)) →
      (∀ i : ℤ, Module.Projective S (P'.X i)) →
      ∀ (a a' : P' ⟶ P), DerivedCategory.Q.map a = DerivedCategory.Q.map a' →
        DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap S a (𝟙 N)) =
          DerivedCategory.Q.map (CochainComplex.projectiveHomModelMap S a' (𝟙 N))) := by
  sorry

end ModuleCat
