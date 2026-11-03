/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurSupportTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Meanings attached to the support-localization triangle

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).

The predicates below use the intrinsic constant-coefficient module category and the
chosen K-injective resolution from `PurSupportTriangle`.  In particular, a pullback
is compared with a newly chosen resolution of the pulled-back input complex.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

variable {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/--
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).  This is the triangle attached to the intrinsic
support short exact sequence; its first map is the map whose cone is
`supportTriangleCone`.
-/
noncomputable def supportTriangle
    (K : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (hI : ∀ n : ℤ, Injective (r.complex.X n)) :
    Triangle (DerivedCategory
      (proEtaleRingModules X (proEtaleConstantRing X Λ))) := by
  let hPair : IsCompl (Set.range s.base) (Set.range j.base) := by
    rw [hcomp]
    exact isCompl_compl.symm
  exact DerivedCategory.triangleOfSES
    (proEtaleInjectiveSupportExact s j hPair Λ r.complex hI).1

/--
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).  This records a comparison map between two chosen
resolutions after localization.
-/
def supportTriangleResolutionComparison
    (K : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r r' : CochainComplex.KInjectiveResolutionChoice K.obj) : Prop :=
  ∃ a : r.complex ⟶ r'.complex,
    DerivedCategory.Q.map r.map ≫ DerivedCategory.Q.map a =
      DerivedCategory.Q.map r'.map

/--
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).  Canonicality asserts independence of the chosen
injective resolution and of the comparison lift in the derived category.
-/
def supportTriangleCanonicality
    (s : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion s] [IsOpenImmersion j]
    [QuasiCompact j] (hcomp : Set.range s.base = (Set.range j.base)ᶜ) : Prop :=
  ∀ (K : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r r' : CochainComplex.KInjectiveResolutionChoice K.obj),
    (hI : ∀ n : ℤ, Injective (r.complex.X n)) →
    (hI' : ∀ n : ℤ, Injective (r'.complex.X n)) →
    supportTriangleResolutionComparison Λ K r r' ∧
    ∀ (a b : r.complex ⟶ r'.complex),
      DerivedCategory.Q.map r.map ≫ DerivedCategory.Q.map a =
        DerivedCategory.Q.map r'.map →
      DerivedCategory.Q.map r.map ≫ DerivedCategory.Q.map b =
        DerivedCategory.Q.map r'.map →
      ∃ (t : supportTriangle s j hcomp Λ K r hI ≅
          supportTriangle s j hcomp Λ K r' hI'),
        t.hom.hom₂ = DerivedCategory.Q.map a ∧
        IsIso (DerivedCategory.Q.map a) ∧ IsIso (DerivedCategory.Q.map b)

/--
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).  Functoriality specifies the three components of
the triangle morphism and its identity and composition laws.
-/
def supportTriangleFunctoriality
    (s : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion s] [IsOpenImmersion j]
    [QuasiCompact j] (hcomp : Set.range s.base = (Set.range j.base)ᶜ) : Prop :=
  (∀ (K L : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (r' : CochainComplex.KInjectiveResolutionChoice L.obj)
    (hI : ∀ n : ℤ, Injective (r.complex.X n))
    (hI' : ∀ n : ℤ, Injective (r'.complex.X n))
    (f : K.obj ⟶ L.obj) (a : r.complex ⟶ r'.complex),
    DerivedCategory.Q.map r.map ≫ DerivedCategory.Q.map a =
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map r'.map →
    ∃! t : supportTriangle s j hcomp Λ K r hI ⟶
      supportTriangle s j hcomp Λ L r' hI',
      t.hom₂ = DerivedCategory.Q.map a ∧
      t.hom₁ = DerivedCategory.Q.map
        (((sfIntrinsicSectionsWithSupport j Λ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a) ∧
      t.hom₃ = DerivedCategory.Q.map
        (((sfConstantModulePullback j Λ ⋙ sfConstantModuleDirectImage j Λ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a)) ∧
  (∀ (K : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (hI : ∀ n : ℤ, Injective (r.complex.X n)),
    ∃! t : supportTriangle s j hcomp Λ K r hI ⟶
      supportTriangle s j hcomp Λ K r hI, t.hom₂ = 𝟙 _) ∧
  (∀ (K L M : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (rK : CochainComplex.KInjectiveResolutionChoice K.obj)
    (rL : CochainComplex.KInjectiveResolutionChoice L.obj)
    (rM : CochainComplex.KInjectiveResolutionChoice M.obj)
    (hK : ∀ n : ℤ, Injective (rK.complex.X n))
    (hL : ∀ n : ℤ, Injective (rL.complex.X n))
    (hM : ∀ n : ℤ, Injective (rM.complex.X n))
    (a : rK.complex ⟶ rL.complex) (b : rL.complex ⟶ rM.complex),
    ∀ (t₁ : supportTriangle s j hcomp Λ K rK hK ⟶
        supportTriangle s j hcomp Λ L rL hL)
      (t₂ : supportTriangle s j hcomp Λ L rL hL ⟶
        supportTriangle s j hcomp Λ M rM hM),
      t₁.hom₂ = DerivedCategory.Q.map a →
      t₂.hom₂ = DerivedCategory.Q.map b →
      (t₁ ≫ t₂).hom₂ = DerivedCategory.Q.map (a ≫ b))

/--
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).  Étale base change compares the pulled-back
triangle with the triangle for the pullbacks of the closed and open pieces and
of the input complex, using the canonical derived-category factor maps.
-/
def supportTriangleEtaleBaseChange
    (s : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion s] [IsOpenImmersion j]
    [QuasiCompact j] (hcomp : Set.range s.base = (Set.range j.base)ᶜ) : Prop :=
  ∀ {X' Z' U' : Scheme.{u}} (v : X' ⟶ X) (vZ : Z' ⟶ Z) (vU : U' ⟶ U)
    (s' : Z' ⟶ X') (j' : U' ⟶ X') [Etale v] [Etale vU]
    [IsClosedImmersion s'] [IsOpenImmersion j'] [QuasiCompact j']
    (hcomp' : Set.range s'.base = (Set.range j'.base)ᶜ)
    (_hs : IsPullback vZ s' s v) (_hj : IsPullback vU j' j v)
    (K : CochainComplex.Plus
      (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (hI : ∀ n : ℤ, Injective (r.complex.X n))
    (r' : CochainComplex.KInjectiveResolutionChoice
      ((sfConstantModulePullback v Λ).mapCochainComplexPlus.obj K).obj)
    (hI' : ∀ n : ℤ, Injective (r'.complex.X n)),
    ∃ (e : (sfIntrinsicSupportComplexSequence j Λ r.complex).map
        ((sfConstantModulePullback v Λ).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      sfIntrinsicSupportComplexSequence j' Λ r'.complex),
      DerivedCategory.Q.map
          (((sfConstantModulePullback v Λ).mapHomologicalComplex
            (ComplexShape.up ℤ)).map r.map) ≫
          DerivedCategory.Q.map e.τ₂ = DerivedCategory.Q.map r'.map ∧
      ∃ (t : (sfConstantModulePullback v Λ).mapDerivedCategory.mapTriangle.obj
          (supportTriangle s j hcomp Λ K r hI) ≅
        supportTriangle s' j' hcomp' Λ
          ((sfConstantModulePullback v Λ).mapCochainComplexPlus.obj K) r' hI'),
        t.hom.hom₁ =
            (sfConstantModulePullback v Λ).mapDerivedCategoryFactors.hom.app
                (sfIntrinsicSupportComplexSequence j Λ r.complex).X₁ ≫
              DerivedCategory.Q.map e.τ₁ ∧
          t.hom.hom₂ =
            (sfConstantModulePullback v Λ).mapDerivedCategoryFactors.hom.app r.complex ≫
              DerivedCategory.Q.map e.τ₂ ∧
          t.hom.hom₃ =
            (sfConstantModulePullback v Λ).mapDerivedCategoryFactors.hom.app
                (sfIntrinsicSupportComplexSequence j Λ r.complex).X₃ ≫
              DerivedCategory.Q.map e.τ₃

/--
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
def-pur-triangle-meaning.md`, node `def-pur-triangle-meaning` (blueprint:
def-pur-triangle-meaning).  The node's three meanings are conjoined here.
-/
def supportTriangleMeaning : Prop :=
  supportTriangleCanonicality (s := s) (j := j) (hcomp := hcomp) Λ ∧
    supportTriangleFunctoriality (s := s) (j := j) (hcomp := hcomp) Λ ∧
      supportTriangleEtaleBaseChange (s := s) (j := j) (hcomp := hcomp) Λ

end AlgebraicGeometry.Scheme
end
