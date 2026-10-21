module

public import Sheaf.Paper.AffineLinePurityCoordinateMaps
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula

/-! # The twisted affine-line source and its etale origin

Source: main-20261015, sec-smooth-purity/sk-prop-an,
affine-line purity comparison, order 2318 (blueprint: def-pur-affine-line-purity-source).

The actual compared Tate coefficient, its inverse-limit identification, the
literal twisted inverse image, and its explicit bounded-below ordinary origin.
All comparison isomorphisms are compositions of the recorded canonical maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineLinePurity

open VectorIntegrationSite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ) (Y : Scheme.{u})

variable (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient l E n)) = 0)

/-- The shifted ordinary Tate coefficient restricted to the standard affine chart.
The canonical Tate pullback identifies it with B_X[2]. Source: main-20261015,
affine-line purity comparison (blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def etaleCoefficient :
    Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y) :=
  (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
    (ProjectiveLine.affineChart Y)).obj
    (linePlus l E n r hA (ProjectiveLine Y)).obj

/-- A_X(1)[2] in the canonical comparison coordinates fixed by tau and Tate pullback.
Source: main-20261015, affine-line purity comparison
(blueprint: def-pur-affine-line-purity-source). -/
abbrev coefficient : DerivedCategory
    (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} Y))
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).obj
    (etaleCoefficient l E n Y r hA)

/-- Defining comparison coordinate equality, retained for inexpensive transport.
Source: the displayed coefficient (blueprint: def-pur-affine-line-purity-source).
Proof: unfold coefficient; the two objects are identical by reflexivity. -/
theorem coefficient_comparison_eq : coefficient l E n Y r hA =
    (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).obj
      (etaleCoefficient l E n Y r hA) := by
  sorry

/-- The defining ordinary shifted-line coordinate equality.
Source: the displayed coefficient (blueprint: def-pur-affine-line-purity-source).
Proof: unfold etaleCoefficient and linePlus; the underlying object is identical. -/
theorem etaleCoefficient_eq : etaleCoefficient l E n Y r hA =
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
      (ProjectiveLine.affineChart Y)).obj
      ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine Y))⟦(2 : ℤ)⟧) := by
  sorry

/-- Identification with the specified inverse-limit pro-etale twist, not a new Tate line.
The ordinary pullback is fixed on roots and the final map is tau shifted by two.
Source: main-20261015, Tate comparison paragraph
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def coefficientTwistIso
    (hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)))
    (hX : IsUnit (l : Γ(AffineSpace PUnit.{u + 1} Y, ⊤))) :
    coefficient l E n Y r hA ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteTateProSheaf l E n
          (AffineSpace PUnit.{u + 1} Y) 1))⟦(2 : ℤ)⟧ :=
  eqToIso (coefficient_comparison_eq l E n Y r hA) ≪≫
    (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).mapIso
      (eqToIso (etaleCoefficient_eq l E n Y r hA)) ≪≫
    twistPullbackComparison l E n r hA (ProjectiveLine.affineChart Y) hP hX

/-- The literal pro-etale twisted inverse image M_K = Lp^*K tensor A_X(1)[2].
Source: main-20261015, transpose display
(blueprint: def-pur-affine-line-purity-source). -/
abbrev source (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} Y))
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  projectionSourceObject (Scheme.finiteTateCoefficient l E n)
    (AffineSpace PUnit.{u + 1} Y ↘ Y) (coefficient l E n Y r hA) K

/-- The explicit ordinary representative of the twisted source.
Source: main-20261015, etale-origin witness
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def etaleSource (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y) :
    Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y) :=
  ordinarySourceObject (Scheme.finiteTateCoefficient l E n)
    (AffineSpace PUnit.{u + 1} Y ↘ Y) (etaleCoefficient l E n Y r hA) K

/-- The literal tensor expression defining the pro-etale source.
Source: M_K display (blueprint: def-pur-affine-line-purity-source).
Proof: unfold source, projectionSourceObject and coefficient; both sides are the same
derived tensor object. -/
theorem source_eq
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    source l E n Y r hA K =
    ((derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (AffineSpace PUnit.{u + 1} Y)).obj
      ((upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (AffineSpace PUnit.{u + 1} Y ↘ Y)).leftDerivedFunctor.obj K)).obj
      (coefficient l E n Y r hA) := by
  sorry

/-- The literal tensor expression defining the ordinary source.
Source: ordinary source display (blueprint: def-pur-affine-line-purity-source).
Proof: unfold etaleSource; both sides are the same cached derived tensor object. -/
theorem etaleSource_eq
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y) :
    etaleSource l E n Y r hA Ke =
    ordinarySourceObject (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y ↘ Y) (etaleCoefficient l E n Y r hA) Ke := by
  sorry

/-- The defining pro-etale coordinate, using the cached literal tensor template.
Source: M_K display (blueprint: def-pur-affine-line-purity-source).
Proof: unfold source, proSourceObject and coefficient; both sides are identical
by reflexivity. -/
theorem source_coordinate_eq
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    source l E n Y r hA K =
    proSourceObject (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y ↘ Y) (etaleCoefficient l E n Y r hA) K := by
  sorry

/-- Canonical tensor/pullback comparison, followed by the chosen realization of K.
Source: main-20261015, explicit witness display
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def sourceComparison
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).obj
      (etaleSource l E n Y r hA Ke) ≅ source l E n Y r hA K :=
  (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).mapIso
      (eqToIso (etaleSource_eq l E n Y r hA Ke)) ≪≫
    realizedTensorComparison (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y ↘ Y) K Ke (etaleCoefficient l E n Y r hA) eK ≪≫
    (eqToIso (source_coordinate_eq l E n Y r hA K)).symm

/-- The representative displayed in the node is bounded below.
Source: main-20261015, bounded etale-origin paragraph
(blueprint: def-pur-affine-line-purity-source).
Proof: Ke is bounded constructible of finite Tor amplitude. Exact p_e^* preserves
its bounds. Tensoring a finite-Tor-amplitude complex with the degree-zero
ordinary Tate sheaf has a finite lower bound, shifted by -2. On the unit-prime
domain of the node the Tate sheaf is furthermore locally free of rank one. -/
theorem etaleSource_plus (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke) :
    DerivedCategory.TStructure.t.plus (etaleSource l E n Y r hA Ke) := by
  sorry

/-- The realized source has the same lower bound.
Source: main-20261015, bounded etale-origin paragraph
(blueprint: def-pur-affine-line-purity-source).
Proof: exact comparison preserves the lower bound of etaleSource_plus.
Transfer it along sourceComparison. This uses no exceptional adjunction. -/
theorem source_plus
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    DerivedCategory.TStructure.t.plus (source l E n Y r hA K) := by
  sorry

/-- The retained pair consisting of the explicit ordinary source and canonical iso.
Source: main-20261015, bounded etale-origin paragraph
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def sourceWitness
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    Scheme.FixedEtaleOriginWitness (AffineSpace PUnit.{u + 1} Y)
      (Scheme.finiteTateCoefficient l E n)
      ⟨source l E n Y r hA K, source_plus l E n Y r hA K Ke hKe eK⟩ where
  complex := ⟨etaleSource l E n Y r hA Ke, etaleSource_plus l E n Y r hA Ke hKe⟩
  iso := sourceComparison l E n Y r hA K Ke eK


end AlgebraicGeometry.ProEtale.AffineLinePurity
