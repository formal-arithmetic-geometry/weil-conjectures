/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.RingTheory.CotangentSquareConstructions
import Sheaf.RingTheory.CotangentTransitivityTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.TraceFormula.OnePointDerivedRingIdentification
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Cotangent comparison for squares with zero relative complexes

Source: Stacks Project, cotangent.tex, Tags 08QS, 08R3 and 08SF;
more-algebra.tex, Tags 06XZ and 06Y6; sites-cohomology.tex, Tags 07A6 and 0D6D
(blueprint: lem-trf-cotangent-zero-relative-square).

The comparison is the existing normalized `cotangentBaseChange`. Its chain
representative is the ordinary tensor adjunct of the standard square map.
The tensor convention puts the scalar first: `c ⊗ x` denotes the paper's `x ⊗ c`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]

/-- Termwise scalar extension, using the additive structure of its canonical
adjunction. Source: Stacks, Tag 06Y6
(blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeTensorFunctor {B B' : CommRingCat.{u}} (b : B ⟶ B') :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} b.hom).left_adjoint_additive
  (ModuleCat.extendScalars b.hom).mapHomologicalComplex (.up ℤ)

/-- The canonical chain map `B' ⊗_B Lstd[B/A] → Lstd[B'/A']`.
Source: Stacks, Tag 08QL (blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeChainMap (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    SquareData.transitivityFirstComplex C f.hom q.right ⟶ SquareData.standardComplex C g :=
  ((SquareData.tensorComplexAdj q.right).homEquiv _ _).symm (SquareData.standardComplexMap C q)

/-- Canonical derived-to-ordinary scalar extension, the derived adjunct of the
localized ordinary scalar-extension unit. Thus no computation isomorphism or
adjunction is chosen arbitrarily. Source: Stacks, Tags 06Y6 and 07A6
(blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeTensorComparison {B B' : CommRingCat.{u}} (b : B ⟶ B')
    (K : CochainComplex (ModuleCat.{u} B) ℤ) :
    (SquareData.baseChangeExtension b).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((zeroRelativeTensorFunctor b).obj K) :=
  ((SquareData.baseChangeAdjunction b).homEquiv _ _).symm
    (DerivedCategory.Q.map ((SquareData.tensorComplexAdj b).unit.app K) ≫
      (ModuleCat.restrictScalars b.hom).mapDerivedCategoryFactors.inv.app
        ((zeroRelativeTensorFunctor b).obj K))

/-- The canonical derived tensor associator, obtained by uniqueness of left
adjoints from the identity-on-elements composition of scalar restrictions.
Source: Stacks, Tag 0D6D (blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeDerivedAssoc {B B' B'' : CommRingCat.{u}}
    (b : B ⟶ B') (c : B' ⟶ B'') :
    SquareData.baseChangeExtension b ⋙ SquareData.baseChangeExtension c ≅
      SquareData.baseChangeExtension (b ≫ c) :=
  (((SquareData.baseChangeAdjunction b).comp (SquareData.baseChangeAdjunction c)).ofNatIsoRight
    ((Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars c.hom)
        (ModuleCat.restrictScalars b.hom)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp b.hom c.hom).symm)
    ).leftAdjointUniq (SquareData.baseChangeAdjunction (b ≫ c))

/-- The canonical identity scalar-extension identification, with its normalized
adjunction unit. Source: Stacks, Tag 07A6
(blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeDerivedId (B : CommRingCat.{u}) :
    SquareData.baseChangeExtension (𝟙 B) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} B)) :=
  ((SquareData.baseChangeAdjunction (𝟙 B)).ofNatIsoRight
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId B) ≪≫
      Functor.mapDerivedCategoryIdIso (ModuleCat.{u} B))).leftAdjointUniq Adjunction.id

/-- Termwise tensor associativity, scalar first: `d ⊗ (c ⊗ x) ↦ b'(c)d ⊗ x`.
Source: Stacks, Tags 0D6D and 08QL
(blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeOrdinaryAssoc {B B' B'' : CommRingCat.{u}}
    (b : B ⟶ B') (c : B' ⟶ B'') :
    (zeroRelativeTensorFunctor b) ⋙ (zeroRelativeTensorFunctor c) ≅
      (zeroRelativeTensorFunctor (b ≫ c)) :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} b.hom).left_adjoint_additive
  letI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} c.hom).left_adjoint_additive
  letI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (b ≫ c).hom).left_adjoint_additive
  Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp b.hom c.hom).symm (.up ℤ)

/-- The composite of the first and second transitivity arrows, transporting the
middle object along the commuting-square equality. Source: Stacks, Tags 08QS and 08SF
(blueprint: lem-trf-cotangent-zero-relative-square). -/
def zeroRelativeTransitivityComposite (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    DerivedCategory.Q.obj (SquareData.transitivityFirstComplex C f.hom q.right) ⟶
      cotangentComplex C g :=
  SquareData.transitivityFirstMap C f.hom q.right ≫
    eqToHom (by rw [q.w]) ≫ SquareData.transitivitySecondMap C q.left g.hom

/-- Every clause of the canonical zero-relative-square comparison, including
its specified transitivity factorization, composition, identities, and flat
ordinary representatives. Source: Stacks, Tags 08QS, 08R3, 08SF, 06XZ and 06Y6
(blueprint: lem-trf-cotangent-zero-relative-square). -/
structure ZeroRelativeSquareComparisons (C : Coherence.{u}) : Prop where
  /-- No pushout hypothesis: only the two stated relative vanishings. -/
  invertible : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    IsZero (cotangentComplex C (Arrow.mk q.left)) →
    IsZero (cotangentComplex C (Arrow.mk q.right)) → IsIso (SquareData.cotangentBaseChange C q)
  /-- The standard chain map computes the actual normalized adjunct. -/
  representative : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    zeroRelativeTensorComparison q.right (SquareData.standardComplex C f) ≫
      DerivedCategory.Q.map (zeroRelativeChainMap C q) = SquareData.cotangentBaseChange C q
  /-- The two specified standard transitivity arrows give precisely this map. -/
  transitivity : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    SquareData.cotangentBaseChange C q =
      zeroRelativeTensorComparison q.right (SquareData.standardComplex C f) ≫
      zeroRelativeTransitivityComposite C q
  /-- Comparison for successive zero-relative squares, under the derived associator. -/
  composition : ∀ {f g h : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ h),
    IsZero (cotangentComplex C (Arrow.mk q.left)) →
    IsZero (cotangentComplex C (Arrow.mk q.right)) →
    IsZero (cotangentComplex C (Arrow.mk r.left)) →
    IsZero (cotangentComplex C (Arrow.mk r.right)) →
    (zeroRelativeDerivedAssoc q.right r.right).hom.app (cotangentComplex C f) ≫
        SquareData.cotangentBaseChange C (q ≫ r) =
      (SquareData.baseChangeExtension r.right).map (SquareData.cotangentBaseChange C q) ≫
        SquareData.cotangentBaseChange C r
  /-- Identity square, under the identity extension identification. -/
  identity : ∀ f : Arrow CommRingCat.{u},
    SquareData.cotangentBaseChange C (𝟙 f) =
      (zeroRelativeDerivedId f.right).hom.app (cotangentComplex C f)
  /-- Flat coefficients in degree zero are K-flat, for the recorded predicate. -/
  flat_kFlat : ∀ {B B' : CommRingCat.{u}} (b : B ⟶ B'), b.hom.Flat →
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars b.hom).obj (ModuleCat.of B' B')))
  /-- The canonical computation works for every unbounded complex. -/
  flat_computation : ∀ {B B' : CommRingCat.{u}} (b : B ⟶ B'), b.hom.Flat →
    ∀ K : CochainComplex (ModuleCat.{u} B) ℤ, IsIso (zeroRelativeTensorComparison b K)
  /-- The specified chain map is a quasi-isomorphism under the hypotheses. -/
  flat_quasiIso : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    IsZero (cotangentComplex C (Arrow.mk q.left)) →
    IsZero (cotangentComplex C (Arrow.mk q.right)) → q.right.hom.Flat →
    QuasiIso (zeroRelativeChainMap C q)
  /-- Successive flat chain comparisons compose under the ordinary tensor associator. -/
  flat_composition : ∀ {f g h : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ h),
    IsZero (cotangentComplex C (Arrow.mk q.left)) →
    IsZero (cotangentComplex C (Arrow.mk q.right)) →
    IsZero (cotangentComplex C (Arrow.mk r.left)) →
    IsZero (cotangentComplex C (Arrow.mk r.right)) →
    q.right.hom.Flat → r.right.hom.Flat →
    (zeroRelativeOrdinaryAssoc q.right r.right).hom.app (SquareData.standardComplex C f) ≫
        zeroRelativeChainMap C (q ≫ r) =
      (zeroRelativeTensorFunctor r.right).map (zeroRelativeChainMap C q) ≫ zeroRelativeChainMap C r
  /-- The ordinary associator represents the same derived associator. -/
  flat_associator : ∀ {f g h : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ h),
    q.right.hom.Flat → r.right.hom.Flat →
    (zeroRelativeDerivedAssoc q.right r.right).hom.app (cotangentComplex C f) ≫
        zeroRelativeTensorComparison (q.right ≫ r.right) (SquareData.standardComplex C f) =
      (SquareData.baseChangeExtension r.right).map
          (zeroRelativeTensorComparison q.right (SquareData.standardComplex C f)) ≫
        zeroRelativeTensorComparison r.right
          ((zeroRelativeTensorFunctor q.right).obj (SquareData.standardComplex C f)) ≫
        DerivedCategory.Q.map
          ((zeroRelativeOrdinaryAssoc q.right r.right).hom.app (SquareData.standardComplex C f))

/-- The full canonical comparison theorem for zero-relative squares.
Source: Stacks Project, cotangent.tex, Tags 08QS, 08R3 and 08SF
(blueprint: lem-trf-cotangent-zero-relative-square).

Proof:
1. The standard complexes have free terms by the polynomial Kähler basis
lemma and vanish in positive degrees. The bounded-flat K-flat lemma makes them
K-flat. The normalized coefficient adjunction, transported from the singleton
site, identifies the adjunct of the standard square map with Q of its tensor
adjunct after the canonical computation map. This gives representative.
2. Apply the transitivity triangle to A → B → B'. Its third object vanishes,
so the distinguished-cone-zero lemma makes its first standard arrow invertible.
3. Apply the triangle to A → A' → B'. Its first object is zero because derived
scalar extension preserves zero. Rotate and apply the same cone-zero lemma to
its second standard arrow. Standard square composition and adjunction naturality
identify their composite with cotangentBaseChange, proving transitivity and
invertible without a tensor-pushout hypothesis.
4. For successive squares, the composite-unit normalization of derived scalar
extension and adjunction naturality identify the adjunct of the composite with
the composite of standard square maps. Strict standard coherence and bijectivity
of adjunction prove composition. The identity square similarly gives identity.
The composite relative complexes vanish by their own transitivity triangles.
5. For flat B → B', tensor preserves the cycle and boundary exact sequences,
so it preserves acyclicity and all quasi-isomorphisms. This proves flat_kFlat.
For arbitrary unbounded K, take a flat-term K-flat resolution P → K. Naturality
of the canonical computation map and its invertibility on P show that it is
invertible on K as well; this is flat_computation.
6. The map in representative is the canonical tensor adjunct of the standard
chain map. Both the derived comparison and its computation map are invertible
under the hypotheses, so Q of that chain map is invertible. Cohomology factors
through Q, proving flat_quasiIso.
7. For successive squares, on pure tensors d ⊗ (c ⊗ x) the composite chain map
has value b'(c)d γ'γ(x). Strict standard coherence identifies this with the
composite-square map after the ordinary associator. Pure tensors generate, so
the maps agree. Normalized units and computation maps identify this ordinary
associator with zeroRelativeDerivedAssoc, giving flat_associator and showing
that flat_composition localizes to exactly composition. -/
theorem zeroRelativeSquareComparison (C : Coherence.{u}) : ZeroRelativeSquareComparisons C := by
  sorry

end Algebra.CotangentResolution
