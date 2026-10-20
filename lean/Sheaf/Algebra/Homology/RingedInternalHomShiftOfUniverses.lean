/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.DerivedInternalHomShiftLeft
import Sheaf.Algebra.Homology.DerivedInternalHomShiftRight
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.HomComplexMappingCone
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Normalized internal-Hom shifts with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 08JA and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
The existing restriction and signed small-site interfaces are reexported. The
normalizations below use the very same Hom complex, its fixed product projections,
and its fixed augmentation to the K-injective localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The recorded modules, retaining both site universes.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev Modules := SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- The recorded cochain category.
Source: Stacks 0A8X (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev Complex := CochainComplex (Modules.{c, v, r} J R) ℤ

/-- The recorded Hom complex, without a second construction.
Source: Stacks 0A8X (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev complexHom (L F : Complex.{c, v, r} J R) :=
  homComplex.{c, v, max c v r, max c v r} (R := R) L F

/-- Unsigned target reindexing, specified on every Hom-product projection.
Source: Stacks 0A8X (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def RightFormula (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e : (complexHom.{c, v, r} J R L F)⟦s⟧ ≅ complexHom.{c, v, r} J R L (F⟦s⟧)) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q),
    e.hom.f k ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R L (F⟦s⟧) k p q h =
      WeilConjectures.coefficientHomComponent.{r, c, v} J R L F (k + s) p (q + s)
        (by omega) ≫ SheafOfModules.homObjMap (R := R) (𝟙 (L.X p))
          (F.shiftFunctorObjXIso s q (q + s) rfl).inv

/-- Signed source reindexing: in Hom degree k multiply the reindexed family
by (-1)^(s*k). Source: Stacks 0A8X
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def LeftFormula (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅ complexHom.{c, v, r} J R (L⟦s⟧) F) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q),
    e.hom.f k ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R (L⟦s⟧) F k p q h =
      (s * k).negOnePow •
        (WeilConjectures.coefficientHomComponent.{r, c, v} J R L F (k + -s) (p + s) q
          (by omega) ≫ SheafOfModules.homObjMap (R := R)
            (L.shiftFunctorObjXIso s p (p + s) rfl).hom (𝟙 (F.X q)))

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- The existing ambient derived category.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev D := DerivedCategory (Modules.{c, v, r} J R)

/-- The recorded derived internal Hom with its source fixed.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev hom (M : D.{c, v, r, w} J R) : D.{c, v, r, w} J R ⥤ D.{c, v, r, w} J R :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op M)

/-- The right shift structure agrees, through the fixed ordinary-to-derived
comparison, with unsigned target reindexing. This pins the shift signs, rather
than choosing an arbitrary shift structure.
Source: Stacks 08JA, 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def RightNormalization
    (S : ∀ M : D.{c, v, r, w} J R, (hom.{c, v, r, w} J R M).CommShift ℤ) : Prop :=
  ∀ (M : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
    (eM : DerivedCategory.Q.obj L ≅ M) (s : ℤ),
    letI := S M
    ∃ e : (complexHom.{c, v, r} J R L F)⟦s⟧ ≅ complexHom.{c, v, r} J R L (F⟦s⟧),
      RightFormula.{c, v, r} J R L F s e ∧
      DerivedCategory.Q.map e.hom ≫
          ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L (F⟦s⟧) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom eM.inv.op ((DerivedCategory.Q.commShiftIso s).hom.app F)) ≫
          ((hom.{c, v, r, w} J R M).commShiftIso s).hom.app
            (DerivedCategory.Q.obj F) =
        (DerivedCategory.Q.commShiftIso s).hom.app (complexHom.{c, v, r} J R L F) ≫
          (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
              (Prod.mkHom eM.inv.op (𝟙 _)))⟦s⟧'

/-- Existence and uniqueness of the ordinary normalized right shift structure.
Source: Stacks 08JA, 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: product projections define the unsigned reindexing chain isomorphism.
The shifted Hom differential and Hom into the shifted target agree. Its naturality
commutes with the fixed K-injective augmentation. Localize this identity; on
K-injective targets the augmentation comparison is invertible. Essential
surjectivity and the localization universal property give a unique natural shift
structure on every derived object. The degreewise reindexings compose and are the
identity at zero, so they satisfy the CommShift coherence identities. -/
theorem rightShift_existsUnique :
    ∃! S : ∀ M : D.{c, v, r, w} J R, (hom.{c, v, r, w} J R M).CommShift ℤ,
      RightNormalization.{c, v, r, w} J R S := by
  sorry

/-- The uniquely normalized shift of the recorded Hom functor.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
instance homCommShift (M : D.{c, v, r, w} J R) : (hom.{c, v, r, w} J R M).CommShift ℤ :=
  (rightShift_existsUnique.{c, v, r, w} J R).exists.choose M

/-- Normalization of the signed source-shift family against the fixed
ordinary-to-derived Hom comparison.
Source: Stacks 0A8X, 08JA
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def LeftNormalization
    (S : ∀ (M : D.{c, v, r, w} J R) (s : ℤ),
      hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅ hom.{c, v, r, w} J R (M⟦s⟧)) : Prop :=
  ∀ (M : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
    (eM : DerivedCategory.Q.obj L ≅ M) (s : ℤ),
    ∃ e : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅ complexHom.{c, v, r} J R (L⟦s⟧) F,
      LeftFormula.{c, v, r} J R L F s e ∧
      (DerivedCategory.Q.commShiftIso (-s)).hom.app (complexHom.{c, v, r} J R L F) ≫
          (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
              (Prod.mkHom eM.inv.op (𝟙 _)))⟦-s⟧' ≫
          (S M s).hom.app (DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map e.hom ≫
          ringedSiteOrdinaryHomComparison.{c, v, r, w} J R (L⟦s⟧) F ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (((shiftFunctor _ s).map eM.inv) ≫
              (DerivedCategory.Q.commShiftIso s).inv.app L).op (𝟙 _))

/-- The uniquely specified signed source shift.
Source: Stacks 0A8X, 08JA
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: in degree k reindex p to p+s and multiply by (-1)^(s*k).
The ratio between consecutive degrees is (-1)^s, exactly compensating for
the shifted source differential. The inverse reindexes backwards with the same
sign. Projectionwise equality gives naturality and uniqueness. Localize the
chain isomorphism through the fixed K-injective augmentation; K-injective targets
and essential surjectivity determine the unique derived natural isomorphism. -/
theorem leftShift_existsUnique :
    ∃! S : ∀ (M : D.{c, v, r, w} J R) (s : ℤ),
      hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅ hom.{c, v, r, w} J R (M⟦s⟧),
      LeftNormalization.{c, v, r, w} J R S := by
  sorry

/-- The signed source shift selected by its full representative normalization.
Source: Stacks 08JA (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def sourceShift (M : D.{c, v, r, w} J R) (s : ℤ) :
    hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅ hom.{c, v, r, w} J R (M⟦s⟧) :=
  (leftShift_existsUnique.{c, v, r, w} J R).exists.choose M s

/-- Exactness for the normalized target shift at independent site universes.
Source: Stacks 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: represent a target triangle by a cone of a map of K-injective complexes.
The cone is K-injective, since Hom from an acyclic test complex takes it to a
cone of acyclic complexes. Hom(L,Cone(f)) is the cone of Hom(L,f), with its
inclusion, projection and connecting arrow. The right-shift normalization above
fixes the connecting-arrow sign. Localize and use the ordinary representative
comparison. Independence of K-injective representatives and TR3 transfer the
result to every distinguished triangle. No boundedness assumption is used. -/
theorem hom_isTriangulated (M : D.{c, v, r, w} J R) : (hom.{c, v, r, w} J R M).IsTriangulated := by
  sorry

end CategoryTheory.RingedHomUniverses
