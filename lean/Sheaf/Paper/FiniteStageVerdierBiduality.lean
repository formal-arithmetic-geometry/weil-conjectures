/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.DualityPairing
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Paper.EtaleGeometricBiduality
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-! # Finite-stage Verdier biduality on both small sites

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2136 (blueprint: thm-fix-general-biduality).

The conclusion records the restriction of the specified ambient Verdier functor,
its exactness on the full finite-Tor constructible subcategory, and invertibility of
the evaluation transpose. In particular it does not substitute an unspecified
isomorphism to the double dual. Pro-etale exceptional inverse image is the existing
comparison composite, without an ambient pro-etale adjoint or boundary-duality datum.
-/

@[expose] public section

set_option autoImplicit false

universe v u a

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- A specified contravariant functor restricts to an exact anti-equivalence on the
full subcategory cut out by P. Exactness is expressed using its ambient distinguished
triangles, so it does not require a second choice of triangulated structure on that
full subcategory. The natural comparison fixes both objects and maps of the restriction.
Source: blueprint order 2136 (blueprint: thm-fix-general-biduality). -/
def IsExactAntiEquivalenceOn {C : Type u} [Category.{v} C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (D : Cᵒᵖ ⥤ C) : Prop :=
  (∀ K : C, P K → P (D.obj (op K))) ∧
    (∃ e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory,
      Nonempty (e.functor ⋙ P.ι ≅ P.ι.op ⋙ D)) ∧
    ∃ s : D.CommShift ℤ, ∀ T : Triangle Cᵒᵖ,
      P T.obj₁.unop → P T.obj₂.unop → P T.obj₃.unop → T ∈ distTriang Cᵒᵖ →
      Triangle.mk (D.map T.mor₁) (D.map T.mor₂)
        (D.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈ distTriang C

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

/-- The canonical pro-etale evaluation transpose is invertible on the indicated objects.
The pairing witness fixes its value by symmetry and the tensor-Hom adjunction.
Source: Stacks Project, Tags 08J9 and 08JA (blueprint: thm-fix-general-biduality). -/
noncomputable def HasInvertibleBidualityOn
    (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  ∃ h : AmbientDualityPairing A X W,
    ∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
      P K → IsIso (AmbientDualityPairing.bidualityMap A X (W := W) h K)

end AlgebraicGeometry.ProEtale

namespace WeilConjectures

open AlgebraicGeometry

/-- The pro-etale finite-stage conclusion, in the equivalent fixed-scalar sheaf
presentation of the same intrinsic `Dᵇ_ctf`. The dualizing object uses
`Rν_* ⋙ aY^× ⋙ ν^*`, exactly the recorded exceptional inverse-image construction.
The canonical evaluation transpose, rather than an arbitrary isomorphism, is invertible.
Source: blueprint order 2136 (blueprint: thm-fix-general-biduality). -/
noncomputable def FiniteProEtaleVerdierBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  IsExactAntiEquivalenceOn (finiteTorConstructibleProEtaleModule l E n hn Y)
    (MonoidalClosed.internalHom.flip.obj
      ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
        (NagataCompactification aY)).obj (𝟙_ _))) ∧
  ProEtale.HasInvertibleBidualityOn
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y
    ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
      (NagataCompactification aY)).obj (𝟙_ _))
    (finiteTorConstructibleProEtaleModule l E n hn Y)

/-- Finite-stage Verdier duality is an exact anti-equivalence, with invertible
canonical double-dual map, on both small sites. No boundary-duality input is assumed.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2136
(blueprint: thm-fix-general-biduality).

Proof:
1. Work at the positive level n, with l different from the characteristic of k.
   Etale preservation (lem-weil-verdier-preservation-strata) applies to K and to
   the constant rank-one sheaf. Thus the etale dualizing complex is bounded
   constructible and finite-Tor. Etale geometric biduality
   (thm-weil-etale-geometric-biduality) gives the exact anti-equivalence and the
   canonical double-dual isomorphism.
2. By lem-sf-proetale-constructible-origin, every bounded constructible pro-etale
   K has a bounded constructible etale representative K'. The reflection and
   preservation clauses of lem-sf-comparison-tor-amplitude give precisely an
   equivalence on the two finite-Tor constructible subcategories.
3. Apply lem-weil-finite-duality-site-comparison to K' and to the etale dualizing
   object, then again to its etale dual. The dualizing-object comparison gives
   c_K' : ν* D_et K' ≅ D_proet ν* K'. Preservation of finite Tor amplitude
   therefore shows that D_proet preserves the same full subcategory.
4. Evaluation and transpose compatibility identifies the pro-etale double-dual
   arrow with ν*(δ_K') followed by c_(D_et K') and D_proet(c_K'^(-1)). Every
   factor is invertible. Naturality transports this to any K isomorphic to ν*K'.
5. The same comparison transports the etale exact contravariant anti-equivalence
   to the specified pro-etale Verdier functor. Its exceptional inverse image is
   the comparison composite; no ambient pro-etale adjoint is used.
-/
theorem finite_stage_verdier_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    FiniteEtaleGeometricBiduality l E n hn Y aY ∧
      FiniteProEtaleVerdierBiduality l E n hn Y aY := by
  sorry

end WeilConjectures
