/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact

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

/-- The ambient Verdier-duality conclusion for a fixed dualizing object and
subcategory predicate. Keeping the coefficient category abstract fixes the native
closed structure before any finite coefficient specialization.
Source: blueprint order 2136 (blueprint: def-sf-finite-verdier-biduality-predicate). -/
noncomputable def VerdierBidualityOn
    (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  IsExactAntiEquivalenceOn P (MonoidalClosed.internalHom.flip.obj W) ∧
    HasInvertibleBidualityOn A X W P

end AlgebraicGeometry.ProEtale

namespace WeilConjectures

open AlgebraicGeometry

-- Match the generic duality functors before specializing their coefficient category.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

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
  ProEtale.VerdierBidualityOn
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y
    ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
      (NagataCompactification aY)).obj (𝟙_ _))
    (finiteTorConstructibleProEtaleModule l E n hn Y)

private theorem proEtaleFiniteTor_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u})
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))}
    (e : K ≅ L) (hK : finiteTorConstructibleProEtaleModule l E n hn Y K) :
    finiteTorConstructibleProEtaleModule l E n hn Y L := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let F := (ProEtale.finiteCoefficientIntrinsicRealization Y
    (Padic.coefficientExtensionRing l E n)).mapDerivedCategory
  change finiteTorConstructible l E n hn Y (F.obj L)
  change finiteTorConstructible l E n hn Y (F.obj K) at hK
  refine ⟨?_, ?_⟩
  · exact (Scheme.finiteTorsionConstructible D l hl E n hn Y).prop_of_iso
      (F.mapIso e) hK.1
  · obtain ⟨a, b, hab, ht⟩ := hK.2
    refine ⟨a, b, hab, ?_⟩
    intro M P he f hf hP N i hi
    exact ht M P (he.map (fun j ↦ j ≪≫ (F.mapIso e).symm)) f hf hP N i hi

private theorem exactAntiEquivalenceOn_of_comparison
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (V : Cᵒᵖ ⥤ C)
    (hP : ∀ {K L : C}, (K ≅ L) → P K → P L)
    (e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory)
    (c : e.functor ⋙ P.ι ≅ P.ι.op ⋙ V)
    (hex : ∃ s : V.CommShift ℤ, letI := s; V.IsTriangulated) :
    IsExactAntiEquivalenceOn P V := by
  refine ⟨?_, ⟨e, ⟨c⟩⟩, ?_⟩
  · intro K hK
    exact hP (c.app (op ⟨K, hK⟩)) (e.functor.obj (op ⟨K, hK⟩)).property
  · obtain ⟨s, hs⟩ := hex
    let := s
    have : V.IsTriangulated := hs
    exact ⟨s, fun T _ _ _ hT ↦ V.map_distinguished T hT⟩

private theorem proEtaleConclusion_of_comparison
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (w : (ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj W ⟶ W')
    (Pet Qet : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (hP : ∀ {K L}, (K ≅ L) → P K → P L)
    (hc : ProEtale.FiniteDualityComparisonData A X W W' w Pet Qet P) :
    ProEtale.VerdierBidualityOn A X W' P := by
  obtain ⟨ω, _, hEt, hPro, _, _, ⟨d, ⟨c⟩⟩, hδ⟩ := hc.transport
  refine ⟨?_, hPro, ?_⟩
  · exact exactAntiEquivalenceOn_of_comparison P
      (MonoidalClosed.internalHom.flip.obj W') hP d c
      (_root_.DerivedCategory.nativeInternalHom_contravariant_exact
        (Sheaf (Scheme.ProEt.topology X) A) W')
  · intro K hK
    rw [(ProEtale.pairing_normalized A X W' hPro K).2]
    exact hδ K hK

private theorem finiteDualityProEtaleObject_eq
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    ProEtale.finiteDualityProEtaleObject A c =
      (ProEtale.sfFiniteExceptionalFixed A c).obj (𝟙_ _) := rfl

private theorem fixedProEtaleConclusion
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a)
    (Pet Qet : ObjectProperty (_root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))))
    (P : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))))
    (hP : ∀ {K L}, (K ≅ L) → P K → P L)
    (hc : letI := ProEtale.preservesFlat_comparisonUpperStar (X := X) (Λ := ULift.{u + 1, u} A)
      ProEtale.FiniteDualityComparisonData (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
        (ProEtale.finiteDualityEtaleObject A c) (ProEtale.finiteDualityProEtaleObject A c)
        (ProEtale.finiteDualityObjectMap A c) Pet Qet P) :
    ProEtale.VerdierBidualityOn (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
      ((ProEtale.sfFiniteExceptionalFixed A c).obj (𝟙_ _)) P := by
  let := ProEtale.preservesFlat_comparisonUpperStar (X := X) (Λ := ULift.{u + 1, u} A)
  apply (congrArg (fun W ↦ ProEtale.VerdierBidualityOn
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X W P)
    (finiteDualityProEtaleObject_eq A c)).mp
  exact proEtaleConclusion_of_comparison
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
    (ProEtale.finiteDualityEtaleObject A c) (ProEtale.finiteDualityProEtaleObject A c)
    (ProEtale.finiteDualityObjectMap A c) Pet Qet P hP hc

/-- Finite-stage Verdier duality is an exact anti-equivalence, with invertible
canonical double-dual map, on both small sites. No boundary-duality input is assumed.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2136
(blueprint: thm-fix-general-biduality).

Proof:
1. Apply thm-weil-etale-geometric-biduality to obtain the etale conclusion.
2. Specialize lem-weil-finite-duality-site-comparison to the given structural
   morphism. Its last clauses already give the restricted pro-etale
   anti-equivalence with the specified ambient internal Hom and invertibility
   of the canonical evaluation transpose, with its original pairing witness.
3. The finite-Tor constructible predicate is invariant under isomorphism:
   constructibility transports through the intrinsic realization, and the Tor
   interval is retained by composing each representative isomorphism.
   The inclusion comparison of the restricted anti-equivalence therefore proves
   that the ambient dual functor preserves this predicate.
4. Apply lem-weil-native-internal-hom-contravariant-exact to the fixed pro-etale
   dualizing object. Its shift comparison and map_distinguished give exactly
   the ambient triangle clause of IsExactAntiEquivalenceOn.
5. Rewrite the dualizing-object abbreviation by its defining equality before
   combining the clauses, avoiding expansion of the native internal Hom.
-/
theorem finite_stage_verdier_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    FiniteEtaleGeometricBiduality l E n hn Y aY ∧
      FiniteProEtaleVerdierBiduality l E n hn Y aY := by
  refine ⟨finite_stage_etale_geometric_biduality D l _hl E n hn Y aY, ?_⟩
  let : Y.Over (Spec (.of D.k)) := ⟨aY⟩
  have : IsSeparated (Y ↘ Spec (.of D.k)) := ‹IsSeparated aY›
  have : LocallyOfFiniteType (Y ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Y ↘ Spec (.of D.k)) := ‹QuasiCompact aY›
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have hc := finite_duality_site_comparison D l _hl E n hn Y
  dsimp only [FiniteDualitySiteComparison] at hc
  simp only [CategoryTheory.over] at hc
  exact fixedProEtaleConclusion (Padic.coefficientExtensionRing l E n)
    (NagataCompactification aY) (finiteTorConstructibleEtale l E n hn Y)
    (Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y)
    (finiteTorConstructibleProEtaleModule l E n hn Y)
    (fun e hK ↦ proEtaleFiniteTor_iso D l _hl E n hn Y e hK)
    hc

end WeilConjectures
