module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import Sheaf.Paper.FiniteFreeHomLocalCalculation
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import Sheaf.Paper.FiniteHomDomainCalculus
import Sheaf.Paper.FiniteConstructibleHom
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.EtaleFiniteFreeHomLocalIdentity
import Sheaf.Paper.EtalePerfectHomRestriction
import Sheaf.Paper.EtaleLisseCanonicalIso
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.OpenComplement
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import Sheaf.Paper.FiniteCoefficientFlatModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Lisse stratum Hom and finite coefficient reduction

Source: blueprint thm-coef-finite-hom, proof paragraphs 2–3, expanded stratum argument
(blueprint: lem-coef-etale-lisse-hom-reduction).
The indices n,m stand for the positive exponents n+1,m+1. All objects lie in the
ordinary unbounded derived category on the small etale site. The comparison is the
published evaluation transpose. Its coordinates below are defined by evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option linter.privateModule false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local instance] lisseHomModuleDerivedCategory

attribute [local implicit_reducible] finiteHomEtaleCategory

private theorem finiteFreeIso (R : Type v) [Ring R] (V : ModuleCat.{v} R)
    [Module.Finite R V] [Module.Free R V] :
    ∃ t : ℕ, Nonempty (V ≅ ModuleCat.of R (Fin t → R)) := by
  classical
  let b := Module.Free.chooseBasis R V
  let e := Fintype.equivFin (Module.Free.ChooseBasisIndex R V)
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex R V),
    ⟨(b.reindex e).equivFun.toModuleIso⟩⟩

private theorem coefficientIntegers_local (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsLocalRing (Padic.coefficientExtensionIntegers l E) := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  exact h.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_prime_pow_zero (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    (l : Padic.coefficientExtensionRing l E n) ^ n = 0 := by
  change Ideal.Quotient.mk _ ((l : Padic.coefficientExtensionIntegers l E) ^ n) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := by
    simpa only [Padic.coefficientExtensionUniformizer,
      Padic.coefficientExtensionMaximalIdeal, Padic.coefficientExtensionIntegers] using
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rw [Padic.coefficientExtensionIdeal, hgen]
  apply Ideal.pow_mem_pow
  have hm : ∀ x : Padic.coefficientExtensionIntegers l E,
      x ∈ Padic.coefficientExtensionMaximalIdeal l E ↔
        Padic.coefficientExtensionAbsoluteValue l E (x : E) < 1 := by
    simpa only [Padic.coefficientExtensionMaximalIdeal,
      Padic.coefficientExtensionIntegers] using h.2.1
  apply (hm _).mpr
  change spectralNorm (Padic l) E (l : E) < 1
  rw [← map_natCast (algebraMap (Padic l) E), spectralNorm_extends]
  exact Padic.norm_p_lt_one

/-- Finiteness of the lifted positive coefficient ring, from the recorded quotient theorem.
Source: finite coefficient convention (blueprint: lem-coef-etale-lisse-hom-reduction). -/
instance lisseHomPositiveCoefficientFinite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) : Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) :=
  @Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))) Equiv.ulift.symm

/-- Endpoint boundedness and Tor-amplitude assertions used for the coefficient Hom reduction.
Source: cor-weil-finite-constructible-hom and finite-domain endpoint calculus.
(blueprint: lem-coef-etale-lisse-hom-endpoint-bounds)
The space `S` is separated of finite type over the fixed algebraically closed field and the
dimension parameter `dS` is a natural number.
Proof: the bounded constructible Hom theorem, applied with the widened interval
`[min a (b+2dX+1), b+2dX+1]` of `N`, gives the constructibility of `Q`. The first input is
dualizable of Tor interval `[0,0]`, so the dualizable Hom Tor estimate gives `Q` the
interval `[a, b+2dX+1]`, contained in `[a-2dS, b+2dX+1+2dS]` because `dS ≥ 0`. The finite
coefficient endpoint calculus gives the two reduced endpoints and their finite Tor
amplitudes. -/
theorem etaleLisseHomEndpointBounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (n m : ℕ) (hmn : m ≤ n)
    (S : Scheme.{u}) [S.Over (Spec (.of D.k))] [IsSeparated (S ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of D.k))] [QuasiCompact (S ↘ Spec (.of D.k))]
    (K N Q : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S)
    (hQ : Q = (finiteHomEtaleInternalHom l E S n).obj (op K, N))
    (hKbc : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S K)
    (hKtor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S 0 0 K)
    (hKdual : IsDualizable K)
    (hNbc : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S N)
    (a b dX : ℤ) (dS : ℕ)
    (hNtor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      a (b + 2 * dX + 1) N) :
    Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S Q ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
        (a - 2 * (dS : ℤ)) (b + 2 * dX + 1 + 2 * (dS : ℤ)) Q ∧
    Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))) S
        ((finiteHomEtaleReduction l E S hmn).obj Q) ∧
    Etale.DerivedCategory.finiteTorAmplitude
        (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) S
        ((finiteHomEtaleReduction l E S hmn).obj Q) ∧
    Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))) S
        ((finiteHomEtaleInternalHom l E S m).obj
          (op ((finiteHomEtaleReduction l E S hmn).obj K),
            (finiteHomEtaleReduction l E S hmn).obj N)) ∧
    Etale.DerivedCategory.finiteTorAmplitude
        (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) S
        ((finiteHomEtaleInternalHom l E S m).obj
          (op ((finiteHomEtaleReduction l E S hmn).obj K),
            (finiteHomEtaleReduction l E S hmn).obj N)) := by
  subst hQ
  have hKt := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hKtor
  have hNt := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hNtor
  have hNw := Etale.DerivedCategory.torAmplitudeIn.mono
    (min_le_left a (b + 2 * dX + 1)) le_rfl hNt
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (S ↘ Spec (.of D.k))
  have hH := finite_constructible_derivedHom_etale D l _hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) S d hd 0 0 _ _ le_rfl (min_le_right _ _)
    K N hKbc hNbc hKt hNw
  have hQt := Etale.torAmplitudeIn_derivedHom_of_isDualizable_aux _ hKt hKdual hNt
  have hE := finiteHomDomain_endpoints D l _hl E S hmn K N hKbc hNbc
    ⟨0, 0, le_rfl, hKtor⟩
    ⟨_, _, min_le_right _ _,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hNw⟩
  obtain ⟨⟨hsbc, c, e, -, hs⟩, ⟨htbc, c', e', -, ht⟩⟩ := hE
  refine ⟨hH.1, ?_, hsbc,
    ⟨c, e, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hs⟩, htbc,
    ⟨c', e', Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩⟩
  apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
  refine Etale.DerivedCategory.torAmplitudeIn.mono ?_ ?_ hQt <;> omega

attribute [local irreducible] _root_.DerivedCategory instCategoryDerivedCategory
attribute [local irreducible] Sheaf.monoidalCategory Sheaf.braidedCategory
  Sheaf.symmetricCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  _root_.DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
attribute [local irreducible] Functor.rightAdjoint Functor.leftAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Etale.rightDerivedUpperShriek Etale.rightDerivedLowerShriek
  Etale.upperStar Etale.lowerStar Etale.derivedHom _root_.DerivedCategory.monoidalClosed
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor
  Padic.coefficientExtensionAbsoluteValue Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal
  coefficientBaseChangeHom finiteHomEtaleData finiteHomEtaleClosed finiteHomEtaleTensor
  finiteHomEtaleClosedGeneral finiteHomEtaleRightAdjunctionGeneral finiteHomDerivedBraiding


/-- Closed support and open restriction with coefficient-independent instance data.
Source: the stratum convention (blueprint: lem-coef-etale-lisse-hom-reduction). -/
private def lisseHomStratumExceptionalRing (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z S : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) :
    Etale.DerivedCategoryModule A X ⥤ Etale.DerivedCategoryModule A S :=
  (R(Etale.lowerStar (ModuleCat.{u + 1} A) g)).rightAdjoint ⋙
    (Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- The closed-support adjoint followed by exact open restriction: s! = j* Rg!.
Source: stratum convention (blueprint: lem-coef-etale-lisse-hom-reduction). -/
def lisseHomStratumExceptional (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Z S : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) : finiteHomEtale l E X n ⥤ finiteHomEtale l E S n :=
  (R(Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) g)).rightAdjoint ⋙
    (Etale.upperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) j).mapDerivedCategory

attribute [local irreducible] lisseHomStratumExceptionalRing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The local model predicate evaluated on the published canonical comparison.
The equality witness fixes the arrow itself; it only delays comparison of two
definitionally equal closed-instance presentations. No arrow is chosen as data.
Source: finite-free local identity (blueprint: lem-coef-etale-lisse-hom-reduction). -/
def LisseHomLocalFreeCalculation (T : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K N : finiteHomEtale l E T n) : Prop :=
  ∃ v : LisseHomComparisonType
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
      (finiteHomQuotient l E h) T K N,
    HEq v (etaleFiniteHomCanonical l E T h K N) ∧
    LisseHomLocalFreeCalculationRing _ _ (finiteHomQuotient l E h) T K N v

/-- The local identity calculation on the actual restricted inputs.
Source: local etale models (blueprint: lem-coef-etale-lisse-hom-reduction). -/
def LisseHomRestrictedLocalFreeCalculation (T U : Scheme.{u}) (f : U ⟶ T)
    {n m : ℕ} (h : m ≤ n) (K N : finiteHomEtale l E T n) : Prop :=
  LisseHomLocalFreeCalculation l E U h
    ((lisseHomRestrictionFunctorRing
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) T U f).obj K)
    ((lisseHomRestrictionFunctorRing
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) T U f).obj N)

/-- The restriction square evaluated on the actual global and local canonical arrows.
Source: restriction compatibility (blueprint: lem-coef-etale-lisse-hom-reduction). -/
def LisseHomRestrictionCompatibility (T U : Scheme.{u}) (f : U ⟶ T)
    {n m : ℕ} (h : m ≤ n) (K N : finiteHomEtale l E T n) : Prop :=
  let R := lisseHomRestrictionFunctorRing
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) T U f
  ∃ (vT : LisseHomComparisonType
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
      (finiteHomQuotient l E h) T K N)
    (vU : LisseHomComparisonType
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
      (finiteHomQuotient l E h) U (R.obj K) (R.obj N)),
    HEq vT (etaleFiniteHomCanonical l E T h K N) ∧
    HEq vU (etaleFiniteHomCanonical l E U h (R.obj K) (R.obj N)) ∧
    LisseHomRestrictionCompatibilityRing _ _ (finiteHomQuotient l E h) T U f K N vT vU


attribute [local irreducible] lisseHomStratumExceptional

private theorem lisseBounded_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hb⟩
    refine ⟨(_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
      ⟨a, b, ?_, ?_⟩, ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hb q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hb q (.inr hq)
    · intro q
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨hb, hc⟩
    obtain ⟨a, b, ha, hb⟩ :=
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hb
    refine ⟨fun q ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc q), min a b, b, min_le_right _ _, ?_⟩
    intro q hq
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q hq

private theorem single_cover_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C' ⥤ D') (G : C ⥤ D) (s : C ⥤ C') (t : D ⥤ D')
    (ε : s ⋙ F ≅ G ⋙ t) (X : C) (Y : D) (e : G.obj X ≅ Y) :
    Nonempty (F.obj (s.obj X) ≅ t.obj Y) :=
  ⟨ε.app X ≪≫ t.mapIso e⟩

private theorem derived_free_cover (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (htriv : ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : V.I₀,
      ∃ r : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (V.f i)).obj L ≅
        (lisseHomConstantFunctor A (V.X i)).obj (ModuleCat.of A (Fin r → A)))) :
    ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : V.I₀,
      ∃ r : ℕ, Nonempty ((L(Etale.upperStar (ModuleCat.{u + 1} A) (V.f i))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((lisseHomConstantFunctor A (V.X i)).obj (ModuleCat.of A (Fin r → A)))) := by
  obtain ⟨V, hV⟩ := htriv
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := hV i
  exact ⟨r, single_cover_transport _ _ _ _
    (Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) (V.f i)) L _ e⟩


private theorem flat_of_free_cover (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (htriv : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).obj L ≅
        (lisseHomConstantFunctor A (U.X i)).obj (ModuleCat.of A (Fin t → A)))) :
    ObjectProperty.flat L := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨U, hU⟩ := htriv
  apply (Etale.flat_iff_forall_flat_sheafFiber_obj L).2
  intro Ω _ _ s
  obtain ⟨i, t, rfl⟩ := U.exists_comp_eq_of_isSepClosed s
  obtain ⟨r, ⟨e⟩⟩ := hU i
  let eS := ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} A)
    (U.f i) t).app L).symm ≪≫ (pointSmallEtale t).sheafFiber.mapIso e ≪≫
      (pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of A (Fin r → A))
  apply ObjectProperty.prop_of_iso _
    (((pointSmallEtale (t ≫ U.f i)).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} A)).symm.app L)
  exact ObjectProperty.prop_of_iso _ eS.symm
    ((ModuleCat.flat_iff_flat _).2 inferInstance)

private theorem single_terms_retract
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (X : C) (F : ℕ → C) (t : ℕ) (e : X ≅ F t) :
    ∀ q : ℤ, ∃ r : ℕ, Nonempty
      (Retract (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).X q) (F r)) := by
  intro q
  by_cases hq : q = 0
  · subst q
    exact ⟨t, ⟨Retract.ofIso ((HomologicalComplex.singleObjXSelf _ 0 X) ≪≫ e)⟩⟩
  · exact ⟨0, ⟨(HomologicalComplex.isZero_single_obj_X _ _ X q hq).retract (F 0)⟩⟩

private theorem single_projective_model
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : ℕ → C) (t : ℕ) :
    ∃ (P : CochainComplex C ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ q, ∃ r : ℕ, Nonempty (Retract (P.X q) (F r))) ∧
      Nonempty ((_root_.DerivedCategory.singleFunctor C 0).obj (F t) ≅
        _root_.DerivedCategory.Q.obj P) := by
  refine ⟨(HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (F t),
    0, 0, inferInstance, inferInstance, ?_, ?_⟩
  · exact single_terms_retract (F t) F t (Iso.refl _)
  · exact ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app (F t)⟩

private theorem nonempty_iso_trans {C : Type*} [Category C] {X Y Z : C}
    (e : Nonempty (X ≅ Y)) (f : Nonempty (Y ≅ Z)) : Nonempty (X ≅ Z) :=
  e.elim fun e ↦ f.elim fun f ↦ ⟨e ≪≫ f⟩

private theorem perfect_of_cover (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (htriv : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).obj L ≅
        (lisseHomConstantFunctor A (U.X i)).obj (ModuleCat.of A (Fin t → A)))) :
    Etale.DerivedCategory.IsSitePerfect
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) := by
  obtain ⟨U, hU⟩ := derived_free_cover A S L htriv
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨t, e⟩ := hU i
  obtain ⟨P, a, b, ha, hb, hp, hq⟩ := single_projective_model
    (fun r ↦ (lisseHomConstantFunctor A (U.X i)).obj
      (ModuleCat.of A (Fin r → A))) t
  exact ⟨P, a, b, ha, hb, hp, nonempty_iso_trans e hq⟩

private theorem lisse_bounds_of_cover (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (htriv : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).obj L ≅
        (lisseHomConstantFunctor A (U.X i)).obj
          (ModuleCat.of A (Fin t → A)))) :
    Etale.DerivedCategory.hasTorAmplitudeIn A S 0 0
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      Etale.DerivedCategory.isBoundedConstructible A S
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hflat : ObjectProperty.flat L := flat_of_free_cover A S L htriv
  have hLtor : Etale.DerivedCategory.hasTorAmplitudeIn A S 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (Etale.torAmplitudeIn_singleFunctor_zero_of_flat (ModuleCat.{u + 1} A) L hflat)
  refine ⟨hLtor, ?_⟩
  have hlc : IsLocallyConstantSheaf L := by
    obtain ⟨U, hU⟩ := htriv
    refine ⟨⟨⟨U, fun i ↦ ?_⟩⟩⟩
    apply (isConstant_over_iff_upperStar (ModuleCat.{u + 1} A) _ L).2
    obtain ⟨r, ⟨e⟩⟩ := hU i
    exact ⟨ModuleCat.of A (Fin r → A), ⟨e.symm⟩⟩
  have hfinite : IsFiniteSheaf L := by
    obtain ⟨U, hU⟩ := htriv
    have (i : U.I₀) : IsFiniteSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).obj L) := by
      obtain ⟨r, ⟨e⟩⟩ := hU i
      have : IsFiniteSheaf ((lisseHomConstantFunctor A (U.X i)).obj
          (ModuleCat.of A (Fin r → A))) := by
        unfold lisseHomConstantFunctor
        exact isFiniteSheaf_constantSheaf (X := U.X i) (ModuleCat.of A (Fin r → A))
      exact IsFiniteSheaf.of_iso e.symm
    exact IsFiniteSheaf.of_cover U L
  have hcons : IsConstructibleSheaf L :=
    IsFiniteLocallyConstantSheaf.isConstructibleSheaf
      { toIsLocallyConstantSheaf := hlc, toIsFiniteSheaf := hfinite }
  exact (lisseBounded_iff A S _).2
    (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj L 0)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def closed_adj_iso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] :
    Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g ≅
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) g)).rightAdjoint :=
  ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) g)).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) g)))

attribute [local irreducible] closed_adj_iso

private theorem closed_restrict_bounds (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z S : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (M : Etale.DerivedCategoryModule A X) (a b : ℤ)
    (h : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj M) ∧
      Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Z a b
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj M)) :
    Etale.DerivedCategory.isBoundedConstructible A S
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) g)).rightAdjoint.obj M)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A S a b
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) g)).rightAdjoint.obj M)) := by
  constructor
  · apply (lisseBounded_iff A S _).2
    exact ((Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z
      ).prop_of_iso ((closed_adj_iso A g).app M) h.1).mapDerivedCategory_upperStar j
  · apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    have hz := (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Z a b
      ).prop_of_iso ((closed_adj_iso A g).app M) h.2
    have hs := Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A) j _ _ hz
    exact (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) S a b).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).app _) hs

attribute [local irreducible] Etale.DerivedCategory.isBoundedConstructible
  Etale.DerivedCategory.hasTorAmplitudeIn Etale.DerivedCategory.IsSitePerfect

attribute [local irreducible] LisseHomLocalFreeCalculation
  LisseHomRestrictedLocalFreeCalculation LisseHomRestrictionCompatibility
  LisseHomLocalFreeCalculationRing LisseHomRestrictionCompatibilityRing
  LisseHomRestrictionSquare lisseHomSourceCoordinatesRing lisseHomTargetCoordinatesRing
  lisseHomCoordinatesRing lisseHomReducedBasisRing lisseHomModelMapRing

/-- A closed immersion followed by an open immersion in a separated finite-type
scheme over the fixed field has the geometric finiteness instances needed by the
constructible Hom theorem. The proof uses stability of separatedness, local finite
type and quasi-compactness under composition and the standard Noetherian criterion.
Source: proof paragraphs 2--4 of `thm-coef-finite-hom`
(blueprint: lem-coef-etale-lisse-hom-reduction). -/
private theorem etaleLisseHomStratumInstances
    (D : FiniteFieldDatum.{u})
    (X Z S : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] :
    AlgebraicGeometry.IsNoetherian X ∧
    IsSeparated (g ≫ (X ↘ Spec (.of D.k))) ∧
    LocallyOfFiniteType (g ≫ (X ↘ Spec (.of D.k))) ∧
    QuasiCompact (g ≫ (X ↘ Spec (.of D.k))) ∧
    AlgebraicGeometry.IsNoetherian Z ∧
    IsSeparated (j ≫ g ≫ (X ↘ Spec (.of D.k))) ∧
    LocallyOfFiniteType (j ≫ g ≫ (X ↘ Spec (.of D.k))) ∧
    QuasiCompact (j ≫ g ≫ (X ↘ Spec (.of D.k))) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)) }
  have : AlgebraicGeometry.IsNoetherian Z :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance⟩


private theorem exceptional_bounds
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A] [HasInvertibleExponent A (Spec (.of k))]
    (X Z S : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [AlgebraicGeometry.IsNoetherian X]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (dX : ℕ) (_hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (M : Etale.DerivedCategoryModule A X) (a b : ℤ)
    (_hM : Etale.DerivedCategory.isBoundedConstructible A X M)
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b M) :
    Etale.DerivedCategory.isBoundedConstructible A S
      ((lisseHomStratumExceptionalRing A g j).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A S a (b + 2 * (dX : ℤ) + 1)
      ((lisseHomStratumExceptionalRing A g j).obj M) := by
  let W : X.Opens := ⟨(Set.range g.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding g).isClosed_range.isOpen_compl⟩
  have hcompl : Set.range g.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hopen' := Etale.openComplementCondition_two_mul (Λ := A)
    (X ↘ Spec (.of k)) W.ι dX _hdX
  have hclosed := Etale.boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek
    g W.ι hcompl hopen' ((lisseBounded_iff A X M).1 _hM)
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 _hTor)
  have hn := closed_restrict_bounds A g j M _ _ hclosed
  unfold lisseHomStratumExceptionalRing
  dsimp only [Functor.comp_obj]
  convert hn using 1; norm_num only [Nat.cast_mul, Nat.cast_ofNat]

set_option backward.defeqAttrib.useBackward false in
private theorem projective_free_of_local_quotient
    (R A : Type v) [CommRing R] [IsLocalRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f)
    (V : Type w) [AddCommGroup V] [Module A V]
    [Module.Finite A V] [Module.Projective A V] : Module.Free A V := by
  rcases subsingleton_or_nontrivial A with hzero | hnonzero
  · exact Module.Free.of_subsingleton' A V
  · have : IsLocalRing A := IsLocalRing.of_surjective' f hf
    have : Module.Flat A V := Module.Flat.of_projective (R := A) (M := V)
    exact Module.free_of_flat_of_isLocalRing (R := A) (P := V)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward false in
private theorem coefficientProjective_free (n : ℕ)
    (V : ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    [Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) V]
    [Module.Projective (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) V] :
    ∃ t : ℕ, Nonempty (V ≅ ModuleCat.of
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (Fin t → ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  have : IsLocalRing (Padic.coefficientExtensionIntegers l E) :=
    coefficientIntegers_local l E
  let e : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) ≃+*
      Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  let : IsLocalRing (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :=
    e.symm.isLocalRing
  have : Module.Free
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) V :=
    projective_free_of_local_quotient _ _
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).ulift)
      (fun x ↦ by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x.down
        exact ⟨ULift.up y, congrArg ULift.up hy⟩) V
  exact finiteFreeIso _ V

/-- A projective coefficient trivialization can be refined to a finite-free one.
Source: finite projective modules over the positive coefficient local quotient.
(blueprint: lem-coef-etale-lisse-hom-finite-free-cover)
Finite projective modules over the coefficient local ring are finite free; applying a
basis isomorphism on each member of the supplied etale cover gives the result. -/
theorem etaleLisseHomFiniteFreeCover
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (S : Scheme.{u})
    (L : Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (_hL : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ V : ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))),
        Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) V ∧
        Module.Projective (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))) V ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (U.f i)).obj L ≅
          (lisseHomConstantFunctor
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (U.X i)).obj V)) :
    ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (U.f i)).obj L ≅
          (lisseHomConstantFunctor
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (U.X i)).obj
            (ModuleCat.of (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E (n + 1)))
              (Fin t → ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E (n + 1))))) := by
  obtain ⟨U, hU⟩ := _hL
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨V, hfin, hproj, ⟨e⟩⟩ := hU i
  obtain ⟨t, ⟨eV⟩⟩ := coefficientProjective_free l E n V
  exact ⟨t, ⟨e ≪≫ (lisseHomConstantFunctor _ (U.X i)).mapIso eV⟩⟩

/-- The finite-free lisse cover yields perfectness, Tor amplitude and constructibility.
Source: the lisse cover lemmas for site-perfect complexes.
(blueprint: lem-coef-etale-lisse-hom-lisse-bounds)
The cover is degree-zero finite free, so the single complex is site-perfect and has
Tor interval [0,0]; the same cover gives bounded constructibility. -/
theorem etaleLisseHomLisseBounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (S : Scheme.{u})
    (L : Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (htriv : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (U.f i)).obj L ≅
          (lisseHomConstantFunctor
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (U.X i)).obj
            (ModuleCat.of (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E (n + 1)))
              (Fin t → ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E (n + 1)))))) :
    Etale.DerivedCategory.IsSitePerfect ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
    Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) := by
  obtain ⟨h₁, h₂⟩ := lisse_bounds_of_cover _ S L htriv
  exact ⟨perfect_of_cover _ S L htriv, h₁, h₂⟩

/-- Positive coefficient quotients have an invertible exponent over the finite field.
Source: the coefficient annihilator and the characteristic inequality.
(blueprint: lem-coef-etale-lisse-hom-coefficient-invertible-exponent)
The power l^(n+1) annihilates the coefficient quotient and l is invertible in the
algebraic closure of the finite field because l differs from its characteristic. -/
theorem etaleLisseHomCoefficientInvertibleExponent
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (n : ℕ) :
    HasInvertibleExponent
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (Spec (.of D.k)) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hlk : (l : D.k) ≠ 0 := fun hz ↦
    _hl ((CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm.trans
      (ringChar.eq D.k D.p))
  have hu : IsUnit ((l ^ (n + 1) : ℕ) : D.k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow _
  refine ⟨l ^ (n + 1), pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
  · apply ULift.down_injective
    simp only [Nat.cast_pow, ULift.pow_down, ULift.down_natCast, ULift.zero_down]
    exact coefficient_prime_pow_zero l E (n + 1)
  · simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom

/-- Exceptional pullback bounds on the open lisse stratum.
Source: open-complement cohomological dimension and closed-support Tor bounds.
(blueprint: lem-coef-etale-lisse-hom-exceptional-bounds)
The coefficient annihilator supplies the invertible-exponent hypothesis, after which
the open-complement and closed-support theorems give the stated constructibility and
Tor interval. -/
theorem etaleLisseHomExceptionalBounds
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (n : ℕ)
    (X Z S : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (dX : ℕ) (_hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (M : finiteHomEtale l E X n) (a b : ℤ)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X M)
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b M) :
    Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      ((lisseHomStratumExceptional l E n g j).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      a (b + 2 * (dX : ℤ) + 1) ((lisseHomStratumExceptional l E n g j).obj M) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : AlgebraicGeometry.IsNoetherian X := (etaleLisseHomStratumInstances D X Z S g j).1
  have : HasInvertibleExponent
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (Spec (.of D.k)) :=
    etaleLisseHomCoefficientInvertibleExponent l E D _hl n
  have h := exceptional_bounds D.k _ X Z S g j dX _hdX M a b _hM _hTor
  unfold lisseHomStratumExceptionalRing at h
  unfold lisseHomStratumExceptional
  exact h

/-- The canonical Hom comparison and its two local compatibility predicates.
Source: finite-free evaluation and perfect-input restriction calculations.
(blueprint: lem-coef-etale-lisse-hom-comparison-data)
Proof: the canonical arrow is invertible by lem-coef-etale-lisse-canonical-iso. The
finite-free coordinate identity (lem-coef-etale-finite-free-hom-local-identity), applied to
the restricted inputs, is the local predicate on every etale object, and the perfect-input
restriction square (lem-coef-etale-perfect-hom-restriction) is the restriction predicate. -/
theorem etaleLisseHomComparisonData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n m : ℕ) (hmn : m ≤ n)
    (S : Scheme.{u}) (K N : finiteHomEtale l E S n)
    (hKdual : IsDualizable K)
    (htrivK : ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : V.I₀,
      ∃ r : ℕ, Nonempty
        ((L(Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (V.f i))).obj K ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((lisseHomConstantFunctor
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (V.X i)).obj
                (ModuleCat.of (ULift.{u + 1, u}
                  (Padic.coefficientExtensionRing l E (n + 1)))
                  (Fin r → ULift.{u + 1, u}
                    (Padic.coefficientExtensionRing l E (n + 1)))))))
    (hNbc : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S N)
    (c d : ℤ) (hcd : c ≤ d)
    (hNtor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S c d N) :
    IsIso (etaleFiniteHomCanonical l E S hmn K N) ∧
    (∀ U : S.Etale, LisseHomRestrictedLocalFreeCalculation l E S U.left U.hom hmn K N) ∧
    (∀ U : S.Etale, LisseHomRestrictionCompatibility l E S U.left U.hom hmn K N) := by
  refine ⟨etaleLisseCanonicalIso l E n m hmn S K N hKdual htrivK hNbc c d hcd hNtor,
    fun U ↦ ?_, fun U ↦ ?_⟩
  · unfold LisseHomRestrictedLocalFreeCalculation LisseHomLocalFreeCalculation
    exact etaleFiniteFreeHomLocalIdentity l E U.left hmn _ _
  · have : Etale U.hom := U.prop
    unfold LisseHomRestrictionCompatibility
    exact etalePerfectHomRestriction l E S U.left U.hom hmn K N hKdual

/-- Lisse projective strata have the stated exceptional and Hom Tor bounds, and their
canonical coefficient-Hom comparison is invertible with both endpoints in D^b_ctf.
Source: thm-coef-finite-hom proof paragraphs 2–3
(blueprint: lem-coef-etale-lisse-hom-reduction).

Proof:
1. The coefficient DVR and finite-quotient theorems make A a finite local ring. Finite
projective modules are flat and finite flat modules over a local ring are free. Also
ℓ belongs to the maximal ideal generated by the uniformizer, so ℓ^(n+1) annihilates A. Thus
L has a finite-free etale cover, including rank zero; its single complex is site-perfect
in degree zero. Restriction and tensor commute, so testing on degree-zero sheaves gives
Tor interval [0,0]. The one-stratum partition proves constructibility of L.
2. Finite type over the fixed field makes X Noetherian. A closed subscheme Z is still
separated finite type, and an open S in Z is quasi-compact, separated and finite type.
3. Apply thm-pur-open-complement-unconditional to X minus Z: its direct image has
cohomological dimension at most 2dX and preserves constructibility. The closed-support
Tor theorem gives Rg!M interval [a,b+2dX+1]. Exact inverse image along j preserves it.
4. Apply cor-weil-finite-constructible-hom on S to L of interval [0,0] and N of the
previous interval. Its formula gives [a-2dS,b+2dX+1+2dS] for Q.
5. Bounded-flat models and K-flat scalar extension preserve constructibility and the
finite Tor intervals for L, N and Q. Apply the finite constructible Hom theorem over B
to the reductions of L and N; hence both comparison endpoints lie in D^b_ctf over B.
On a trivializing cover bounded-free RHom identifies Q with P^t and
the target with (P tensor B)^t. Evaluation is sum a_i x_i; its reduced transpose has
the same coordinates, so is the identity, including t=0. These coordinates commute
with restriction and B-scalar multiplication. The cone of the comparison restricts
to zero on this cover, hence has zero geometric stalks and is zero by conservativity.
Fullness gives the isomorphism in D^b_ctf. -/
theorem etaleLisseHomReduction
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (n m : ℕ) (hmn : m ≤ n)
    (X Z S : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (dX dS : ℕ) (_hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (_hdS : topologicalKrullDim S ≤ (dS : WithBot ℕ∞))
    (L : Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (_hL : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ V : ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))),
        Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) V ∧
        Module.Projective (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))) V ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (U.f i)).obj L ≅
          (lisseHomConstantFunctor
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (U.X i)).obj V))
    (M : finiteHomEtale l E X n) (a b : ℤ)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X M)
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b M) :
    (∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (U.f i)).obj L ≅
          (lisseHomConstantFunctor
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (U.X i)).obj
            (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
              (Fin t → ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))) ∧
    Etale.DerivedCategory.IsSitePerfect ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
    Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      ((lisseHomStratumExceptional l E n g j).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      a (b + 2 * (dX : ℤ) + 1) ((lisseHomStratumExceptional l E n g j).obj M) ∧
    Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      ((finiteHomEtaleInternalHom l E S n).obj
        (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L),
          (lisseHomStratumExceptional l E n g j).obj M)) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S
      (a - 2 * (dS : ℤ)) (b + 2 * (dX : ℤ) + 1 + 2 * (dS : ℤ))
      ((finiteHomEtaleInternalHom l E S n).obj
        (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L),
          (lisseHomStratumExceptional l E n g j).obj M)) ∧
    Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))) S
      ((finiteHomEtaleReduction l E S hmn).obj
        ((finiteHomEtaleInternalHom l E S n).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L),
            (lisseHomStratumExceptional l E n g j).obj M))) ∧
    Etale.DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) S
      ((finiteHomEtaleReduction l E S hmn).obj
        ((finiteHomEtaleInternalHom l E S n).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L),
            (lisseHomStratumExceptional l E n g j).obj M))) ∧
    Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))) S
      ((finiteHomEtaleInternalHom l E S m).obj
        (op ((finiteHomEtaleReduction l E S hmn).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)),
          (finiteHomEtaleReduction l E S hmn).obj
            ((lisseHomStratumExceptional l E n g j).obj M))) ∧
    Etale.DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) S
      ((finiteHomEtaleInternalHom l E S m).obj
        (op ((finiteHomEtaleReduction l E S hmn).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)),
          (finiteHomEtaleReduction l E S hmn).obj
            ((lisseHomStratumExceptional l E n g j).obj M))) ∧
    IsIso (etaleFiniteHomCanonical l E S hmn
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L)
      ((lisseHomStratumExceptional l E n g j).obj M)) ∧
    (∀ U : S.Etale, LisseHomRestrictedLocalFreeCalculation l E S U.left U.hom hmn
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L)
      ((lisseHomStratumExceptional l E n g j).obj M)) ∧
    (∀ U : S.Etale, LisseHomRestrictionCompatibility l E S U.left U.hom hmn
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L)
      ((lisseHomStratumExceptional l E n g j).obj M)) := by
  classical
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : Z.Over (Spec (.of D.k)) := ⟨g ≫ (X ↘ Spec (.of D.k))⟩
  let : S.Over (Spec (.of D.k)) := ⟨j ≫ (Z ↘ Spec (.of D.k))⟩
  obtain ⟨hXnoeth, hZsep, hZft, hZqc, hZnoeth, hSsep, hSft, hSqc⟩ :=
    etaleLisseHomStratumInstances D X Z S g j
  have : AlgebraicGeometry.IsNoetherian X := hXnoeth
  have : IsSeparated (Z ↘ Spec (.of D.k)) := hZsep
  have : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) := hZft
  have : QuasiCompact (Z ↘ Spec (.of D.k)) := hZqc
  have : AlgebraicGeometry.IsNoetherian Z := hZnoeth
  have : IsSeparated (S ↘ Spec (.of D.k)) := hSsep
  have : LocallyOfFiniteType (S ↘ Spec (.of D.k)) := hSft
  have : QuasiCompact (S ↘ Spec (.of D.k)) := hSqc
  have htriv : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : U.I₀,
      ∃ t : ℕ, Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).obj L ≅
        (lisseHomConstantFunctor A (U.X i)).obj
          (ModuleCat.of A (Fin t → A))) :=
    etaleLisseHomFiniteFreeCover l E n S L _hL
  obtain ⟨hperfect, hLtor, hLbc⟩ := etaleLisseHomLisseBounds l E n S L htriv
  obtain ⟨hNbc, hNtor⟩ :=
    etaleLisseHomExceptionalBounds l E D _hl n X Z S g j dX _hdX M a b _hM _hTor
  generalize hNdef : (lisseHomStratumExceptional l E n g j).obj M = N at hNbc hNtor ⊢
  have htrivK := derived_free_cover A S L htriv
  generalize hKdef :
    (_root_.DerivedCategory.singleFunctor _ 0).obj L = K at hperfect hLtor hLbc htrivK
  let Q := (finiteHomEtaleInternalHom l E S n).obj (op K, N)
  have hNwide : Etale.DerivedCategory.hasTorAmplitudeIn A S
      (min a (b + 2 * (dX : ℤ) + 1)) (b + 2 * (dX : ℤ) + 1) N :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (Etale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hNtor))
  have hKdual : IsDualizable K := hperfect.isDualizable
  obtain ⟨hQbc, hQtor, hsrcbc, hsource, htgtbc, htarget⟩ :=
    etaleLisseHomEndpointBounds l E D _hl n m hmn S K N Q (by rfl)
      hLbc hLtor hKdual hNbc a b (dX : ℤ) dS hNtor
  obtain ⟨c, d, hsource⟩ := hsource
  obtain ⟨e, f, htarget⟩ := htarget
  obtain ⟨hcanonical, hlocal, hrestrict⟩ := etaleLisseHomComparisonData l E n m hmn S K N
    hKdual htrivK hNbc (min a (b + 2 * (dX : ℤ) + 1)) _ (min_le_right _ _) hNwide
  exact ⟨htriv, hperfect, hLtor, hNbc, hNtor, hQbc, hQtor, hsrcbc,
    ⟨c, d, hsource⟩,
    htgtbc,
    ⟨e, f, htarget⟩,
    hcanonical, hlocal, hrestrict⟩

end WeilConjectures
