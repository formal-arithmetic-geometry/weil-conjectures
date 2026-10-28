module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
import all Sheaf.SixFunctors.FlatModelGeneration
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.CategoryTheory.SignedDerivedInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Sheaf.Paper.LocallyClosedProjectiveHomAnyField

/-! # Finite-Tor internal Hom over an arbitrary field

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemma 6.7.13,
Definition 6.5.1 and its finite-coefficient comparison paragraph
(blueprint: lem-per-finite-tor-internal-hom-any-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.Scheme

/-- Ambient internal Hom of finite-Tor bounded constructible finite-coefficient complexes
is bounded constructible and has bounded constructible étale origin over any ground field.

Source: Bhatt–Scholze, Lemma 6.7.13, p. 57, and Definition 6.5.1, p. 49
(blueprint: lem-per-finite-tor-internal-hom-any-field).

Proof:
1. The coefficient ring A = O_E/ϖ^n is finite and Noetherian, and is killed by ℓ^n,
which is invertible in k. Finite A-modules are precisely finitely presented ones.
2. Finite-type k-schemes, their locally closed strata, closures and open complements
are Noetherian and qcqs. No perfection or separable closedness of k is required.
3. Bounded complexes with constructible finite-valued cohomology form a thick subcategory:
use the constructible weak Serre property for triangles and kernels of idempotents for retracts.
4. Exact constant-coefficient inverse image preserves cohomological bounds and pulls back
finite constructible stratifications and their finite locally constant models.
5. Finite-type direct image preserves bounded constructibility: choose a bounded constructible
étale origin, apply finite-type étale finiteness, and use the qcqs direct-image comparison.
6. For a closed immersion g with open complement h, the support triangle
 g_* Rg^! N → N → Rh_* h^* N
and steps 3--5 give constructibility of g_* Rg^! N. Apply exact g^* and g^*g_* ≅ 1.
7. For a locally constant finite projective sheaf L on a stratum, perfect duality gives
RHom(L,N) ≅ L^∨ ⊗ᴸ N. Locally this is a finite projective summand of finite sums of N,
so it has bounded constructible finite-valued cohomology.
8. Finite-Tor constructible K is generated, under shifts, cones, isomorphisms and retracts,
by a_! L with a locally closed and L locally constant finite projective. Factor a = j ≫ g
with j open in the closure and g closed, so a_! L = g_* j_! L.
9. Apply ambient internal adjunction first to g and then to j:
RHom(g_*j_!L,M) ≅ Rg_* Rj_* RHom(L,j^*Rg^!M).
Steps 4--7 and 5 show that this is bounded constructible.
10. For fixed M, the inputs P for which RHom(P,M) is bounded constructible form a thick
subcategory by the exactness, shifts and contravariance of ambient Hom. Steps 8--9 put K in it.
11. Finite-ring constructible derived comparison gives the bounded constructible étale
origin of the resulting object. Empty X and zero inputs give zero; n = 1 is included.
The finite-Tor hypothesis on M is retained as stated, though this argument needs only its
bounded constructibility. There is no characteristic assumption beyond ℓ being invertible.
-/
theorem finiteTor_internalHom_constructible_anyField
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (K M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hK : WeilConjectures.finiteTorConstructible l E n hn X K)
    (_hM : WeilConjectures.finiteTorConstructible l E n hn X M) :
    intrinsicFiniteTorsionConstructible l E n hn X
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, M)) ∧
    ∃ L : ProEtale.FiniteCoefficientEtaleDerivedCategory X
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)),
      @Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
        (Finite.of_equiv (Padic.coefficientExtensionRing l E n)
          (h := Padic.finite_coefficientExtensionRing l E n hn) Equiv.ulift.symm) X L ∧
      Nonempty ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison X
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj L ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, M)) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)) }
  let C := proEtaleRingModules X (proEtaleConstantRing X A)
  let P : ObjectProperty (proEtaleDerivedCategory X A) :=
    intrinsicFiniteTorsionConstructible l E n hn X
  obtain ⟨hiso, htri⟩ := proEtale_bounded_constructible_isTriangulated X A
  have : P.IsClosedUnderIsomorphisms := hiso
  have : P.IsTriangulated := htri
  have : P.IsStableUnderRetracts := ⟨fun {B D} r hD ↦ by
    refine ⟨hD.1.subset ?_, fun q ↦ ?_⟩
    · intro q hq hz
      have rr := r.map (DerivedCategory.homologyFunctor C q)
      apply hq
      apply (IsZero.iff_id_eq_zero _).mpr
      rw [← rr.retract, hz.eq_of_tgt rr.i 0, zero_comp]
    · have hc := flatModel_intrinsic_constructible_retract X A
        (r.map (DerivedCategory.homologyFunctor C q))
        ((CoefficientSerre.coefficient_constructible_iff X (ULift.{u + 1, u} A) _).mpr
          ((proEtaleModuleRestriction_constructible_iff X A _).mp (hD.2 q)))
      exact (proEtaleModuleRestriction_constructible_iff X A _).mpr
        ((CoefficientSerre.coefficient_constructible_iff X (ULift.{u + 1, u} A) _).mp hc)⟩
  let H := derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology X) (proEtaleConstantRing X A)
  let F := Prod.sectL _ M ⋙ H
  obtain ⟨sF, hsF⟩ := signedDerivedInternalHom_exact.{u + 1, u, u}
    (ProEt.topology X) (proEtaleConstantRing X A) M
  let : F.CommShift ℤ := sF
  have : F.IsTriangulated := hsF.1
  let Q := (P.inverseImage F).unop
  have : Q.IsTriangulated := inferInstance
  have : Q.IsStableUnderRetracts := ⟨fun r h ↦ P.prop_of_retract (r.op.map F) h⟩
  let G : ObjectProperty (proEtaleDerivedCategory X A) := fun B ↦
    ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L : proEtaleRingModules S (proEtaleConstantRing S A)),
      FlatModelProEtaleLisseProjective S A L ∧
      Nonempty (B ≅ (DerivedCategory.singleFunctor _ 0).obj
        ((flatModelProEtaleExtension A a ha).obj L))
  have hgen : G ≤ Q := by
    rintro B ⟨S, a, ha, L, hL, ⟨e⟩⟩
    exact P.prop_of_iso (F.mapIso e.op)
      (locallyClosedProjective_internalHom_constructible_anyField
        k l _hl E n hn X S a ha L hL M _hM.1)
  have hK : G.triangEnvelope K := by
    rw [← proEtale_flatConstructible_thickGeneration X A]
    refine ⟨fun q ↦ ?_, ?_, _hK.2⟩
    · exact (CoefficientSerre.coefficient_constructible_iff X (ULift.{u + 1, u} A) _).mpr
        ((proEtaleModuleRestriction_constructible_iff X A _).mp (_hK.1.2 q))
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
        Set.finite_iff_bddBelow_bddAbove.mp _hK.1.1
      refine ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
      by_contra hz
      rcases hq with hq | hq
      · exact (not_le_of_gt hq) ((min_le_left _ _).trans (ha hz))
      · exact (not_le_of_gt hq) ((hb hz).trans (le_max_right _ _))
  have hH : P (H.obj (op K, M)) :=
    ((ObjectProperty.triangEnvelope_le_iff (P := G)).mpr hgen) K hK
  refine ⟨hH, ?_⟩
  have hb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor C i).obj (H.obj (op K, M))) := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Set.finite_iff_bddBelow_bddAbove.mp hH.1
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hz
    rcases hi with hi | hi
    · exact (not_le_of_gt hi) ((min_le_left _ _).trans (ha hz))
    · exact (not_le_of_gt hi) ((hb hz).trans (le_max_right _ _))
  obtain ⟨L, ⟨e⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1
    (H.obj (op K, M))).mpr ⟨hH.2, hb⟩
  exact ⟨L.obj, L.property, ⟨e⟩⟩

end AlgebraicGeometry.Scheme
