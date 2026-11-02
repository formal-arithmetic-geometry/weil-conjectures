/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleGenericImmersionProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Bounded-below Hom continuity for a perfect etale stratum

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14,
Remark 6.3.15 and the filtered-colimit argument of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-etale-stratum-hom-continuity).

The filtered colimit is formed on compatible complex representatives, not in the
ordinary triangulated category. A functorial model E and its natural identification e
specify all transition maps. The comparison is Q(colimit.post N E) followed by e at
colimit N. The second assertion gives all shifted Hom groups without choosing E.
Local constancy with perfect values is written out using the recorded perfect-ring
predicate and the existing derived constant and inverse-image functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Every shifted derived Hom group carries the colimit cocone induced by the original
representatives. No choice of a global-Hom complex model is required in this assertion.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-stratum-hom-continuity).
Proof: Follow steps 1--6 above, including the shifts n of P. The natural coefficient-model
cohomology identification of lem-sfb-global-rhom-coefficient-model identifies degree q
with Hom(a!(P[n]),N[q]). Exact filtered colimits commute with homology by
src-weil-homology-preserves-exact-colimits. The original cocone therefore becomes a
colimit cocone of abelian groups, with its original postcomposition maps. This also
includes negative q, n=0, the zero ring and the empty stratum. -/
theorem etaleStratum_shiftedHom_isColimit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_ha : Topology.IsConstructible (Set.range (i ≫ j)))
    (P : DerivedCategoryModule A S)
    (_hPb : ∃ a b : ℤ, P.IsGE a ∧ P.IsLE b)
    (_hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ k : 𝒰.I₀,
      ∃ C : _root_.DerivedCategory (ModuleCat.{u + 1} A),
        _root_.DerivedCategory.IsPerfectRingComplex C ∧
        Nonempty ((ExternalRHom.pull A (𝒰.f k)).obj P ≅
          (ExternalRHom.constant A (𝒰.X k)).obj C))
    (n : ℤ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (r : ℤ) (_hN : ∀ k : J, (_root_.DerivedCategory.Q.obj (N.obj k)).IsGE r) (q : ℤ) :
    Nonempty (IsColimit
      ((_root_.DerivedCategory.Q ⋙ shiftFunctor (DerivedCategoryModule A X) q ⋙
        preadditiveCoyoneda.obj (op ((immersionLowerShriek A i j).obj (P⟦n⟧)))).mapCocone
          (colimit.cocone N))) := by
  sorry

end AlgebraicGeometry.Etale
