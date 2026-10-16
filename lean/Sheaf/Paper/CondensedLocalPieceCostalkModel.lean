/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Paper.CondensedFiniteFreeDerivedHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # A compatible strict costalk model for the Hom cocone of a locally closed piece -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Transport the Hom cocone through j_! and i_* to a strict bounded-below diagram on U.
This does not assert that either Hom cocone is a colimit, and makes no finite-presentation
assumption on P.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), costalk and adjunction steps.
(blueprint: lem-weil-pbc-condensed-local-piece-costalk-model)

Proof: use the exceptional right adjoint of the closed pushforward and the exact
restriction along j. On the bounded-below derived categories, the two adjunctions
identify Hom(i_*j_!P[0],N[n]) with Hom(P[0],j^*Ri^!N[n]), naturally in N. Choose the
functorial bounded injective resolution at the common bound supplied by recollement,
apply the exceptional functor and j^* termwise, and use good truncation to obtain L.
Its terms vanish below a common bound. The recollement triangle identifies i_*Ri^!N
with Cone(N -> Rk_*k^*N)[-1], for the complementary quasi-compact open k.
Qcqs pushforward continuity and exact filtered colimits identify the termwise colimit
of these models with j^*Ri^! of the original colimit. Apply Hom(P[0],-[n]) to this
identification to obtain the vertex isomorphism. Naturality of both adjunctions gives
the diagram isomorphism and its leg equation. All isomorphisms use the original cocone
legs. Include the bounded-below derived categories fully faithfully into the ordinary
ones. The argument also applies to zero P and empty U or Z. -/
theorem condensed_local_piece_costalk_model
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((N.obj s).X r))
    (n : ℤ) :
    let F := shiftFunctor
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj P))))
    let G := condensedShiftedHom Λ U ((DerivedCategory.singleFunctor _ 0).obj P) n
    ∃ L : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ,
      (∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((L.obj s).X r)) ∧
      ∃ (e : (N ⋙ DerivedCategory.Q) ⋙ F ≅ L ⋙ G)
        (v : F.obj (DerivedCategory.Q.mapCocone (colimit.cocone N)).pt ≅
          G.obj (colimit.cocone L).pt),
        ∀ s : I, F.map ((DerivedCategory.Q.mapCocone (colimit.cocone N)).ι.app s) ≫ v.hom =
          e.hom.app s ≫ G.map ((colimit.cocone L).ι.app s) := by
  sorry

end AlgebraicGeometry.ProEtale
