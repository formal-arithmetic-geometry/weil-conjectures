/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitRoos
import Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitCanonical

/-! # Global Hom and the limit of a strict mapping tower

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph;
Stacks 0B6E, 0D3F and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Global Hom into a prescribed Roos limit is the total derived limit of the
strict global Hom tower. This assertion uses no finite duality comparison.

Source: current blueprint prop-coef-integral-dualizing, first displayed comparison
in the second proof paragraph; Stacks 0B6E, 0D3F and 0941.
(blueprint: lem-coef-integral-dualizing-mapping-tower-limit).

Proof: resolve T.tower by a K-injective complex of injective completed-module
towers. Evaluation gives K-injectives and degreewise split transition maps.
The ordinary limit of this resolution computes the published derived limit.
Its canonical Roos triangle and the triangle in hM have the same 1-shift map,
so rotation and the distinguished-triangle isomorphism theorem identify their
first objects. Use a K-flat representative P for the first Hom argument. The
constant-ring sequence equivalence identifies the internal Hom in the definition
of integralDualizingMappingTower with the tower Hom(P,I_n), including its maps.
Sections retain exactly integralDualizingScalar, since coefHomScalar is the same
constant-to-completion section map. The global-Hom sections model identifies
Hom(P,lim I) with lim Hom(P,I_n), with the same differential and projections.
The latter tower has degreewise surjective transitions, so its ordinary limit
computes its derived limit. These comparisons commute with precomposition in P
and with homotopies. Descend them through localization, obtaining naturality on
the entire constructible category, rather than choosing separate isomorphisms
for its objects. The construction applies also to the zero complex and empty X. -/
private theorem integralDualizingGlobalHom_iso_of_iso
    {M N : DerivedCategory (scalarReductionSource l E X)} (e : M ≅ N) :
    Nonempty (integralDualizingGlobalHom l E X M ≅
      integralDualizingGlobalHom l E X N) := by
  let F := (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X))).flip
  exact ⟨Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι.op (F.mapIso e))
    (integralDualizingDerivedSections l E X)⟩

theorem integralDualizing_mapping_tower_limit
    (T : NormalizedDVRTower l E X D hl)
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    Nonempty (integralDualizingGlobalHom l E X M.obj ≅
      integralDualizingMappingTower l E X T.tower ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E)) := by
  obtain ⟨eM⟩ := integralDualizing_mapping_tower_limit_roos_iso D l hl E X T M hM
  obtain ⟨eLimit⟩ := integralDualizing_mapping_tower_limit_canonical D l hl E X T
  obtain ⟨eHom⟩ := integralDualizingGlobalHom_iso_of_iso l E X eM
  exact ⟨eHom ≪≫ eLimit⟩

end WeilConjectures
