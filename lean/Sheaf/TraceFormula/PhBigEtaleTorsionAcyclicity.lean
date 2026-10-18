/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.AlgebraicGeometry.PhSchemeSite
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.TraceFormula.BigSmallEtaleExactRetraction
import Sheaf.TraceFormula.PhEtaleComparisonHypotheses
import Sheaf.TraceFormula.RefinedTopologyComparisonVanishing

/-!
# Torsion étale-origin sheaves are ph-to-big-étale acyclic

Source: Stacks Project, Etale Cohomology, Tag 0DE4, lemma-V-C-all-n-etale-ph,
part (1), with the comparison setup of Tag 0F0I (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity).

The statement uses the identity comparison between the ph and big étale topologies
on `Over T`, together with the canonical big-to-small étale retraction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme

/-- The identity functor from the big étale site to the big ph site is continuous.
Source: Stacks Project, Topologies, Tag 0DBQ (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity).
The étale covering families are ph covering families, and fibre products in `Over T`
are preserved by the identity functor. -/
theorem phBigEtale_identity_isContinuous (T : Scheme.{u}) :
    (𝟭 (Over T)).IsContinuous (etaleTopology.over T) (phTopology T) := by
  sorry

attribute [instance] phBigEtale_identity_isContinuous

/-- The inverse image of the comparison preserves finite limits.
Source: Stacks Project, Sites, Tag 00YV (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
theorem phBigEtale_inverse_leftExact (T : Scheme.{u}) :
    PreservesFiniteLimits ((𝟭 (Over T)).sheafPullback (Type (u + 1))
      (etaleTopology.over T) (phTopology T)) := by
  sorry

attribute [instance] phBigEtale_inverse_leftExact

/-- The ph sheaf category has enough injectives for ordinary right derived functors.
Source: Stacks Project, Sites, Tag 00YV (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
theorem phBigEtale_hasInjectiveResolutions_exists (T : Scheme.{u}) :
    HasInjectiveResolutions (Sheaf (phTopology T) AddCommGrpCat.{u + 1}) := by
  sorry

/-- Instance form of the ph-site injective-resolution interface.
Source: Stacks Project, Sites, Tag 00YV (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
noncomputable instance phBigEtale_hasInjectiveResolutions (T : Scheme.{u}) :
    HasInjectiveResolutions (Sheaf (phTopology T) AddCommGrpCat.{u + 1}) :=
  phBigEtale_hasInjectiveResolutions_exists T

/-- The comparison geometric morphism from ph sheaves to big étale sheaves.
Source: Stacks Project, Etale Cohomology, Tags 0DDW and 0F0I (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity).
Its inverse image is ph sheafification and its direct image keeps the underlying
presheaf unchanged. -/
def phBigEtaleGeometricMorphism (T : Scheme.{u}) :
    GeometricMorphism
      (Sheaf (phTopology T) (Type (u + 1)))
      (Sheaf (etaleTopology.over T) (Type (u + 1))) where
  inverse := (𝟭 (Over T)).sheafPullback (Type (u + 1))
    (etaleTopology.over T) (phTopology T)
  direct := (𝟭 (Over T)).sheafPushforwardContinuous (Type (u + 1))
    (etaleTopology.over T) (phTopology T)
  adj := (𝟭 (Over T)).sheafAdjunctionContinuous _ _ _
  leftExact := phBigEtale_inverse_leftExact T

/-- The abelian adjunction underlying the comparison geometric morphism.
Source: Stacks Project, Sites, Tags 00WW and 00WX, with Etale Cohomology,
Tags 0DDW and 0F0I (blueprint: lem-trf-ph-big-etale-torsion-acyclicity). -/
def phBigEtaleAbelianAdjunction (T : Scheme.{u}) :
    ((𝟭 (Over T)).sheafPullback AddCommGrpCat.{u + 1}
      (etaleTopology.over T) (phTopology T)) ⊣
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (etaleTopology.over T) (phTopology T)) :=
  (𝟭 (Over T)).sheafAdjunctionContinuous _ _ _

/-- A chosen canonical big-to-small étale retraction datum.
Source: Stacks Project, Etale Cohomology, Tag 0DDI (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
noncomputable def bigSmallEtaleData (T : Scheme.{u}) :
    BigSmallEtaleRetractionData T :=
  Classical.choice (bigSmallEtaleExactRetraction T)

/-- The inverse-image component of the big-to-small étale retraction.
Source: Stacks Project, Etale Cohomology, Tag 0DDI (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
abbrev bigEtaleInverse (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over T) AddCommGrpCat.{u + 1} :=
  (bigSmallEtaleData T).morphism.inverse

/-- The inverse-image functor from big étale sheaves to ph sheaves.
Source: Stacks Project, Etale Cohomology, Tags 0DDW and 0F0I (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
abbrev phBigEtaleInverse (T : Scheme.{u}) :
    Sheaf (etaleTopology.over T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (phTopology T) AddCommGrpCat.{u + 1} :=
  (𝟭 (Over T)).sheafPullback AddCommGrpCat.{u + 1}
    (etaleTopology.over T) (phTopology T)

/-- The direct-image functor from ph sheaves to big étale sheaves.
Source: Stacks Project, Etale Cohomology, Tags 0DDW and 0F0I (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
abbrev phBigEtaleDirect (T : Scheme.{u}) :
    Sheaf (phTopology T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over T) AddCommGrpCat.{u + 1} :=
  (𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (etaleTopology.over T) (phTopology T)

/-- The direct image on abelian sheaves is additive.
Source: Stacks Project, Sites, Tag 00YV (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
theorem phBigEtaleDirect_additive_exists (T : Scheme.{u}) :
    (phBigEtaleDirect T).Additive := by
  sorry

/-- Instance form of additivity of the comparison direct image.
Source: Stacks Project, Sites, Tag 00YV (blueprint:
lem-trf-ph-big-etale-torsion-acyclicity). -/
noncomputable instance phBigEtaleDirect_additive (T : Scheme.{u}) :
    (phBigEtaleDirect T).Additive :=
  phBigEtaleDirect_additive_exists T

/-- For a scheme `T` and a torsion abelian sheaf `F` on its small étale site, the
ordinary unit from its big étale origin to the ph comparison inverse image is an
isomorphism, and all positive right derived direct images of that inverse image
vanish. Source: Stacks Project, Etale Cohomology, Tag 0DE4, lemma-V-C-all-n-etale-ph,
part (1), with Tag 0F0I (blueprint: lem-trf-ph-big-etale-torsion-acyclicity).

Proof: apply the comparison-hypotheses theorem (Tag 0F0I) to the identity slice
and then the refined-topology comparison vanishing theorem (Tag 0EZF), taking
`n = q`; the degree-zero map is the sheafification unit on a ph sheaf, hence
invertible. The torsion predicate is local and no common annihilator or
invertibility of torsion orders is used. -/
theorem isIso_phBigEtale_torsion_unit_and_isZero_rightDerived
    (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion)
    (q : ℕ) (hq : 0 < q) :
    IsIso ((phBigEtaleAbelianAdjunction T).unit.app
      ((bigSmallEtaleData T).morphism.inverse.obj F)) ∧
      IsZero (((phBigEtaleDirect T).rightDerived q).obj
        ((phBigEtaleInverse T).obj ((bigSmallEtaleData T).morphism.inverse.obj F))) := by
  sorry

end Scheme
end AlgebraicGeometry
