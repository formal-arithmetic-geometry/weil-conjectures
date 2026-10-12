/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import Sheaf.Algebra.Homology.KFlatModuleBaseChange
import Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso

/-! # K-flatness under open restriction

Source: Stacks Project, Tag 06YB, applied to open restriction.
(blueprint: lem-pc-kflat-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Open restriction preserves K-flat complexes of module sheaves.
Source: Stacks Project, Cohomology, Tag 06YB, lemma-check-K-flat-stalks.
(blueprint: lem-pc-kflat-open-restriction).

Proof: apply the stalk criterion for K-flatness to K. For each point x of X,
restriction has the same module stalk as K at j(x), with scalars transported by the
isomorphism of local rings induced by the open immersion. The comparison is natural
in module maps, so it identifies the stalk complexes including their differentials.
Extension and restriction of scalars along a ring isomorphism are inverse exact
monoidal equivalences: they preserve acyclic complexes and identify total tensor
complexes degree by degree, including every coproduct in an unbounded totalization.
Thus the K-flat stalk at j(x) gives a K-flat stalk of the restricted complex at x.
The reverse implication of the stalk criterion proves the result. On an empty X
the criterion is vacuous; neither quasi-coherence nor boundedness is needed. -/
theorem isKFlat_restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K) :
    CochainComplex.IsKFlat (R := X.sheaf)
      (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K) := by
  have hstalk :=
    (RingedSpace.isKFlat_iff_stalk_isKFlat Y.toRingedSpace K).mp hK
  apply (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace _).mpr
  intro x F hF
  obtain ⟨e⟩ := nonempty_restriction_stalk_extension_iso j x K
  have h := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat
    (j.stalkMap x).hom _ (hstalk (j x)) F hF
  let T := ((MonoidalCategory.curriedTensor
    (ModuleCat.{u} (X.presheaf.stalk x))).map₂CochainComplex).obj F
  intro i
  exact (h i).of_iso (T.mapIso e)

end AlgebraicGeometry
