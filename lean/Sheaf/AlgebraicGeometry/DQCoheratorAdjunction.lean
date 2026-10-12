/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration
import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
import Sheaf.AlgebraicGeometry.GlobalDerivedHom
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum
import Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint

/-! # Coherator adjunction and detection by global sections

Source: Stacks Project, Tag 0B6I, final paragraph of the proof, and Derived Categories
of Schemes, `perfect-lemma-better-coherator`
(blueprint: lem-pc-dq-coherator-adjunction).

Derived global sections are expressed by their K-injective representatives: applying
`RingedSpace.globalSectionsFunctor` termwise to a K-injective complex represents RΓ.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- The inclusion of the quasi-coherent derived full subcategory on a qcqs scheme
has a right adjoint. Its adjunction supplies the natural Hom bijection.
Source: Stacks Project, Tag 0B6I, final proof paragraph, and
`perfect-lemma-better-coherator` (blueprint: lem-pc-dq-coherator-adjunction).

Proof: compact generation (`lem-pc-derived-qcoh-compact-generation`) and coproducts
(`lem-pc-derived-qcoh-direct-sums`) hold for qcqs schemes. Ambient coproducts have
cohomology given by direct sums (`lem-pc-derived-ambient-direct-sums`). Finite sums
of quasi-coherent modules are quasi-coherent (`lem-weil-pbc-quasi-coherent-module-direct-sum`),
and their directed colimit is quasi-coherent
(`lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`). Thus ambient coproducts
lie in the full subcategory and are its coproducts, so inclusion preserves them.
The inherited triangles make inclusion exact. Brown representability
(`lem-pc-brown-representability-right-adjoint`) supplies the right adjoint. -/
theorem exists_dqCoheratorAdjunction (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ DQ_Y : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y,
      Nonempty (Adjunction (schemeDerivedQCohProperty Y).ι DQ_Y) := by
  sorry

/-- Any coherator right adjoint detects quasi-isomorphisms on derived global sections,
computed on K-injective representatives of the source and target.
Source: Stacks Project, Tag 0B6I, final proof paragraph
(blueprint: lem-pc-dq-coherator-adjunction).

Proof: global sections of a K-injective representative compute RΓ
(`def-pc-global-derived-rhom`). Degree-i cocycles are chain maps from O_Y[-i],
and coboundaries are null homotopies. The K-injective comparison
(`lem-sc-kinjective-quasi-iso-comparison`) identifies this cohomology with derived Hom.
The shift O_Y[-i] has quasi-coherent cohomology (`def-pc-derived-category`).
Adjunction identifies these groups with Hom into DQ_Y. An isomorphism after DQ_Y
therefore gives an isomorphism on each global cohomology group, which is precisely
quasi-isomorphism of the global-sections complexes. -/
theorem dqCoherator_detects_globalSections (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (DQ_Y : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y)
    (adj : (schemeDerivedQCohProperty Y).ι ⊣ DQ_Y)
    (I J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J)
    [IsIso (DQ_Y.map (DerivedCategory.Q.map f))] :
    QuasiIso (((RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  sorry

/-- Every shift O_Y[-i] is in the quasi-coherent full subcategory.
Source: Stacks Project, Tag 0B6I, final proof paragraph
(blueprint: lem-pc-dq-coherator-adjunction).

Proof: the shifted complex has only one nonzero cohomology sheaf, namely O_Y,
which is quasi-coherent; every other cohomology sheaf is zero and quasi-coherent.
Use `def-pc-derived-category` to conclude. -/
theorem structureSheaf_shift_is_derivedQCoh (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] (i : ℤ) :
    schemeDerivedQCohProperty Y
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦-i⟧) := by
  sorry

/-- Global degree-i cohomology of a K-injective representative is the derived Hom
from O_Y[-i], as an additive group.
Source: Stacks Project, Tag 0B6I, final proof paragraph
(blueprint: lem-pc-dq-coherator-adjunction).

Proof: a chain map from O_Y[-i] to I is an i-cocycle of global sections, and
homotopies correspond to i-coboundaries. Passage to the homotopy category gives
H^i(Γ(Y,I)). The K-injective comparison (`lem-sc-kinjective-quasi-iso-comparison`)
identifies these homotopy classes with morphisms in the derived category.
This identification is additive and natural in I. -/
theorem globalSections_homology_equiv_structureSheaf_shift (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [I.IsKInjective] (i : ℤ) :
    Nonempty
      (((((RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i) ≃+
        ((((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦-i⟧) ⟶
              DerivedCategory.Q.obj I)) := by
  sorry

end AlgebraicGeometry
