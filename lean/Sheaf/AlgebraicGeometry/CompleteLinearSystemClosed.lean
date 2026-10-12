/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.Paper.EulerCharacteristicWellDefined
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The complete linear system of a closed-immersion subsystem

Source: Stacks Project, Constructions, Lemma 01NE and Definition 01NF; Morphisms, Lemmas 07RK
and 01W6; the projection argument in `lem-pc-very-ample-ample`
(blueprint: lem-pc-complete-linear-system-closed).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite-dimensional subsystem whose associated morphism is a closed immersion forces the
complete linear system to give a closed immersion, pulling back `O(1)` to the same module.
The subsystem `V` is given by a `k`-basis: a linearly independent finite family `s` of global
sections (`V` is its span); "associated morphism" is
`ProjectiveSpace.homOfGeneratingSections` of the family over `Spec k`
(def-weil-pbc-morphism-to-projective-space-by-sections), which needs `s` to generate `M`.
The complete linear system is a finite family `t` of global sections that is a `k`-basis of
`Γ(M, ⊤)`; its existence includes finite-dimensionality of `Γ(M, ⊤)`. The `k`-action on
`Γ(M, ⊤)` is restriction of scalars along `Scheme.globalSectionsRingHom`, as for `M.H n`.
Empty index types are allowed (the empty scheme has zero sections).

Source: Stacks Project, Constructions, Lemma 01NE and Definition 01NF; Morphisms, Lemmas 07RK
and 01W6 (blueprint: lem-pc-complete-linear-system-closed).

Proof:
1. The empty scheme has zero global sections and the unique closed immersion to the empty
   projective space. Otherwise properness gives finite type over a Noetherian field spectrum
   (`lem-weil-pbc-finite-type-over-noetherian`). The invertible module is quasi-coherent and
   locally free of rank one, hence coherent (`pqf-lem-coherent-ft-locnoeth`). Its global
   sections are finite-dimensional (`lem-pc-euler-characteristic-well-defined`, degree zero).
2. Extend the basis `s` of V to a basis `t` of Γ(M). The subsystem generates M, so does the
   extended family; `homOfGeneratingSections` gives φ and (01NE,
   `lem-weil-pbc-projective-space-functor-of-points`) its pullback isomorphism.
3. Let U be the union of standard opens for the coordinates of V
   (`lem-weil-pbc-projective-space-standard-charts`). These coordinates generate O(1) on U,
   so 01NE gives the projection p to P(Vᵛ). Generation on X makes φ factor through U;
   uniqueness in 01NE gives φ ≫ p = j by matching the pulled-back coordinate sections.
4. Projective space is separated (`lem-weil-pbc-projective-space-proj-separated`), hence U
   is separated over k. Cancellation (`lem-weil-pbc-separated-cancellation`) makes p
   separated. Closed-immersion cancellation (`lem-weil-pbc-closed-immersion-cancellation`,
   07RK(3)) makes X → U closed, so φ is an immersion. Properness of X and separatedness of
   projective space make φ proper (`lem-weil-pbc-proper-to-separated`). A proper immersion
   is closed (`lem-weil-pbc-proper-immersion-closed`). The pullback isomorphism is from step 2. -/
theorem completeLinearSystem_isClosedImmersion
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (M : X.Modules) [M.IsInvertible] :
    letI : Module k Γ(M, ⊤) :=
      Module.compHom Γ(M, ⊤) (Scheme.globalSectionsRingHom k (X := X))
    ∀ (I : Type u) [Finite I] (s : I → M.sections) (hs : Epi (M.freeHomEquiv.symm s)),
      LinearIndependent (M := Γ(M, ⊤)) k (fun i ↦ (s i).val (Opposite.op ⊤)) →
      IsClosedImmersion
        (ProjectiveSpace.homOfGeneratingSections I (X ↘ Spec (.of k)) M s hs) →
      Nonempty ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.homOfGeneratingSections I (X ↘ Spec (.of k)) M s hs)).obj
            (ProjectiveSpace.twist I (Spec (.of k)) 1) ≅ M) →
      ∃ (J : Type u) (_ : Finite J) (t : J → M.sections) (ht : Epi (M.freeHomEquiv.symm t)),
        LinearIndependent (M := Γ(M, ⊤)) k (fun j ↦ (t j).val (Opposite.op ⊤)) ∧
        Submodule.span k (Set.range fun j ↦ (t j).val (Opposite.op ⊤) : Set Γ(M, ⊤)) = ⊤ ∧
        IsClosedImmersion
          (ProjectiveSpace.homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht) ∧
        Nonempty ((Scheme.Modules.tensorPullback
            (ProjectiveSpace.homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht)).obj
              (ProjectiveSpace.twist J (Spec (.of k)) 1) ≅ M) := by
  sorry

end AlgebraicGeometry
