/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine

/-! # The finite graph of a prescribed formal comparison map

Source: Stacks Project, Tag 0889(1), formal gluing of comparison morphisms.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The discrepancy between the second projection and the prescribed formal map
at level n+1, on the pullback of the two comparison arrows. -/
noncomputable def torsionControlledGraphError
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) :
    pullback a.hom a'.hom ⟶ formalModuleQuotient J (n + 1) F'.obj :=
  let t : formalModuleQuotient J (n + 1) F.obj ⟶
      formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
  pullback.snd a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
    pullback.fst a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t

/-- The graph is a real kernel, retaining the chosen component of θ. -/
noncomputable def torsionControlledGraph
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) : X.Modules :=
  kernel (torsionControlledGraphError J a a' θ n)

/-- First projection from the finite graph. -/
noncomputable def torsionControlledGraphFst
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) :
    torsionControlledGraph J a a' θ n ⟶ F.obj :=
  kernel.ι (torsionControlledGraphError J a a' θ n) ≫ pullback.fst a.hom a'.hom

/-- Second projection from the finite graph. -/
noncomputable def torsionControlledGraphSnd
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) :
    torsionControlledGraph J a a' θ n ⟶ F'.obj :=
  kernel.ι (torsionControlledGraphError J a a' θ n) ≫ pullback.snd a.hom a'.hom

/-- The finite graph surjects onto F at every positive depth.
Source: Stacks Project, Tag 0889(1), affine comparison argument using Tag 05EK.
Proof: work on an affine open Spec(A), where all coherent sheaves give finite modules.
The graph is the kernel of the displayed discrepancy on F ×_H F'. Complete over A.
Completion is flat and exact for finite modules over the Noetherian ring A, so the
completed graph is this same kernel in the completed pullback. The map
x ↦ (x, θ(x)) lies in that kernel, by hθ and its level n+1 component; thus the
completed first projection is surjective. At a prime containing J, Nakayama applied
to its finite cokernel makes the original projection surjective. At a prime not
containing J, the power-torsion kernel and cokernel of a' vanish, so a' is an
isomorphism, the quotient at level n+1 is zero, and the graph projection is an
isomorphism. These two cases cover Spec(A). Local surjectivity is epimorphy of
sheaves, giving the global assertion. The zero ideal makes the graph the usual
graph of θ; the unit ideal makes a' an isomorphism. Zero modules and the empty
scheme cause no exception.
(blueprint: lem-weil-pbc-torsion-controlled-finite-graph-epi). -/
theorem torsionControlledGraphFst_epi
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) : Epi (torsionControlledGraphFst J a a' θ n) := by sorry

end AlgebraicGeometry
