/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHom
import WeilConjectures.AlgebraicGeometry.FormalFunctionsCompleteBase
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FormalCompletionMapInjectiveProper
import WeilConjectures.AlgebraicGeometry.FormalCompletionMapSurjectiveProper

/-! # Fully faithful completion over a complete proper base

Source: Stacks Project, Cohomology of Schemes, Lemma 0883.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Completion induces a bijection on morphisms between coherent modules on a proper
scheme over an adically complete Noetherian ring. The ideal of completion is I O_X:
transport I to global sections of Spec A, form its ideal sheaf, and extend it along f.
Noetherianity of X is derived from the proper morphism, not assumed separately.
Source: Stacks Project, Cohomology of Schemes, Lemma 0883.

Proof:
1. Spec A is Noetherian, and properness makes f finite type, so X is Noetherian. The extended ideal I O_X is quasi-coherent:
   pull back the quasi-coherent ideal on Spec A and take its image.
2. The internal Hom H = Hom(G,F) is coherent, and its global sections are Hom(G,F).
3. Lemma 0882 identifies the inverse limit of
   global sections of H/I^n H with morphisms of the completed modules.
4. Formal functions in degree zero over the complete base identifies global sections of H with
   that inverse limit, by reduction modulo I^n.
5. The composite of these bijections sends u to its compatible family of reductions:
   evaluation of the reduced internal-Hom section is precisely u modulo I^n.
   Thus the composite is the map of def-weil-pbc-coherent-formal-module's completion
   functor, proving its bijectivity for every coherent G and F. -/
theorem formalCompletion_map_bijective_of_proper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (G F : CoherentModules X) :
    Function.Bijective
      (fun v : G ⟶ F ↦
        (@completion X (isNoetherian_of_locallyOfFiniteType f)
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)).map v) := by
  exact ⟨formalCompletion_map_injective_of_proper I f G F,
    formalCompletion_map_surjective_of_proper I f G F⟩

end AlgebraicGeometry
