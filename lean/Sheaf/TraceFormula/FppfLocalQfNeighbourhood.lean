/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.CompositeFibreLocalModels
import Sheaf.AlgebraicGeometry.FibreCohenMacaulayLocus
import Sheaf.AlgebraicGeometry.Morphisms.CohenMacaulayClosedPointSlice
import Sheaf.TraceFormula.FlatLFPCMLocusFibreDense

/-!
# Flat locally finitely presented quasi-finite neighbourhoods

Source: Stacks Project, More on Morphisms, Tag 0571, lemma-qf-fp-flat-neighbourhood-dominates-fppf
(blueprint: lem-trf-fppf-local-qf-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Stacks Project, More on Morphisms, Tag 0571, lemma-qf-fp-flat-neighbourhood-dominates-fppf
(blueprint: lem-trf-fppf-local-qf-neighbourhood).

For a flat, locally finitely presented morphism and a point in its image, there is a
flat, locally finitely presented, locally quasi-finite morphism through that point.
The proof first selects a closed Cohen--Macaulay point in the nonempty fibre and then
applies the Cohen--Macaulay flat quasi-finite slice lemma (Tag 0570), finally using the
composite and the chosen fibre point to establish the image clause.
-/
theorem exists_flat_lfp_locallyQuasiFinite_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S) (hs : s ∈ Set.range f) :
    ∃ (S' : Scheme.{u}) (h : S' ⟶ X) (g : S' ⟶ S),
      h ≫ f = g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
        Scheme.Hom.IsLocallyQuasiFinite g ∧ s ∈ Set.range g := by
  sorry

end AlgebraicGeometry
