/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantCounit
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantStalk

/-!
# Etale sheaves on an algebraically closed spectrum are constant

Source: literature/stacks-project/etale-cohomology.tex, Remark 59.23.2 (Tag 03P5),
together with Lemma 59.39.3 (Tag 0A3H).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every set-valued sheaf on the small etale site of an algebraically closed field
is canonically constant, and its global sections identify with its identity geometric stalk.
Source: Stacks Project, Remark 59.23.2 (Tag 03P5), together with Lemma 59.39.3 (Tag 0A3H). -/
theorem spec_algClosed_etale_sheaf_constant
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf ((Spec (CommRingCat.of Ω)).smallEtaleTopology) (Type (u + 1))) :
    IsIso ((constantSheafAdj (Spec (CommRingCat.of Ω)).smallEtaleTopology
      (Type (u + 1)) terminalIsTerminal).counit.app G) ∧
      Function.Bijective
        ((pointSmallEtale (𝟙 (Spec (CommRingCat.of Ω)))).toPresheafFiber
          (Etale.mk (𝟙 (Spec (CommRingCat.of Ω))))
          (Over.homMk (𝟙 (Spec (CommRingCat.of Ω)))
            (Category.comp_id (𝟙 (Spec (CommRingCat.of Ω))))) G.obj) := by
  exact ⟨spec_algClosed_etale_sheaf_constant_counit Ω G,
    spec_algClosed_etale_sheaf_constant_stalk Ω G⟩

end AlgebraicGeometry.Scheme
