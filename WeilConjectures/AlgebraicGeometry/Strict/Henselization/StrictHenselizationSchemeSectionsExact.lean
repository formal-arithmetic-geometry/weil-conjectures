/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Exact sections on the affine-neighbourhood strict henselization

Source: Stacks Project, Tag 03QO.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Global sections on the spectrum of the pointed-neighbourhood colimit are exact.

Source: Stacks Project, Tag 03QO. -/
instance strictHenselizationScheme_globalSections_preservesFiniteColimits
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) := by
  obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure s
  let := hlocal
  let := hstrict
  let E := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have hE : ((sheafSections (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
        (op (Scheme.etaleTerminal (Scheme.strictHenselizationRing s)))).PreservesEpimorphisms := by
    exact Scheme.preservesEpimorphisms_sheafSections_of_isStrictlyHenselianLocalRing
      (Scheme.strictHenselizationRing s)
  have : E.PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{v + 1}
        (Scheme.isTerminalEtaleTerminal (Scheme.strictHenselizationRing s))).symm
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  exact E.preservesFiniteColimits_of_preservesHomology

end AlgebraicGeometry.Etale
