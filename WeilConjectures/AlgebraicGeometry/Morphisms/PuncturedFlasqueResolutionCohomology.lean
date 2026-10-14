/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionComparison
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Flasque associated-module resolutions compute cohomology on an open

Source: Stacks Project, Tags 09T2 and 0A6T.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The sections complex of an associated injective-module resolution computes the
cohomology of the structure sheaf on any open of a Noetherian affine scheme.
Source: Stacks Project, Tag 09T2, Lemma 36.8.1, and Tag 0A6T, Lemma 51.2.1.
(blueprint: lem-sbc-punctured-flasque-resolution-cohomology).

Proof: Localizing an exact sequence of modules is exact. Therefore the associated
sheaves of the resolution I form an exact resolution of the unit structure module
on Spec R; the augmentation uses tildeSelf. Restriction to W preserves exactness
(stalks are unchanged). Every I.X k is injective, and its associated sheaf is
flasque on the Noetherian affine scheme by 09T2. Restriction of a flasque sheaf
remains flasque, hence is acyclic for sections. The acyclic-resolution comparison
computes sheaf cohomology from the complex of sections. Sections of the restricted
associated sheaf are precisely evaluation of modulesSpecToSheaf on W, which is
the concrete puncturedSectionsComplex. The underlying additive sheaf of the unit
module gives Modules.H. This includes degree zero. On the empty open each sections
module and the structure sheaf cohomology vanish, and the same comparison holds. -/
theorem nonempty_open_h_addEquiv_injective_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (W : (Spec (.of R)).Opens)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) (n : ℕ) :
    Nonempty (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) n ≃+
      ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier) := by
  obtain ⟨f, g, hgf, hfg⟩ := punctured_flasque_resolution_comparison_maps R W I n
  let e : Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) n ≃+
      ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := hgf
          right_inv := hfg }
      map_add' := f.map_add }
  exact ⟨e⟩

end AlgebraicGeometry.Scheme
