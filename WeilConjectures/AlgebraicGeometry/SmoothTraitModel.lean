/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-! # Smooth models over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 4.3, printed pp.103--104
(blueprint: def-sfb-smooth-trait-model).

## Main definitions

- `SmoothTraitModel`: the model and its generic identification.
- `SmoothTraitModel.genericInclusion`, `stalkScalar`: canonical structural maps.
- `traitStrictBase`: the landed strict-henselization structural morphism.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- A smooth separated finite-type model with a specified generic-fibre identification.
Source: BLR 4.3, printed p.104 (blueprint: def-sfb-smooth-trait-model). -/
structure SmoothTraitModel {R E : Type u} [CommRing R] [Field E] [Algebra R E]
    (G : Over (Spec (.of E))) where
  scheme : Scheme.{u}
  hom : scheme ⟶ Spec (.of R)
  smooth : Smooth hom
  separated : IsSeparated hom
  finiteType : LocallyOfFiniteType hom
  quasiCompact : QuasiCompact hom
  genericIso : Over.mk (pullback.snd hom (Spec.map (CommRingCat.ofHom (algebraMap R E)))) ≅ G

namespace SmoothTraitModel
variable {R E : Type u} [CommRing R] [Field E] [Algebra R E]
variable {G : Over (Spec (.of E))}

/-- The generic-fibre inclusion, using the specified identification with G.
Source: BLR 4.3, printed p.104 (blueprint: def-sfb-smooth-trait-model). -/
noncomputable def genericInclusion (M : SmoothTraitModel (R := R) G) : G.left ⟶ M.scheme :=
  M.genericIso.inv.left ≫ pullback.fst M.hom (Spec.map (CommRingCat.ofHom (algebraMap R E)))

/-- Scalars in a model's local ring, through its structural morphism.
Source: BLR 4.3 order construction, printed p.104
(blueprint: def-sfb-smooth-trait-model). -/
noncomputable def stalkScalar (M : SmoothTraitModel (R := R) G) (z : M.scheme) :
    R →+* M.scheme.presheaf.stalk z :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ M.hom.appTop ≫
    M.scheme.presheaf.germ ⊤ z trivial).hom

end SmoothTraitModel

/-- The canonical map from the strict henselization to the base: the landed structural
morphism `Scheme.strictHenselizationStructuralMap` of
def-weil-pbc-strict-henselization-structural-map, not a second construction.
Source: BLR 2.3 and 4.3; Stacks 03Q9
(blueprint: def-sfb-smooth-trait-model). -/
noncomputable abbrev traitStrictBase {R : Type u} [CommRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of R)) :
    Scheme.strictHenselizationScheme s ⟶ Spec (.of R) :=
  Scheme.strictHenselizationStructuralMap s

end AlgebraicGeometry
