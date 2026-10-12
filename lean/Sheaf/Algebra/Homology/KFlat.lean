/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# K-flat complexes of modules on a ringed site

Source: the blueprint of the Weil conjectures, chapter `sec-picard-framework`, unit
`sk-thm-picard-semicon` (blueprint: def-pc-kflat-complex); Stacks Project, Cohomology on Sites,
Definition `sites-cohomology-definition-K-flat` (Tag 06YN), and the term "K-flat resolution" as
used in Lemma `sites-cohomology-lemma-K-flat-resolution` (Tag 06YS).

Let `R` be a sheaf of commutative rings on a site `(C, J)`. Sheaves of modules over `R` carry the
monoidal structure `SheafOfModules.monoidalCategory R` (the tensor product is the sheafification
of the tensor product of presheaves of modules); it is not an instance and is used here with
`letI`. The total tensor complex `Tot(F ⊗ K)` of two cochain complexes is
`CochainComplex.mapBifunctor F K (curriedTensor _)`.

## Main definitions

- `CochainComplex.IsKFlat`: a complex `K` of `R`-modules is K-flat if `Tot(F ⊗ K)` is acyclic
  for every acyclic complex `F` of `R`-modules.
- `CochainComplex.IsKFlatResolution`: a morphism `K ⟶ G` is a K-flat resolution of `G` if it is
  a quasi-isomorphism and `K` is K-flat.

## Main statements

- `SheafOfModules.preservesZeroMorphisms_curriedTensor`,
  `SheafOfModules.preservesZeroMorphisms_curriedTensor_obj`: the tensor product of sheaves of
  modules preserves zero morphisms in each variable (needed to form the total tensor complex).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

/-- The tensor localization is monoidal also when the site's morphisms live in a
separate universe. Source: Stacks Project, Modules on Sites, Section 03EK;
Cohomology on Sites, Definition 06YN (blueprint: def-pc-kflat-complex).

Proof: use the sectionwise tensor/internal-Hom adjunction for presheaves of modules.
For a sheaf N the internal Hom into N is a sheaf. Thus tensoring a locally bijective
map induces bijections on morphisms into all sheaves, so its sheafification is an
isomorphism. Symmetry gives the same assertion in the other variable. This argument
is the proof of SheafOfModules.isMonoidal_W and does not require equal hom universes. -/
@[instance]
theorem isMonoidal_W_separateHomUniverse :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{max u v}
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).obj)).IsMonoidal :=
  sorry

/-- (blueprint: def-pc-kflat-complex) The tensor product of sheaves of modules over a sheaf of
commutative rings `R` (`SheafOfModules.monoidalCategory R`) preserves zero morphisms in the first
variable: `0 ▷ M = 0`. Needed to form the total tensor complex of Stacks, Tag 06YN.

Proof: `M ↦ - ⊗ M` is, up to the counit isomorphism of sheafification, sheafification of the
tensor product of presheaves of modules, which is computed sectionwise in `ModuleCat`, where it
is additive (`MonoidalPreadditive (ModuleCat _)`); sheafification is a left adjoint, hence
preserves zero morphisms. -/
@[instance]
theorem preservesZeroMorphisms_curriedTensor :
    letI := monoidalCategory R
    (curriedTensor (SheafOfModules.{max u v}
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))).PreservesZeroMorphisms :=
  sorry

/-- (blueprint: def-pc-kflat-complex) The tensor product of sheaves of modules over a sheaf of
commutative rings `R` (`SheafOfModules.monoidalCategory R`) preserves zero morphisms in the
second variable: `M ◁ 0 = 0`. Needed to form the total tensor complex of Stacks, Tag 06YN.

Proof: as for `SheafOfModules.preservesZeroMorphisms_curriedTensor`, or from it by the symmetry
`SheafOfModules.symmetricCategory R`. -/
@[instance]
theorem preservesZeroMorphisms_curriedTensor_obj
    (M : SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :
    letI := monoidalCategory R
    ((curriedTensor (SheafOfModules.{max u v}
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))).obj
        M).PreservesZeroMorphisms :=
  by
    let := monoidalCategory R
    let := symmetricCategory R
    refine ⟨fun X Y ↦ ?_⟩
    change M ◁ (0 : X ⟶ Y) = 0
    have h : (0 : X ⟶ Y) ▷ M = 0 :=
      congrArg (fun t ↦ t.app M) ((curriedTensor _).map_zero X Y)
    apply (cancel_mono (β_ M Y).hom).1
    rw [BraidedCategory.braiding_naturality_right, h, comp_zero, zero_comp]

end SheafOfModules

namespace CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max u v}}

-- The `max u v` module universe makes the `HasMapBifunctor` instance term exceed the default
-- `synthInstance.maxSize` of 128.
set_option synthInstance.maxSize 256 in
/-- (blueprint: def-pc-kflat-complex) Let `R` be a sheaf of commutative rings on a site `(C, J)`.
A cochain complex `K` of sheaves of `R`-modules is *K-flat* if for every acyclic complex `F` of
`R`-modules (all cohomology sheaves vanish, `F.Acyclic`) the total tensor complex
`Tot(F ⊗_R K) = mapBifunctor F K (curriedTensor _)` is acyclic (Stacks, Tag 06YN). The tensor
product is `SheafOfModules.monoidalCategory R`. This differs from the source's
`CochainComplex.KFlat` (`FromJoel`: tensoring on both sides preserves quasi-isomorphisms, for a
monoidal preadditive abelian category), which is a different name and a different notion. -/
def IsKFlat
    (K : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    Prop :=
  letI := SheafOfModules.monoidalCategory R
  ∀ F : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ,
    F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic

/-- (blueprint: def-pc-kflat-complex) Let `R` be a sheaf of commutative rings on a site `(C, J)`.
A *K-flat resolution* of a cochain complex `G` of sheaves of `R`-modules is a quasi-isomorphism
`f : K ⟶ G` of complexes of `R`-modules with `K` K-flat (`CochainComplex.IsKFlat`); Stacks,
Tag 06YN, the term as used in Tag 06YS. -/
def IsKFlatResolution
    {K G : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (f : K ⟶ G) : Prop :=
  QuasiIso f ∧ K.IsKFlat

end CochainComplex
