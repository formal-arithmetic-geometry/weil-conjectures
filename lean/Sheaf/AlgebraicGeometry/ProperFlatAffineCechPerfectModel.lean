/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

import Sheaf.AlgebraicGeometry.FiniteAffineCechModelFlatOver
import Sheaf.AlgebraicGeometry.FiniteAffineCechModelComparison
import Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect

/-! # A perfect nonnegative flat cohomology model on a specified affine open -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a specified affine base open, an alternating affine Cech model of a proper
relatively flat finitely presented sheaf is bounded, nonnegative and termwise flat,
and represents a perfect object. Its terms need not be finitely presented.
Source: Stacks Project, Tags 01XB, 0A1D and 0B91(2), and the proof of Tag 0A1H.
(blueprint: lem-pc-proper-flat-affine-cech-perfect-model).

Proof: Restrict f and F to U by the standard cartesian square. Quasi-compactness
provides a finite affine cover of f inverse U. Separatedness makes its finite
intersections affine. Form the alternating complex of section modules indexed by
strictly increasing tuples and associate sheaves over U. Negative terms are zero
and terms above the size of the cover are zero. Relative flatness makes every
section module flat over Gamma(U,O); finite sums and associated sheaves preserve
this, and the terms are quasi-coherent. Affine acyclicity (01XB) and Cech comparison
identify the derived object with the restricted derived direct image of F.
Tag 0B91(2), whose approximation proof is Tag 0A1H, makes that object perfect.
For an affine new base the sections on each pulled-back intersection are tensor
products over the base ring. The entire alternating differential base-changes,
so affine acyclicity identifies its homology with the higher direct images after
base change. Restricting to affine opens of an arbitrary new base gives compatible
identifications from the same augmentation, which glue as sheaf isomorphisms.
Equivalently use Tag 0A1D and the bounded flat derived-pullback comparison.
Transport from the standard fibre product to any supplied cartesian square by
its unique isomorphism. No termwise finite-presentation assertion is made for the
Cech section modules. An empty inverse image uses the zero complex with d = 0.
The model is asserted existentially, not defined from an unproved choice. -/
theorem exists_proper_flat_affine_cech_perfect_model
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    ∃ (D : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE d ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      U.toScheme.IsPerfect ((DerivedCategory.Q
        (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))).obj D) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  classical
  have : IsAffine U.toScheme := hU
  have hUopen : IsAffineOpen U := hU
  let Y := (f ⁻¹ᵁ U).toScheme
  have : CompactSpace Y :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hUopen.isCompact)
  let cover := Y.affineCover.finiteSubcover
  let r := Fintype.card cover.I₀
  let index : Fin r ≃ cover.I₀ := (Fintype.equivFin cover.I₀).symm
  let V : Fin r → Y.Opens := fun i ↦ (cover.f (index i)).opensRange
  have hcover : iSup V = ⊤ := by
    simpa [V] using (index.iSup_comp (g := fun i ↦ (cover.f i).opensRange)).trans
      cover.iSup_opensRange
  have hV : ∀ i, IsAffineOpen (V i) := fun i ↦
    isAffineOpen_opensRange (cover.f (index i))
  let G := F.restrict (f ⁻¹ᵁ U).ι
  let C := finiteAffineCechModel (f ∣_ U) G V
  have hflat : G.IsFlatOver (f ∣_ U) := by
    intro V0 U0 e
    let V1 : T.affineOpens := ⟨U.ι ''ᵁ V0.1, V0.2.image_of_isOpenImmersion U.ι⟩
    let U1 : X.affineOpens :=
      ⟨(f ⁻¹ᵁ U).ι ''ᵁ U0.1, U0.2.image_of_isOpenImmersion (f ⁻¹ᵁ U).ι⟩
    have e1 : U1.1 ≤ f ⁻¹ᵁ V1.1 :=
      ((f ⁻¹ᵁ U).ι.image_mono e).trans (image_morphismRestrict_preimage f U V0.1).le
    have hh := hF V1 U1 e1
    rw [morphismRestrict_appLE]
    convert hh using 1 <;> try rfl
    ext a m
    change (F.smul (((f ⁻¹ᵁ U).ι.appIso U0.1).inv.hom
      ((f.appLE V1.1 U1.1 e1).hom a))).hom m =
        (F.smul ((f.appLE V1.1 U1.1 e1).hom a)).hom m
    rw [Scheme.Opens.ι_appIso]
    rfl
  refine ⟨C, r, finiteAffineCechModel_ge _ _ _, finiteAffineCechModel_le _ _ _,
    finiteAffineCechModel_flatOver _ _ hflat V hV,
    finiteAffineCechModel_quasicoherent _ _ _, ?_, ?_⟩
  · exact finiteAffineCechModel_perfect f F hF U hU V hV hcover
  · exact finiteAffineCechModel_comparison f F U hU V hV hcover

end AlgebraicGeometry.Scheme.Modules
