/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-!+# Ideals of flat closed families under arbitrary base change

Source: Stacks Project, Morphisms, Tags 02FV and 01TV; Algebra, Tag 00HL
(blueprint: lem-sfb-flat-closed-family-ideal-base-change).

The three helper maps are the induced closed-subfamily map, the pulled-back ideal
inclusion and the structure-sheaf quotient map. They use the existing fibre products,
ideal modules and tensor pullback; no replacement notion is introduced.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The induced map `Z ×[T] T' → X ×[T] T'` for the family `Z → X → T`.
Source: Stacks Project, Schemes, Tags 01JO and 01JU
(blueprint: lem-sfb-flat-closed-family-ideal-base-change). -/
def flatClosedFamilyBaseChangeImmersion {T X Z T' : Scheme.{u}}
    (f : X ⟶ T) (i : Z ⟶ X) (g : T' ⟶ T) :
    Limits.pullback (i ≫ f) g ⟶ Limits.pullback f g :=
  Limits.pullback.map (i ≫ f) g f g i (𝟙 T') (𝟙 T) (by simp) (by simp)

/-- Pull back the ideal inclusion and then identify the pulled-back structure sheaf
with the structure sheaf. The existing structure-sheaf comparison is the adjoint
of the ring map under the tensor-pullback adjunction.
Source: Stacks Project, Schemes, Tag 01I9; Modules, Tag 01CA
(blueprint: lem-sfb-flat-closed-family-ideal-base-change). -/
def flatClosedFamilyIdealBaseChangeMap {T X Z T' : Scheme.{u}}
    (f : X ⟶ T) (i : Z ⟶ X) (g : T' ⟶ T) :
    (tensorPullback (Limits.pullback.fst f g)).obj i.ker.toModules ⟶
      SheafOfModules.unit (Limits.pullback f g).ringCatSheaf :=
  (tensorPullback (Limits.pullback.fst f g)).map i.ker.toModulesι ≫
    tensorPullbackObjUnitToUnit (Limits.pullback.fst f g)

/-- The canonical quotient map `O_X' → i'_* O_Z'`, given on sections by the
structure-sheaf map of the induced morphism of fibre products.
Source: Stacks Project, Schemes, Tag 01JU
(blueprint: lem-sfb-flat-closed-family-ideal-base-change). -/
def flatClosedFamilyBaseChangeQuotient {T X Z T' : Scheme.{u}}
    (f : X ⟶ T) (i : Z ⟶ X) (g : T' ⟶ T) :
    SheafOfModules.unit (Limits.pullback f g).ringCatSheaf ⟶
      (pushforward (flatClosedFamilyBaseChangeImmersion f i g)).obj
        (SheafOfModules.unit (Limits.pullback (i ≫ f) g).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit
    (flatClosedFamilyBaseChangeImmersion f i g).toRingCatSheafHom

/-- A flat closed subfamily of finitely presented families has a finite-type ideal,
and its ideal sequence remains short exact after every base change. The final
isomorphism is canonical: its composite with the kernel inclusion is the specified
pulled-back ideal inclusion, which uniquely determines it.

Source: Stacks Project, Morphisms, Tag 02FV (lemma-finite-presentation-permanence),
Tag 01TV (lemma-closed-immersion-finite-presentation); Algebra, Tag 00HL
(lemma-flat-tor-zero)
(blueprint: lem-sfb-flat-closed-family-ideal-base-change).

Proof:
1. On affine charts over Spec R, write the closed immersion as A → B = A/J.
   The affine finite-presentation criterion and the intermediate finite-type
   algebra lemma show that B is finitely presented over A. Affine morphism
   permanence supplies quasi-compactness and quasi-separatedness of i.
2. The closed-immersion ideal description identifies the ideal with the module
   associated to J. The zero-variable presentation-kernel criterion shows J is
   finitely generated. The quasi-coherent finite-type affine criterion gives
   quasi-coherence and finite type of the ideal sheaf.
3. For any base change, the fibre-product universal property identifies Z' with
   Z ×[X] X'. The closed-subscheme ideal-image lemma identifies the new ideal as
   the image of the specified pulled-back inclusion. Affine pushforward base
   change and the structure-sheaf pullback comparison identify the last arrow
   with the displayed canonical quotient.
4. Cover X' by Spec(A ⊗[R] R') from compatible affine opens of X, T and T'.
   The flat affine-chart criterion makes B flat over R. The flat-quotient
   tensor-injectivity lemma, Tag 00HL, therefore makes
   0 → J ⊗[R] R' → A ⊗[R] R' → B ⊗[R] R' → 0 short exact.
5. The affine pullback-sections formula and its naturality identify the first
   arrow with the displayed inclusion, using the balanced isomorphism
   J ⊗[A] (A ⊗[R] R') ≅ J ⊗[R] R'. The affine fibre-product and open-fibre-product
   formulas identify the last arrow with the quotient on these charts.
6. Pullback and affine pushforward preserve quasi-coherence. Quasi-coherent
   affine-section base change and localization exactness give short exactness
   on every principal open in these charts. Principal opens form a basis, so
   the sheaf sequence is short exact. The injective inclusion identifies its
   source with the kernel; its uniquely determined inverse glues locally.
-/
theorem flatClosedFamily_ideal_baseChange {T X Z : Scheme.{u}}
    (f : X ⟶ T) (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation (i ≫ f)] [QuasiCompact (i ≫ f)]
    [QuasiSeparated (i ≫ f)] [Flat (i ≫ f)] :
    (LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i) ∧
      i.ker.toModules.IsQuasiCoherentFiniteType ∧
      ∀ (T' : Scheme.{u}) (g : T' ⟶ T),
        IsClosedImmersion (flatClosedFamilyBaseChangeImmersion f i g) ∧
        ∃ w : flatClosedFamilyIdealBaseChangeMap f i g ≫
            flatClosedFamilyBaseChangeQuotient f i g = 0,
          (ShortComplex.mk (flatClosedFamilyIdealBaseChangeMap f i g)
            (flatClosedFamilyBaseChangeQuotient f i g) w).ShortExact ∧
          ∃ e : (tensorPullback (Limits.pullback.fst f g)).obj i.ker.toModules ≅
              kernel (flatClosedFamilyBaseChangeQuotient f i g),
            e.hom ≫ kernel.ι (flatClosedFamilyBaseChangeQuotient f i g) =
              flatClosedFamilyIdealBaseChangeMap f i g := by
  sorry

end

end AlgebraicGeometry.Scheme.Modules
