/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.TopBaseChangePresheaf
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.AffineOpenHigherDirectImageSectionsIso
import WeilConjectures.AlgebraicGeometry.AffineResolutionSectionBijective
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum
import WeilConjectures.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Universal top-degree base change and tensor projection

Source: Stacks Project, Limits, Tag 0EX3, lemma-top-cohomology-functor,
including the explanation of the canonical map before the proof
(blueprint: lem-sfb-top-degree-base-change).

The tensor comparison is characterized on local cocycle classes. The base-change
comparison is the ordinary adjoint of the existing normalized topBaseChangeAdjoint.
The reversed order of pullback arguments agrees with that existing construction.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

/-- The coefficient map s ↦ s ⊗ f* m on the inverse image of an open U.
Its target is the restriction of the global tensor product, using the existing
section-normalized tensor pullback and restriction tensor comparison.
Source: Stacks Project, Tag 0EX3, proof of (b)
(blueprint: lem-sfb-top-degree-base-change). -/
def topDegreeTensorSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    F.restrict (f ⁻¹ᵁ U).ι ⟶
      (F ⊗ (tensorPullback f).obj M).restrict (f ⁻¹ᵁ U).ι :=
  (ρ_ (F.restrict (f ⁻¹ᵁ U).ι)).inv ≫
    (F.restrict (f ⁻¹ᵁ U).ι) ◁
      homOfGlobalSection (((tensorPullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
        ((((tensorPullback f).obj M).restrictAppIso (f ⁻¹ᵁ U).ι ⊤).inv
          (((tensorPullback f).obj M).presheaf.map
            (eqToHom (f ⁻¹ᵁ U).ι_image_top).op (tensorPullbackSection f M U m))) ≫
    (openRestrictionTensorIso (f ⁻¹ᵁ U).ι F ((tensorPullback f).obj M)).inv

/-- A tensor projection is canonical when it sends every local cocycle class x tensor m
to the class obtained by applying cohomology to s ↦ s tensor f* m. This condition
specifies the map on the presheaf generating the higher-image sheaf, and pure tensors
generate the tensor sheaf; it therefore specifies a unique map, rather than an
unspecified isomorphism between the same objects.
Source: Stacks Project, Tag 0EX3, proof of (b)
(blueprint: lem-sfb-top-degree-base-change). -/
def IsTopDegreeTensorProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (M : Y.Modules) (d : ℕ)
    (φ : (((pushforward f).rightDerived d).obj F) ⊗ M ⟶
      ((pushforward f).rightDerived d).obj (F ⊗ (tensorPullback f).obj M)) : Prop :=
  ∀ (U : Y.Opens) (I : InjectiveResolution F)
    (J : InjectiveResolution (F ⊗ (tensorPullback f).obj M))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ U))
    (R' : RestrictedResolutionSections J (f ⁻¹ᵁ U))
    (x : (RingedSpace.moduleCohomology (f ⁻¹ᵁ U).toScheme.toRingedSpace d).obj
      (F.restrict (f ⁻¹ᵁ U).ι)) (m : Γ(M, U)),
    Hom.app φ U (tmulSection (topBaseChangeClass f F I U (f ⁻¹ᵁ U) rfl R d x) m) =
      topBaseChangeClass f (F ⊗ (tensorPullback f).obj M) J U (f ⁻¹ᵁ U) rfl R' d
        ((RingedSpace.moduleCohomology (f ⁻¹ᵁ U).toScheme.toRingedSpace d).map
          (topDegreeTensorSection f F M U m) x)

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical degree-d ordinary base-change map γ, namely the ordinary adjoint of
the existing map whose formula is H^d(δ) κ⁻¹ with the canonical total/classical
comparisons. Thus no arbitrary comparison is chosen.
Source: Stacks Project, Tag 0EX3, explanation of (c) before the proof
(blueprint: lem-sfb-top-degree-base-change). -/
def topDegreeOrdinaryBaseChange {X Y T : Scheme.{u}} (f : X ⟶ Y) (c : T ⟶ Y)
    (F : X.Modules) (d : ℕ)
    (hC : ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).IsLE (d : ℤ)) :
    (tensorPullback c).obj (((pushforward f).rightDerived d).obj F) ⟶
      ((pushforward (pullback.fst c f)).rightDerived d).obj
        ((tensorPullback (pullback.snd c f)).obj F) :=
  ((tensorPullbackSectionAdjunction c).homEquiv _ _).symm
    (topBaseChangeAdjoint f c F d hC)

/-- Universal vanishing, canonical tensor projection, and canonical further base change
in the highest possibly nonzero degree, for every quasi-coherent module after base change.
Source: Stacks Project, Tag 0EX3, lemma-top-cohomology-functor, (a)--(c)
(blueprint: lem-sfb-top-degree-base-change).

Proof:
1. The qcqs permanence lemma makes f and its base changes qcqs. Restrict to affine
base opens. Quasi-coherent extension from a quasi-compact open, with ambient module
zero, and higher-image open restriction transfer the vanishing hypothesis to these
restrictions (lem-weil-pbc-quasi-coherent-extension-qc-open and
lem-pc-higher-direct-image-open-restriction).
2. Over affine bases both base-change projections are affine. Affine pushforward
preserves quasi-coherence. The affine cohomology edge and affine higher-image section
comparison reduce (a) to the assumed vanishing. Higher images are quasi-coherent,
and the affine tilde/global-section equivalence detects zero objects.
3. For (b), over Spec R consider N ↦ H^d(X', F ⊗ f'* tilde N). Pullback, tilde and
tensor are right exact and preserve quasi-coherence. For an exact three-term sequence,
the two kernels are quasi-coherent; their long exact sequences and (a) give right
exactness of this functor, including d = 0.
4. Tilde, pullback, and tensor preserve sums by their adjunctions; qcqs cohomology
commutes with sums. Apply lem-sfb-linear-right-exact-module-functor-tensor. Its map
x tensor m ↦ H^d(s ↦ s tensor f'*m)(x) is precisely the displayed cocycle-class
normalization, using lem-pc-affine-resolution-section-bijective and the affine tensor
section formula. The affine tilde equivalence detects its invertibility. Glue locally.
5. For (c), on affine bases p = c_X is affine. Affine chart tensor formulas identify
p_*p*F with F tensor f'*tilde B and identify the unit with n ↦ n tensor 1.
6. The affine cohomology edge and (b) give H^d(X'',p*F) = H^d(X',F) tensor B.
The forward map sends x tensor b to b times the cohomology of the pullback unit,
by the preceding unit normalization and B-linearity.
7. Vanishing above d gives the total-derived upper bound recorded in hC. Apply
lem-weil-pbc-derived-pullback-top-cohomology. By its construction the displayed γ is
H^d(δ) κ⁻¹. The theorem lem-weil-pbc-top-base-change-presheaf identifies its adjoint
on local cocycle classes with the ordinary cohomology pullback unit.
8. Over affine opens both cocycle class maps are bijective by
lem-pc-affine-resolution-section-bijective. The affine pullback formula identifies
sections of γ with the map of step 6; hence γ is invertible. Quasi-coherence and the
affine tilde equivalence give the sheaf assertion. Restriction to opens gives the
claim for arbitrary bases and further morphisms, without flatness assumptions. -/
theorem topDegree_base_change {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (d : ℕ)
    (hvan : ∀ (F : X.Modules), F.IsQuasicoherent →
      ∀ i : ℕ, d < i → IsZero (((pushforward f).rightDerived i).obj F)) :
    ∀ (Y' : Scheme.{u}) (b : Y' ⟶ Y),
      (∀ (F : (pullback b f).Modules), F.IsQuasicoherent →
        ∀ i : ℕ, d < i →
          IsZero (((pushforward (pullback.fst b f)).rightDerived i).obj F)) ∧
      (∀ (F : (pullback b f).Modules), F.IsQuasicoherent →
        ∀ (M : Y'.Modules), M.IsQuasicoherent →
          ∃ φ : (((pushforward (pullback.fst b f)).rightDerived d).obj F) ⊗ M ⟶
            ((pushforward (pullback.fst b f)).rightDerived d).obj
              (F ⊗ (tensorPullback (pullback.fst b f)).obj M),
            IsTopDegreeTensorProjection (pullback.fst b f) F M d φ ∧ IsIso φ) ∧
      (∀ (F : (pullback b f).Modules), F.IsQuasicoherent →
        ∃ hC : ((schemeDerivedDirectImage (pullback.fst b f)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback b f).toRingedSpace)) 0).obj F)).IsLE
              (d : ℤ),
          ∀ (Y'' : Scheme.{u}) (c : Y'' ⟶ Y'),
            IsIso (topDegreeOrdinaryBaseChange (pullback.fst b f) c F d hC)) := by
  sorry

end AlgebraicGeometry
