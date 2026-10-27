/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.SeparatingPairOpen
import Sheaf.AlgebraicGeometry.AmpleFibreSectionLifting
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.FractionFieldSectionsBaseChange

/-! # Simultaneous special and generic norm-pair interpolation

Source: de Jong, Families of curves and alterations (1997), §3.4, printed p.606;
the quotient-free norm-section replacement in the DAG proof, steps 1--7.
(blueprint: lem-sfb-relative-norm-pair-interpolation).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry
open Scheme.Modules

/-- Restrict an ordinary section over an open subscheme to a fibre factoring through it.
The commuting triangle fixes the comparison with the original line bundle, and the
normalized pullback unit and canonical power comparison fix the section.
Source: Stacks, Tags 0096, 0097, 01CD; de Jong §3.4, p.606.
(blueprint: lem-sfb-relative-norm-pair-interpolation). -/
noncomputable def normInterpolationRestriction {Y Z : Scheme.{u}}
    (V : Y.Opens) (j : Z ⟶ Y) (e : Z ⟶ V.toScheme) (he : e ≫ V.ι = j)
    (L : Y.Modules) (n : ℕ)
    (a : ((tensorPullback V.ι).obj (L.tensorPow n)).sections) :
    (((tensorPullback j).obj L).tensorPow n).sections :=
  SheafOfModules.sectionsMap (boundaryPullbackPowIso j L n).hom
    (SheafOfModules.sectionsMap
      (eqToIso (congrArg (fun q ↦ (tensorPullback q).obj (L.tensorPow n)) he)).hom
      (SheafOfModules.sectionsMap
        ((tensorPullbackSectionComp e V.ι).inv.app (L.tensorPow n))
        (SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
          (((tensorPullback e).obj ((tensorPullback V.ι).obj (L.tensorPow n))).presheaf.map
            (homOfLE (Scheme.Hom.preimage_top e).ge).op
            (((tensorPullbackSectionAdjunction e).unit.app
              ((tensorPullback V.ι).obj (L.tensorPow n))).app ⊤ (a.val (op ⊤))))))))

/-- The norm pair on a fibre, formed from the restrictions of the ordinary sections, as the
two-entry family indexed by `ULift (Fin 2)` used by the free-sheaf generation API.
It uses the original pulled-back line bundle and the actual base-changed action.
Source: de Jong §3.4, p.606; norm-section replacement, step 7.
(blueprint: lem-sfb-relative-norm-pair-interpolation). -/
noncomputable def normInterpolationPair {Y Z : Scheme.{u}} {G : Type v} [Finite G]
    (V : Y.Opens) (j : Z ⟶ Y) (e : Z ⟶ V.toScheme) (he : e ≫ V.ι = j)
    (ρ : G → Aut Z) (L : Y.Modules) (n : ℕ)
    (a b : ((tensorPullback V.ι).obj (L.tensorPow n)).sections) :
    ULift.{u} (Fin 2) →
      ((pencilOrbitBundle ρ ((tensorPullback j).obj L)).tensorPow n).sections :=
  fun i ↦ if i.down = 0
    then pencilNormSection ρ _ n (normInterpolationRestriction V j e he L n a)
    else pencilNormSection ρ _ n (normInterpolationRestriction V j e he L n b)

/-- A norm pair generates and its canonical coordinate morphism is finite; in the generic
case it is also surjective and etale on a nonempty open. The invertibility witness is
concluded, rather than imposed as an additional assumption.
Source: de Jong §3.4, p.606; norm-section replacement, steps 2, 3 and 7.
(blueprint: lem-sfb-relative-norm-pair-interpolation). -/
def normInterpolationPencil {Z T : Scheme.{u}} (f : Z ⟶ T)
    (M : Z.Modules) (t : ULift.{u} (Fin 2) → M.sections) (generic : Bool) : Prop :=
  ∃ hM : M.IsInvertible, ∃ ht : Epi (M.freeHomEquiv.symm t),
    IsFinite (@ProjectiveSpace.homOfGeneratingSections _ _ _ _ f M hM t ht) ∧
    (generic = true →
      Surjective (@ProjectiveSpace.homOfGeneratingSections _ _ _ _ f M hM t ht) ∧
      ∃ W : Z.Opens, Nonempty W ∧
        Etale (W.ι ≫ @ProjectiveSpace.homOfGeneratingSections _ _ _ _ f M hM t ht))

/-- An affine neighbourhood admits ordinary sections whose norm pair is a finite pencil
on the special fibre and a finite surjective separating pencil on the generic fibre.
No infinitude or characteristic restriction is imposed.

Source: de Jong, Families of curves and alterations (1997), §3.4, printed p.606;
quotient-free norm-section replacement in the DAG.
(blueprint: lem-sfb-relative-norm-pair-interpolation).

Proof:
1. Projectivity gives properness; finite type over k gives a Noetherian base. Base change
of the embedding makes L_s and L_K ample and invertible. Surjectivity and pure geometric
fibre dimension give nonempty one-dimensional special and generic fibres. Use
lem-kun-projective-implies-proper, lem-weil-pbc-finite-type-over-noetherian,
lem-pc-projective-base-change, lem-pc-closed-imm-base-change, lem-pc-dim-base-change,
lem-weil-pbc-projective-ample-invertible and lem-weil-pbc-invertible-pullback-tensor.
2. Apply lem-sfb-ample-curve-two-section-pencil on the special fibre. Choose a positive
multiple n of its exponent above both thresholds from lem-sfb-separating-pair-open and
lem-trf-ample-fibre-section-lifting. The separating open also gives finite-dimensionality
of the generic section space.
3. Power the special ordinary sections. Their norms are the powers of their norms,
as checked in local frames using def-sfb-pencil-orbit-bundle-norm and the canonical tensor
comparisons. The pair still generates; its map is the original map followed by
[x:y] ↦ [x^r:y^r]. On either chart the latter is finite with module basis 1,z,...,z^(r-1),
even in inseparable characteristic. Use lem-weil-pbc-projective-space-standard-charts,
def-weil-pbc-morphism-to-projective-space-by-sections and lem-weil-pbc-finite-local-on-target.
4. Lift the two powered ordinary sections by lem-trf-ample-fibre-section-lifting,
intersect the neighbourhoods, and shrink to a principal affine neighbourhood of s.
5. The restricted line bundle powers are quasi-coherent. Properness gives the qcqs
hypotheses of lem-sc-fraction-field-sections-base-change, identifying their generic
sections with K tensor the relative sections. Extract finitely many relative sections
whose generic restrictions form a basis; no flatness or freeness of relative sections
is used. Use def-sc-invertible-module, def-weil-proper-morphism,
def-weil-finite-type-morphism, lem-pc-projective-base-change and the tensor comparisons.
6. Choose nonzero t in the maximal ideal of s. The localized domain A' is infinite,
since a finite domain is a field and its maximal ideal here is nonzero. Perturb each lift
by t times A'-linear combinations of those basis sections. Over K this is an affine-space
isomorphism. The inverse image of the separating open contains a nonempty principal open.
A nonzero polynomial over K is nonzero at some tuple in A', by induction on the number
of variables and the one-variable root bound; the zero-variable case is a nonzero constant.
7. Choose such a tuple. Perturbations vanish on the special fibre, preserving the powered
finite norm pencil, while the generic pair lies in the separating open. Apply
lem-sfb-separating-pair-open. Restriction commutes with every translated tensor factor,
section, permutation and power comparison in def-sfb-pencil-orbit-bundle-norm, so these
are the stated actual norms, with no division by the group order.
-/
theorem exists_relative_norm_pair_interpolation
    (k A K : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K]
    (s : Spec (.of A)) (hs : s.asIdeal.IsMaximal) (hs0 : s.asIdeal ≠ ⊥)
    (Y : Scheme.{u}) [IsIntegral Y] (p : Y ⟶ Spec (.of A))
    [Surjective p] [IsHProjective p]
    [LocallyOfFiniteType (p ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)))]
    [QuasiCompact (p ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)))]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (q : Spec (.of Ω) ⟶ Spec (.of A)), (pullback p q).IsPureDimension 1)
    [Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K))))]
    [GeometricallyIntegral
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K))))]
    (D : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (D + 1)); Spec (.of A)))
    [IsClosedImmersion i] (hi : i ≫ ℙ(ULift.{u} (Fin (D + 1)); Spec (.of A)) ↘
      Spec (.of A) = p)
    (L : Y.Modules) (hL : L = (tensorPullback i).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin (D + 1))) (Spec (.of A)) 1))
    (G : Type v) [Group G] [Finite G] (ρ : G →* Aut (Over.mk p))
    (hfaithful : Function.Injective (fun g : G ↦
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⋙
        Over.forget _).mapIso (ρ g))) :
    ∃ V : (Spec (.of A)).Opens, s ∈ V ∧ IsAffineOpen V ∧
    ∃ (n : ℕ), 1 ≤ n ∧
    ∃ (a b : ((tensorPullback (p ⁻¹ᵁ V).ι).obj (L.tensorPow n)).sections)
      (es : p.fiber s ⟶ (p ⁻¹ᵁ V).toScheme)
      (hes : es ≫ (p ⁻¹ᵁ V).ι = p.fiberι s)
      (eK : pullback p (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⟶
        (p ⁻¹ᵁ V).toScheme)
      (heK : eK ≫ (p ⁻¹ᵁ V).ι =
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K)))),
      normInterpolationPencil (p.fiberToSpecResidueField s) _
        (normInterpolationPair (p ⁻¹ᵁ V) (p.fiberι s) es hes
          (fun g ↦ (Over.pullback ((Spec (.of A)).fromSpecResidueField s) ⋙
            Over.forget _).mapIso (ρ g)) L n a b) false ∧
      normInterpolationPencil
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) _
        (normInterpolationPair (p ⁻¹ᵁ V)
          (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) eK heK
          (fun g ↦ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⋙
            Over.forget _).mapIso (ρ g)) L n a b) true := by
  sorry

end AlgebraicGeometry
