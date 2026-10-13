/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Source model for the affine derived base-change arrow

Source: Stacks Project, Tag 0DJ8, affine proof and equation-bc.
(blueprint: lem-pc-affine-base-change-source-model).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The localized comparison ending in stalks of the pullback cohomology sheaf,
before any morphism from that pullback is applied. Source: Stacks, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-source-model). -/
def affineBaseChangeIntoPullback
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (p : X') (i : ℤ) :=
  letI := SingleComplexBaseChange.leftAlgebra f g' p
  letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
  letI := hc
  let T := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i
  let s := RingedSpace.moduleStalkFunctor X'.toRingedSpace p
  (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i ≫
    HomologicalComplex.homologyMap
      (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i ≫
    (affineRepresentativeStalkIso X' p T i).inv ≫
    s.map (H.map (inv ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ (derivedPullback g').map e.hom))

/-- The affine base-change arrow has a cohomology module source and a map to the
canonical module of pullback cohomology. No target K', map phi or target coordinates
are involved.
Source: Stacks, Tag 0DJ8, affine proof and its displayed localization identity.
(blueprint: lem-pc-affine-base-change-source-model).

Proof: represent K by a complex of A-modules using the affine derived equivalence.
Resolve over A and then over R. The comparison span of
exists_affineDerivedBaseChangeComparison computes the canonical base-change mate:
the affine tensor-pullback identification identifies the ordinary adjunction maps
on the two resolutions, and the derived adjunction is pinned to these maps.
For every quasi-coherent derived target, affine vanishing and exact tilde
identify cohomology of its affine derived direct image with restriction of
its global sections. Naturality of the tilde/Gamma counit and the direct-image
resolution comparisons gives the natural isomorphism d. The tensor-algebra
cohomology lift in exists_affineDerivedBaseChangeLocalization,
transported across the cartesian identification A tensor_R R' = A', defines U and
its map to H^i of the pulled-back complex. Exact tilde gives eU. Identify the target
with the global sections of pullback cohomology using fromTildeΓ. The counit
calculation gives the displayed global equality. Localize the comparison span at p.
The source localization isomorphism in the same localization theorem identifies
U_p with base-derived tensor cohomology over the three stalk rings extended to
the fourth. Exact localization and tilde stalks identify the target with stalks
of pullback cohomology, through affineDerivedCohomologyStalkIso. For the given
representative P and e, use the unique counit-compatible isomorphism of derived
scalar extensions on the stalks; its multiplication equations preserve the tensor
algebra action. The localized_eq equation and the pullback counit give precisely
affineBaseChangeIntoPullback. Its compatibility with the representative e follows
from the counit naturality, without assuming P is termwise quasi-coherent. This
proves the localized square. These computations hold in every degree without
boundedness, flatness, or a Tor-independence assumption. -/
theorem exists_affineBaseChangeSourceModel
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (i : ℤ) :
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    ∃ (U : ModuleCat.{u} A') (a : U ⟶ V)
      (eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom φg))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf))).obj K))),
      eU.hom ≫ H.map (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K) = F.map a ≫ d.hom.app L ∧
      ∀ p : PrimeSpectrum A',
        let r := affineBaseChangeIntoPullback
          (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
          (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
          sq K P e hc p i
        ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk r).left,
          ∀ x, affineDerivedCohomologyStalkIso A' i p L
            (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = r (lU x) := by
  sorry

end AlgebraicGeometry
