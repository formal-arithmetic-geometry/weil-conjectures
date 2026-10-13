/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.LocalizedHomologyStalkComparison
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback

/-! # The residue calculation for the degree-zero component of a rank-one model

Source: Stacks Project, Tag 0E62, residue-field argument, with Tag 0BCD.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The degree-zero component of a fixed chain representative is invertible at the
chosen stalk when its derived residue arrow is invertible on degree-zero homology.
Source: Stacks Project, Tag 0E62, residue-field argument, and Tag 0BCD.
(blueprint: lem-sc-rank-one-residue-stalk-component).

Proof: Identify the localized site with the open subscheme. The source is the
structure sheaf in degree zero. The target P is bounded with finite-projective
terms, so the termwise flat-complex comparison computes its residue pullback.
Exact restriction and the composition comparison for derived pullback identify
the residue of Q.map alpha with the residue of a, conjugated by c and e. Both
conjugating arrows are isomorphisms, so the residue homology map of alpha is
invertible. Negative terms of P vanish, hence its residue H^0 is the kernel of
the outgoing degree-zero differential without an incoming quotient. Consequently
the image of the residue source generator under alpha^0 is nonzero: it represents
the nonzero image of the source generator in residue homology. The source and
P^0 stalks are free of rank one over the local ring at s. In these bases alpha^0
is multiplication by a scalar whose residue is nonzero. That scalar is a unit
in the local ring, and multiplication by its inverse gives the two-sided inverse
of the stalk component. Forgetting the scalar action gives the asserted additive
isomorphism. No conclusion about the original homology stalk map is used here.
An empty U cannot contain s. Rank zero is excluded by the fixed rank-one hypothesis;
higher differentials and all other fibres are unrestricted. -/
theorem isIso_localized_stalk_component_of_residue_homology (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i))
    (hzero : Nonempty (P.X 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a)))
    (c : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))))
    (α : (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶ P)
    (hα : DerivedCategory.Q.map α = c.inv ≫
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫
        e.hom) :
    IsIso ((localizedModuleStalk S U ⟨s, hs⟩).map (α.f 0)) := by sorry

end AlgebraicGeometry
