/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.Algebra.Homology.ModuleStalkExact

/-! # The local stalk calculation for a connective rank-one model

Source: Stacks Project, Tag 0E62, local argument; Tag 0BCD.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The local unit calculation for an already supplied strictly perfect representative.
Source: Stacks Project, Tag 0E62, local argument, and Tag 0BCD.
(blueprint: lem-sc-connective-rank-one-model-stalk).

Proof: Restrict the structure-sheaf single complex and the given arrow to U. The
restriction of the source is the single structure-sheaf complex on the localized site.
It is strictly perfect. Conjugate the restricted arrow by that identification and e,
and apply perfect_affine_map_representative to obtain a chain map into P. Take stalks
at s; the degree-zero source and target are free of rank one. Since P has zero negative
terms, its residue H^0 is the kernel of its outgoing degree-zero differential, with
no quotient by incoming boundaries. The assumed residue H^0 isomorphism implies that
the degree-zero chain-map component has nonzero residue: it sends the generator to a
nonzero element of the rank-one residue term. Its coefficient in the local ring is
therefore a unit. The chain-map equation says that the outgoing differential composed
with this invertible degree-zero component is zero, so the outgoing differential at
the stalk is zero. There are no incoming boundaries. Every degree-zero cohomology germ
is consequently a vector in P^0_s, and the inverse unit gives a source preimage.
Restriction preserves the stalk at a point of U. Exactness of stalks identifies stalks
of cohomology with cohomology of the stalk complex. Naturality of these identifications
and the representing equality Q.map α = f transport each preimage back along e to the
original H^0(a)_s. Higher terms and all other fibres are unrestricted. -/
theorem surjective_stalk_homology_of_connective_rank_one_model (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U) (hU : IsAffineOpen U)
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
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Surjective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s) := by sorry

end AlgebraicGeometry
