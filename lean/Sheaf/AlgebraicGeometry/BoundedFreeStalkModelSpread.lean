/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.Algebra.Homology.AffinePerfectColimitDescent
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Spreading a prescribed bounded free stalk model

Source: Stacks Project, Tag 0BCD, spreading paragraph, with Tags 0BC7 and 09RE.
(blueprint: lem-sc-bounded-free-stalk-model-spread).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A given bounded finite-free stalk model of a locally strictly perfect object spreads
with its specified ranks to an affine neighbourhood. No residue rank computation is made.

Source: Stacks Project, Tag 0BCD, spreading paragraph; Tags 00CM, 0BC7, 09RE and 00NX.
(blueprint: lem-sc-bounded-free-stalk-model-spread).

Proof:
1. Restrict the strictly perfect representative P from hlocal to an affine neighbourhood
   W = Spec A of x, and let p be its corresponding prime. Its terms are quasi-coherent:
   each is a direct summand of a finite free sheaf. The affine correspondence produces
   a bounded complex C of finite projective A-modules. Its localization at p represents
   the same derived object as the stalk of G, by the exact stalk functor applied to eG
   and the local comparison for P. Thus eF identifies F with C_p in the derived category.
2. Present A_p as the filtered colimit of the A_f for f outside p (Tag 00CM).
   Apply exists_finite_projective_model_of_directed_colimit to F, whose terms are
   finite projective by hfree, obtaining a bounded finite projective complex Q at a stage.
   Apply affine_perfect_hom_colimit in both orders to descend eF and its inverse.
   Its injectivity clause makes their two inverse identities hold at a common later
   stage. Then Q represents E on that principal neighbourhood of x.
3. Apply exists_standardFreeCover_of_finite_projective to each of the finitely many
   possibly nonzero terms of Q. In each cover select a principal open containing p,
   and intersect the finitely many selected principal opens. This is still principal
   in Spec A, hence affine, and contains x. All terms are free there. Their ranks equal
   d i: localization at p recovers F.X i, and invariant basis number over the nonzero
   local ring identifies their finite ranks. Outside the bounds the terms are zero;
   hfree at p and invariant basis number force d i = 0, so the asserted free sheaf
   is zero as well. Sheafify Q and the descended derived isomorphism and transport
   to the over-site. Sheafification and localization preserve the bounds, giving K.
No arbitrary stalk complex is assumed to spread: bounded finite freeness and a local
strictly perfect comparison are both used. This includes d identically zero and any
choice of bounds, and does not require the scheme to be separated.
-/
theorem spread_boundedFree_stalkModel
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i))
    (hfree : ∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x))))
    (eF : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj K) := by sorry

end
end AlgebraicGeometry.Scheme
