/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.AlgebraicGeometry.FiniteTorDimension
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # Tor bounds for an affine module model

Source: Stacks Project, Tags 08CG, 08E9 and 08DX.
(blueprint: lem-pc-affine-local-sheafification-tor-amplitude).
-/

@[expose] public section

universe u w wR

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Tor bounds on an open W pass to a module model on an affine subopen U.
Source: Stacks Project, Tags 08CG, 08E9(1), 08DX(2), and 09U8.
(blueprint: lem-pc-affine-local-sheafification-tor-amplitude).

Proof: Write the interval [a,b] supplied by the finite Tor hypothesis on W.
For each module sheaf G on U, regard G as a sheaf on W by direct image under
U.toScheme -> W.toScheme. Test the Tor bound on that direct image, and restrict
back to U. Exact restriction preserves derived tensor and homology; the
restriction of the direct image is G. Composition of derived open pullbacks
identifies the restricted object with the pullback of K from S to U. Thus the
same interval bounds all its tensors with G. Transport along U.isoSpec and
Modules.overEquiv U: these exact equivalences identify the structure sheaves,
tensor products and cohomology. The representing isomorphism hP identifies the
object with the associated complex of P. Test on associated sheaves of ring
modules and use the affine Tor-amplitude criterion (08E9(1)). Exact faithful
associated sheafification detects zero homology modules, proving Tor amplitude
[a,b] for Q(P). Empty opens and zero rings give zero modules, and no boundedness
or pseudo-coherence of P is used. -/
theorem finiteTorAmplitude_of_affine_sheafification_of_open_tor (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wR} (ModuleCat.{u} (S.presheaf.obj (.op U)))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (W : S.Opens) (hUW : U ≤ W)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (hTor : HasFiniteTorDimension W.toScheme ((derivedPullback W.ι).obj K)) :
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (ModuleCat.{u} (S.presheaf.obj (.op U))) a b (DerivedCategory.Q.obj P) := by sorry

end AlgebraicGeometry.Scheme
