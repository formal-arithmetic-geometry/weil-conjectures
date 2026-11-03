/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Lissity of smooth proper higher direct images

Source: latest blueprint, relative smooth-proper purity proof, Step 1,
lattice, finite-level, limit and scalar-extension paragraphs.
(blueprint: lem-zl-smooth-proper-lisse-cohomology)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeSmoothProperPurity
open CondensedRing

/-- Smooth proper direct image preserves lissity on cohomology of a sheaf.
No Weil structure, purity hypothesis, or constant relative dimension is needed.

Source: latest blueprint, prop-zl-smooth-proper-relative-purity.proof.md,
Step 1, lattice, finite-level, limit and scalar-extension paragraphs
(blueprint: lem-zl-smooth-proper-lisse-cohomology).

Proof: descend the lisse Qbar coefficient to a finite coefficient field. Etale locally
on the base, the smooth-fibre lattice-neighbourhood theorem gives an embedded lisse
integral lattice. Finite proper constructibility gives finite stalks for its reductions.
Smooth proper specialization and the finite-stalk specialization criterion make all
finite-level higher direct images finite locally constant. Integral proper base change
identifies reduction of the derived direct image with these finite-level images.
Proper integral constructibility gives finite integral fibre cohomology. The finite
Mittag-Leffler theorem, the Milnor sequence and the finite-local-system limit-model
lemma identify each integral higher direct image with a finite constant local model.
Flat scalar extension first to the coefficient field and then to Qbar gives the asserted
finite locally free local models. Negative degrees vanish by left exactness of direct
image. The argument allows zero rank, empty fibres and disconnected schemes. -/
theorem smooth_proper_lisse_cohomology
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] [Smooth f.left]
    (M : NativeCondensedModule.Modules ell X.left)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M) (i : ℤ) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((lowerStar (Profinite.padicAlgClRingObj ell) f.left).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by sorry

end WeilConjectures.RelativeSmoothProperPurity
