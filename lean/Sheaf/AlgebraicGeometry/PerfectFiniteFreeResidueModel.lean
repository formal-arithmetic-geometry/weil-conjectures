/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedFiberBetti


/-! # Finite free local models with prescribed residue cohomology ranks

Source: Stacks Project, More on Algebra, Lemma lift-perfect-from-residue-field, Tag 0BCD
(blueprint: lem-sc-perfect-finite-free-residue-model).

The derived fibre is `derivedPullback (X.fromSpecResidueField x)`; its degree-`i`
cohomology vector space over `κ(x)` is `derivedFiberCohomology X E i x` and its dimension
`d_i` is `derivedFiberBetti X E i x` (def-sc-derived-fiber-betti).
-/

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Every perfect complex has an affine local bounded finite free model whose degreewise
ranks equal its derived fibre cohomology dimensions at the prescribed point.
Source: Stacks Project, More on Algebra, Lemma lift-perfect-from-residue-field, Tag 0BCD
(blueprint: lem-sc-perfect-finite-free-residue-model).

Proof:
1. By `def-pc-perfect-complex` and its affine characterization (Tag 08EB), choose an affine
   neighbourhood `Spec A` of `x` with a bounded finite projective representative `P`.
   Pull it to the residue field. By `lem-sc-perfect-pullback-perfect-residue` this fibre
   is perfect. Its cohomology is finite dimensional and has finite support.
2. Localize `P` at the prime corresponding to `x`. Finite projective modules over this
   local ring are finite free (Tag 00NZ), so this complex is pseudo-coherent
   (`def-pur-pseudo-coherent-complex`). Apply
   `lem-sc-perfect-local-pseudocoherent-free-model` (Tag 0BCC) to obtain a bounded above
   free model with term ranks `d i`. Finite support of `d` makes this model bounded.
3. The local ring is the filtered colimit of principal localizations away from the prime
   (Tag 00CM). By `lem-pc-affine-perfect-colimit-descent`, descend the bounded projective
   complex to a principal localization. By `lem-pc-affine-perfect-hom-colimit`, descend
   its derived isomorphism with `P`, its inverse, and the two identity relations after
   further localization. Apply `lem-weil-pbc-finite-projective-standard-free-cover` to
   the finitely many nonzero terms, choosing free neighbourhoods containing the prime.
   Intersect these principal opens. Each free term has rank `d i`, because its
   localization is the prescribed free term over a nonzero local ring. Sheafify this
   complex on the resulting affine open to obtain the asserted model. -/
theorem exists_finiteFreeResidueModel
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) (x : X) :
    (∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x)) ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0) ∧
      ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
        ∃ K : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
          (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
          (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U)
            (ULift.{u} (Fin (derivedFiberBetti X E i x))))) ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj K) := by
  sorry

end
end AlgebraicGeometry.Scheme
