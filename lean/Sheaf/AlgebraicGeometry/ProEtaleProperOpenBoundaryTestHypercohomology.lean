/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Local proper/open boundary hypercohomology

Source: Step 2 of the boundary-restriction proof, or Steps 5--7 of the
open-injective proper-acyclicity plan.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The local cohomology calculation at a boundary-specializing affine test.
The conclusion is a group of derived sections on the proper pullback, not the
vanishing of a higher direct image sheaf or its closed restriction.

Source: the arbitrary-injective boundary step in
`lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction`, Step 2;
parent `lem-sp-proetale-open-injective-proper-acyclic`, Steps 5--7. Stacks
Tag 0F7B supplies the etale analogue, not a pro-etale base-change theorem.
(blueprint: lem-sp-proetale-proper-open-boundary-test-hypercohomology).

Proof plan: Put P = B times_D W, U = C times_D W and E_W = E times_D W.
Restriction along P to B and U to C is weakly etale and preserves injectives.
The open-extension base-change isomorphism identifies the restricted input with
k_W! J_W. The base change of the clopen factor t in the witness identifies U with
a clopen part of P times_W E_W. Compute derived sections using a bounded-below
injective resolution of k_W! J_W on P, rather than a resolution of J_W on U.
The w-contractible evaluation hypothesis makes evaluation at W exact. Use the
finite-principal-open and complementary closed-localization cover of W. Sections
supported in the open have zero restriction on every affine piece specializing
to the closed part; properness keeps the image of a closed support closed. The
injective lifting property of J_W on the clopen open part supplies primitives for
positive cocycles, compatible after refinement, and the zero closed restrictions
allow them to glue across the complementary localization. Hence the positive
cohomology of the section complex is zero. The restriction/injective-resolution
comparison identifies it with the displayed hypercohomology group. This is the
arbitrary-injective calculation still to be proved: no etale-origin witness or
proper base change for arbitrary pro-etale sheaves is assumed. -/
theorem isZero_properOpen_boundary_test_hypercohomology
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J]
    (w : OpenProperClopenWitness p r k i)
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((ProEt.ringHypercohomology B
      ((sheafCompose (ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing B A)) ((proEtaleBaseChange p).obj W) (q : ℤ)).obj
            ((CochainComplex.singleFunctor
              (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
                ((sfIntrinsicExtensionByZero k A).obj J))) := by
  sorry

end AlgebraicGeometry.Scheme
