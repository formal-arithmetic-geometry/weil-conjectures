/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # Hartogs comparison with an actual algebra pushforward

Source: Stacks Project, Tag 0E9I.
(blueprint: lem-sbc-depth-two-hartogs-algebra-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Hartogs identifies a supplied coherent depth-two extension with the actual
pushforward, including the scalar-compatible comparison of ring-valued stalks.

Source: Stacks Project, Tag 0E9I; stalks as filtered colimits, Tag 009E.
(blueprint: lem-sbc-depth-two-hartogs-algebra-comparison)

Proof: Quasi-coherence and finite affine sections over a locally Noetherian
scheme say that N is coherent. Apply Tag 0E9I to get the canonical isomorphism
N to j_*(N restricted to U). Push forward the supplied restriction isomorphism.
The restriction of (f followed by j)_* O_X to U is f_* O_X, and composition
of direct images identifies j_* f_* O_X with the displayed actual algebra's
underlying module. Compose these three module isomorphisms. On stalks apply
the module stalk functor to this isomorphism. Forgetting the rings of the
algebra sheaf to abelian groups commutes with the filtered colimit defining
the stalk, giving the additive comparison with the CommRingCat-valued stalk.
Its scalar compatibility follows on germs from the structure sheaf map:
the germ of r times the germ of b is the germ of r*b. Every scalar and vector
have representatives on a common neighbourhood, so the comparison is linear.
The inverse is linear by bijectivity. This uses no finiteness or etaleness of f
and no boundary depth assumption on the base ring. Empty stalks and empty
schemes obey the same functorial comparisons. -/
theorem depth_two_hartogs_algebra_comparison
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    Nonempty (Modules.restrict N U.ι ≅ Modules.restrict B.toModule U.ι) →
    Nonempty (N ≅ B.toModule) ∧
      ∀ y : L,
        letI : Algebra (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj) :=
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom.toAlgebra
        Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)
          ≃ₗ[L.presheaf.stalk y]
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj)) := by sorry

end AlgebraicGeometry.Scheme
