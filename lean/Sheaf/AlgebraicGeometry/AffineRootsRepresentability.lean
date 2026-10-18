/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf

/-!
# The affine scheme of roots of unity

Source: Stacks Project, groupoids.tex, Tag 040M, Example `example-roots-of-unity`,
and etale-cohomology.tex, Tag 03PK, Section `section-kummer`
(blueprint: lem-asd-affine-roots-representability).

## Main definitions

- `affineRootsOver`: the explicit quotient spectrum over `Spec R`.
- `affineRootsCoordinate`: its distinguished global section.

## Main statement

- `affineRoots_representability`: the natural bijections, their sheaf identification, and
  their compatibility with arbitrary base change.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

namespace AlgebraicGeometry

/-- The scheme `Spec R[t]/(t^n - 1)` over `Spec R`. `AdjoinRoot` is exactly the quotient
by the principal ideal, and the structure morphism is induced by the quotient algebra map.
Source: Stacks, Tag 040M (blueprint: lem-asd-affine-roots-representability). -/
noncomputable def affineRootsOver (R : Type u) [CommRing R] (n : ℕ) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R
    (AdjoinRoot ((X : R[X]) ^ n - 1)))))

/-- The global section corresponding to the residue class of `t` in `R[t]/(t^n - 1)`.
Source: Stacks, Tag 040M (blueprint: lem-asd-affine-roots-representability). -/
noncomputable def affineRootsCoordinate (R : Type u) [CommRing R] (n : ℕ) :
    Γ((affineRootsOver R n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot ((X : R[X]) ^ n - 1)))).inv
    (AdjoinRoot.root ((X : R[X]) ^ n - 1))

/-- The affine root scheme represents roots of unity on all test schemes, naturally and
compatibly with arbitrary base change. The presheaf isomorphism is the identification of
sheaves: the left side is a sheaf by `smallEtaleRepresentablePresheaf_isSheaf`, and the right
side is the underlying presheaf of the recorded roots sheaf. The representable presheaf is
transported by the standard `ULift` functor to the coefficient universe `u+1`. The formula
is specified using
the kernel inclusion into `gmSheaf`, whose sections are lifted, additively written units.
Mathlib's `Over.pullback` chooses `P ×_V V'`, with projection `pullback.fst` to `P`, for the
base change denoted `V' ×_V P` in the source.

Source: Stacks, Tag 040M and Tag 03PK
(blueprint: lem-asd-affine-roots-representability).

Proof: The quotient relation gives `x^n = 1`, so `x` is a unit with inverse `x^(n-1)`.
The adjunction between global sections and affine spectra identifies a morphism into `P`
with a ring homomorphism from `R[t]/(t^n-1)` to the global section ring. Being over `Spec R`
means this homomorphism is an `R`-algebra homomorphism. The polynomial and quotient universal
properties identify these homomorphisms with sections whose nth power is one, which are
units because n is positive. This correspondence sends a morphism to pullback of `x`.
Functoriality of pullback gives naturality in every test scheme. Restrict to the small
etale site; the representable presheaf is a sheaf by
`lem-weil-pbc-small-etale-representable-presheaf-sheaf`, and the kernel definition of
`def-asd-etale-roots-of-unity` gives precisely the same roots and restriction maps. This
produces the displayed presheaf isomorphism with its specified kernel-inclusion formula.
Finally, the fibre-product universal property identifies morphisms into the base-changed
scheme with morphisms into `P` over `V`; applying the same correspondence gives the
base-changed bijections. Composition of pullbacks gives their naturality and the final
compatibility with base-changing a morphism. -/
theorem affineRoots_representability (R : Type u) [CommRing R] (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : Γ((affineRootsOver R n).left, ⊤)ˣ,
      (x : Γ((affineRootsOver R n).left, ⊤)) = affineRootsCoordinate R n ∧
      ((x⁻¹ : Γ((affineRootsOver R n).left, ⊤)ˣ) :
          Γ((affineRootsOver R n).left, ⊤)) = affineRootsCoordinate R n ^ (n - 1) ∧
      ∃ E : ∀ U : Over (Spec (CommRingCat.of R)),
          (U ⟶ affineRootsOver R n) ≃ {z : Γ(U.left, ⊤)ˣ // z ^ n = 1},
        (∀ (U : Over (Spec (CommRingCat.of R))) (a : U ⟶ affineRootsOver R n),
          ((E U a).val : Γ(U.left, ⊤)) = a.left.appTop (affineRootsCoordinate R n)) ∧
        (∀ (U W : Over (Spec (CommRingCat.of R))) (f : U ⟶ W)
            (a : W ⟶ affineRootsOver R n),
          (E U (f ≫ a)).val = Units.map f.left.appTop.hom.toMonoidHom (E W a).val) ∧
        (∃ e : ((Scheme.Etale.forget (Spec (CommRingCat.of R))).op ⋙
              yoneda.obj (affineRootsOver R n) ⋙ uliftFunctor.{u + 1, u}) ≅
            ((Spec (CommRingCat.of R)).rootsOfUnitySheaf n).obj ⋙
              forget AddCommGrpCat.{u + 1},
          ∀ (W : (Spec (CommRingCat.of R)).Etale)
              (a : (Scheme.Etale.forget _).obj W ⟶ affineRootsOver R n),
            Additive.toMul
              (((kernel.ι (n • 𝟙 (Spec (CommRingCat.of R)).gmSheaf)).hom.app (op W)
                (e.hom.app (op W) ⟨a⟩)).down) =
              (E ((Scheme.Etale.forget _).obj W) a).val) ∧
        (∀ (V' : Scheme.{u}) (v : V' ⟶ Spec (CommRingCat.of R)),
          ∃ E' : ∀ U : Over V',
              (U ⟶ (Over.pullback v).obj (affineRootsOver R n)) ≃
                {z : Γ(U.left, ⊤)ˣ // z ^ n = 1},
            (∀ (U : Over V') (a : U ⟶ (Over.pullback v).obj (affineRootsOver R n)),
              ((E' U a).val : Γ(U.left, ⊤)) = a.left.appTop
                ((pullback.fst (affineRootsOver R n).hom v).appTop
                  (affineRootsCoordinate R n))) ∧
            (∀ (U W : Over V') (f : U ⟶ W)
                (a : W ⟶ (Over.pullback v).obj (affineRootsOver R n)),
              (E' U (f ≫ a)).val = Units.map f.left.appTop.hom.toMonoidHom (E' W a).val) ∧
            (∀ (U : Over (Spec (CommRingCat.of R))) (a : U ⟶ affineRootsOver R n),
              (E' ((Over.pullback v).obj U) ((Over.pullback v).map a)).val =
                Units.map (pullback.fst U.hom v).appTop.hom.toMonoidHom (E U a).val)) := by
  sorry

end AlgebraicGeometry
