/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Sheaf.RepresentationTheory.LocalCyclotomicGroupAlgebraSplit
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive

/-! # Equivariant étale coordinates for a tame smooth morphism

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, Proposition 1.2,
second assertion and proof, printed p.138, equations (4)--(5); coefficient localization
in X 1.3, printed pp.139--140 (blueprint: lem-per-tame-smooth-representation-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Equivariant pointed étale neighborhoods admit a chart in a finite free representation.
The coefficient subalgebra `A` is exactly `ℤ[1/N, ζ]`; `Λ` is its prime localization.
The finite basis is allowed to have empty index `Fin 0`. The two projection equations
express equivariance for the diagonal action: the base action on the first factor and
inverse pullback of `ρ` on the symmetric-algebra spectrum on the second factor.

Source: ILO, Exposé X Proposition 1.2, second assertion, p.138, and X 1.3, pp.139--140
(blueprint: lem-per-tame-smooth-representation-chart).

Proof:
1. At the fixed geometric point, the residue field action is trivial. Relative
   differentials give a finite-dimensional residue representation `D`, spanned by
   differentials of local functions (def-sc-relative-differential-sheaf and
   lem-ag-smooth-relative-differentials-finite-locally-free).
2. Apply lem-per-local-cyclotomic-group-algebra-split. In each matrix block choose
   local functions whose differentials after applying `E₁₁` form a basis. The maps
   `Eₐ₁` give an equivariant map from a finite free representation `V` to the local
   ring inducing an isomorphism from the residue scalar extension of `V` onto `D`.
3. Spread these finitely many functions and their finitely many equivariance identities
   to a neighborhood. Intersect its finitely many translates to make it invariant.
   Functions carry the left action by inverse pullback.
4. The universal property of the symmetric algebra gives the equivariant chart over
   the base, with coordinate differentials precisely the basis just constructed.
5. Use lem-weil-pbc-smooth-locally-standard-smooth and
   lem-weil-pbc-standard-smooth-kahler-basis. In a standard smooth presentation,
   the defining equations and these coordinate functions have square Jacobian `J`
   nonzero at the point.
6. Adjoin the coordinate equations `H-T` and `wJ-1`. The resulting square Jacobian
   is `J²`, up to sign, hence invertible after localization. Apply
   lem-exc-etale-jacobian-presentation, def-exc-jacobian-presentation and
   lem-weil-pbc-etale-ring-map-iff-etale-affine. Intersect translates of the étale
   locus. This is a pointed equivariant open neighborhood; the base can remain
   unchanged. When `D=0`, the same argument gives `V=0` and an étale map to the base. -/
theorem exists_tame_smooth_representation_chart
    (N : ℕ) (hN : 0 < N) (G : Type v) [Group G] [Finite G]
    (hG : ∀ g : G, g ^ N = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (A : Subalgebra ℤ ℂ) (hA : A = Algebra.adjoin ℤ {ζ, (N : ℂ)⁻¹})
    (p : Ideal A) [p.IsPrime] (Λ : Type u) [CommRing Λ]
    [Algebra A Λ] [IsLocalization.AtPrime Λ p]
    (X B : Scheme.{u}) [IsLocallyNoetherian X] [IsLocallyNoetherian B]
    (b : B ⟶ Spec (.of Λ)) (h : X ⟶ B) [Smooth h]
    (aX : G →* Aut X) (aB : G →* Aut B)
    (hb : ∀ g : G, (aB g).hom ≫ b = b)
    (hh : ∀ g : G, (aX g).hom ≫ h = h ≫ (aB g).hom)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (hx : ∀ g : G, x ≫ (aX g).hom = x) :
    ∃ (X' B' : Scheme.{u}) (i : X' ⟶ X) (j : B' ⟶ B)
      (h' : X' ⟶ B') (x' : Spec (.of Ω) ⟶ X')
      (aX' : G →* Aut X') (aB' : G →* Aut B'),
      Etale i ∧ Etale j ∧ x' ≫ i = x ∧ h' ≫ j = i ≫ h ∧
      (∀ g : G, (aX' g).hom ≫ i = i ≫ (aX g).hom) ∧
      (∀ g : G, (aB' g).hom ≫ j = j ≫ (aB g).hom) ∧
      (∀ g : G, (aX' g).hom ≫ h' = h' ≫ (aB' g).hom) ∧
      (∀ g : G, x' ≫ (aX' g).hom = x') ∧
      ∃ (V : ModuleCat.{u} Λ) (n : ℕ) (_ : Module.Basis (Fin n) Λ V)
        (ρ : Representation Λ G V)
        (c : X' ⟶ pullback (j ≫ b)
          (Spec.map (CommRingCat.ofHom (algebraMap Λ (SymmetricAlgebra Λ V))))),
        Etale c ∧ c ≫ pullback.fst _ _ = h' ∧
        ∀ g : G,
          (aX' g).hom ≫ c ≫ pullback.snd _ _ =
            c ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom
              (SymmetricAlgebra.lift ((SymmetricAlgebra.ι Λ V).comp (ρ g⁻¹))).toRingHom) := by
  sorry

end AlgebraicGeometry
