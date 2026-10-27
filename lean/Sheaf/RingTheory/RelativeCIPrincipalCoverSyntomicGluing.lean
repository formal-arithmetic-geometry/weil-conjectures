module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionFlat
import Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Syntomicity from relative complete intersections on a principal cover

Source: Stacks Project, Algebra, Tags 00SO (lemma-local-syntomic) and
00SW (lemma-relative-global-complete-intersection)
(blueprint: lem-trf-relative-ci-principal-cover-syntomic-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A finite principal cover by relative global complete intersections makes the ring map
flat and finitely presented, with local complete-intersection residue fibres.
The algebra structure encodes the arbitrary ring homomorphism `A → D`. Each fibre
conclusion includes the finite-type instance required by the local-complete-intersection
definition, whose domain consists of finitely generated algebras.
Source: Stacks Project, Algebra, Tags 00SO (lemma-local-syntomic) and
00SW (lemma-relative-global-complete-intersection).
(blueprint: lem-trf-relative-ci-principal-cover-syntomic-gluing)

Proof:
1. If `D` is the zero ring, it is the finitely presented quotient `A/(1)`, its module
   is zero and flat, and all fibres are zero, hence global and local complete intersections
   by the convention in def-weil-pbc-complete-intersection-over-field. In particular this
   treats `m = 0`, since the displayed sum then forces `0 = 1`.
2. For every chart choose the finite polynomial presentation in
   def-weil-pbc-relative-global-complete-intersection. It is finitely presented by
   def-weil-pbc-finitely-presented-algebra. Apply
   lem-weil-pbc-relative-global-complete-intersection-flat to those very equations and
   transport flatness along the presentation's algebra isomorphism.
3. The relation `∑ a, h a * g a = 1` shows that the range of `g` spans the unit ideal:
   multiply it by any element of `D`. Apply lem-trf-flat-ring-map-principal-cover and
   lem-trf-finite-presentation-ring-map-principal-cover to that range. Repeated chart
   elements cause no problem. These give flatness and finite presentation of `A → D`.
4. For a prime `p` of `A`, put `k = κ(p)` and `F = k ⊗[A] D`. Apply
   lem-weil-pbc-relative-global-complete-intersection-base-change to the chosen chart
   equations and `A → k`. Over the field `k` the resulting quotient is a global complete
   intersection: its nonzero fibre has the specified dimension; the zero quotient uses
   the zero-ring convention. By lem-weil-pbc-localization-base-change and tensor
   reassociation it identifies with the localization of `F` at `1 ⊗ g a`. In the reversed
   tensor order the identification sends `(d/g^r) ⊗ λ` to `(d ⊗ λ)/(g ⊗ 1)^r`;
   the balanced relations verify this on pure tensors.
5. Finite presentation from step 3 gives finitely many algebra generators of `D`;
   their images generate `F` over `k`. The relation maps to a unit-ideal relation in `F`,
   so every prime of `F` avoids some `1 ⊗ g a`. The principal opens thus cover its spectrum,
   and their localized rings are global complete intersections by step 4. This is exactly
   def-weil-pbc-complete-intersection-over-field, including the zero fibre case. -/
theorem relative_ci_principal_cover_syntomic_gluing
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    (m : ℕ) (g h : Fin m → D) (hcover : ∑ a : Fin m, h a * g a = 1)
    (hci : ∀ a : Fin m, IsRelativeGlobalCompleteIntersection
      ((algebraMap D (Localization.Away (g a))).comp (algebraMap A D))) :
    RingHom.Flat (algebraMap A D) ∧
      Algebra.FinitePresentation A D ∧
        ∀ (p : Ideal A) [p.IsPrime],
          ∃ (hft : Algebra.FiniteType p.ResidueField (p.Fiber D)),
            @IsLocalCompleteIntersection p.ResidueField (p.Fiber D) _ _ _ hft := by
  sorry

end Algebra
