module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity
import Sheaf.AlgebraicGeometry.FibreStalkQuotient

/-! # A fibre-avoiding closure neighbourhood in a smooth scheme

Source: EGA IV4, Proposition 21.14.3, first reduction paragraph, using IV3, 9.5.3.
(blueprint: lem-sfb-smooth-closure-fibre-avoidance-neighbourhood)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nongeneric smooth-fibre point of local dimension at least two has affine
neighbourhoods over a Noetherian normal domain on which its closure avoids every
fibre component, and has local dimension at least two on the generic fibre.
The coordinate rings of the affine opens `T` and `V` are `Γ(S, T)` and `Γ(X, V)`.
The inverse image of `closure {x}` under the fibre projection followed by `V.ι`
is exactly the closed subset `Z_t` of the statement.

Source: EGA IV4, Proposition 21.14.3, first reduction paragraph; IV3, 9.5.3.
(blueprint: lem-sfb-smooth-closure-fibre-avoidance-neighbourhood)

Proof:
1. Choose an affine neighbourhood of `f x` by lem-weil-pbc-affine-opens-basis.
   It is Noetherian by pqf-lem-affine-open-locnoeth. Its topological space is
   Noetherian by the ascending-chain condition on radical ideals. Apply
   lem-trf-normal-topologically-noetherian-components to obtain an open integral
   component through `f x`, then choose an affine neighbourhood `T` inside it.
   Its section ring `A` is a Noetherian domain by def-pc-integral-scheme.
2. By lem-sbc-normal-sections-finite-product and lem-weil-pbc-affine-scheme-qcqs,
   `A` is a finite product of normal domains. A nonzero domain has no nontrivial
   idempotents, so this product has exactly one factor and `A` is integrally closed.
3. Choose affine `W` containing `x` inside the preimage of `T`. By
   lem-weil-pbc-smooth-restrict-open-subschemes and lem-pc-smooth-flat its map
   to `T` is smooth and locally finitely presented. Apply
   lem-weil-pbc-lfp-affine-opens-finite-presentation: its section algebra is
   finitely presented, hence finite type and Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Let `D` be the closure of `x`
   in `W`, and `Q` the reduced closure of `f x` in `T`, constructed by
   lem-weil-pbc-reduced-induced-closed-subscheme. Continuity gives `g(D) ⊆ Q`.
4. The complement of `D` is dense in the fibre over `f x`: otherwise a generic
   point of a component lies in the closure of `x`. Maximality of that component
   and the T0 property force it to equal `x`, contradicting the hypothesis.
   Passing to an open subscheme preserves this nongeneric-point hypothesis.
5. Base change to `Q` using lem-sfb-finite-type-composition-base-change.
   Its generic residue field equals the residue field at `f x` in `T`, by the
   localization-and-quotient description of def-weil-residue-field. Apply
   lem-sbc-generic-open-fibre-density to obtain an open `H` of `Q` containing
   `f x`, on all of whose fibres the complement of `D` is dense.
6. Remove the inverse image of the closed subset `Q \ H` from `W`, and choose
   affine `V` containing `x` in the remaining open. Restriction is still smooth,
   and lem-weil-pbc-lfp-affine-opens-finite-presentation gives its finite
   presentation over `A`. The ring `A` has not changed.
7. Outside `Q` the closure fibre is empty; over `Q \ H` the whole `V` fibre is
   empty. Over `H`, the dense complement in the `W` fibre remains dense in the
   open `V` fibre. These fibres are Noetherian by pqf-lem-locnoeth-lft and
   lem-weil-pbc-affine-scheme-qcqs, with finitely many components by
   lem-weil-pbc-noetherian-finitely-many-components. A closed subset with dense
   complement contains no component: isolate each component from the others
   by an open subset and use its generic point.
8. If a closure point lies over the generic point `η` of `T`, continuity and
   the domain property force `f x = η`. Its prime in `Γ(X, V)` contains that
   of `x`. By lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-localization-dimension-chains-below-prime, prime chains below
   the latter prime give local dimension at least two at the closure point.
9. The base stalk at `η` is the fraction field of `A`, hence its maximal ideal
   is zero. By lem-sbc-scheme-fibre-stalk-quotient the fibre stalk equals the
   total-space stalk, giving the required bound. If the closure has empty
   generic fibre, the universally quantified bound is vacuous. -/
theorem exists_affine_smooth_closure_fibre_avoidance_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsLocallyNoetherian S]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (x : X) (hdim : 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (hnongeneric : ∀ C ∈ irreducibleComponents (f.fiber (f x)),
      ¬ IsGenericPoint (f.asFiber x) C) :
    ∃ (T : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ T),
      IsAffineOpen T ∧ IsAffineOpen V ∧ f x ∈ T ∧ x ∈ V ∧
      IsNoetherianRing Γ(S, T) ∧ IsDomain Γ(S, T) ∧ IsIntegrallyClosed Γ(S, T) ∧
      Smooth (f.resLE T V e) ∧ (f.appLE T V e).hom.FinitePresentation ∧
      (∀ (t : T.toScheme) (C : Set ((f.resLE T V e).fiber t)),
        C ∈ irreducibleComponents ((f.resLE T V e).fiber t) →
          ¬ C ⊆ ((f.resLE T V e).fiberι t ≫ V.ι) ⁻¹' closure ({x} : Set X)) ∧
      (∀ (η : T.toScheme), IsGenericPoint η Set.univ →
        ∀ z : (f.resLE T V e).fiber η,
          ((f.resLE T V e).fiberι η ≫ V.ι) z ∈ closure ({x} : Set X) →
            2 ≤ ringKrullDim (((f.resLE T V e).fiber η).presheaf.stalk z)) := by
  sorry

end AlgebraicGeometry
