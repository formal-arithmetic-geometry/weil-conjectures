module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.GroupTheory.MonoidLocalization.Away
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Geometric connected components surject onto a connected scheme

Source: Stacks Project, Varieties, Tags 04L7, 04KZ (3), and 038H.
(blueprint: lem-sfb-geometric-connected-component-surjective)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The reduction of the algebraic-closure base change has finitely many irreducible
components and is nonempty. Each of its connected components is clopen; with its open
subscheme structure it is connected, reduced, locally of finite type over the algebraic
closure, has finitely many irreducible components, and surjects onto the original scheme.
Components are indexed by their points: every maximal nonempty connected subset is
`connectedComponent z` for any point `z` in it. Nonemptiness of the reduction thus also
asserts the existence of a nonempty connected component.

Source: Stacks Project, Varieties, Tag 04L7, first proof paragraph, with Tags 04KZ (3)
and 038H. (blueprint: lem-sfb-geometric-connected-component-surjective)

Proof:
1. Cover `X` by its finitely many irreducible components. By
   lem-sfb-geometric-component-finite-preimage, each inverse image is a finite union
   of irreducible components of the base change. These give a finite closed cover.
   Irreducibility and maximality show that every irreducible component is in this
   cover (lem-sc-irreducible-components-cover). Reduction is a homeomorphism on
   underlying spaces, so its irreducible components are finite as well.
2. The spectrum of the field extension surjects onto the base field's spectrum
   (lem-pc-field-extension-surjective); its base change is surjective
   (lem-weil-pbc-surjective-base-change). Nonemptiness of `X` therefore gives a point
   of the base change and of its reduction.
3. Partition the finite set of irreducible components by chains of intersections.
   Each resulting union is connected; it and its complement are finite unions of
   closed subsets. These clopen unions are exactly the connected components. The
   irreducible components of each union are precisely its ambient components.
4. The reduction is reduced by lem-weil-pbc-reduced-induced-closed-subscheme, and
   open restriction preserves its local rings. Locally, base change tensors affine
   finite-type algebras with the extension field; reduction takes their nilradical
   quotients. Principal open neighbourhoods in the component have localizations
   of these quotients as coordinate rings. All these operations preserve finite
   generation (lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-affine-ideals-closed-subscheme). Thus the component is locally of
   finite type over the extension field, without requiring quasi-compactness.
5. The base-change projection to `X` is open by
   lem-sc-scheme-over-field-universally-open. It is closed: algebraicity makes the
   field extension integral; integrality is preserved by base change
   (lem-sbc-integral-morphism-base-change) and implies universal closedness
   (pqf-lem-integral-univclosed). The nonempty clopen component therefore has
   nonempty clopen image in connected `X`. Its image is all of `X`. -/
theorem geometric_connected_component_surjective
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    (X : Scheme.{u}) [ConnectedSpace X] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (hcomponents : (irreducibleComponents X).Finite) :
    (irreducibleComponents
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme).Finite ∧
    Nonempty
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme ∧
    ∀ z : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme,
      ∃ U : (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme.Opens,
        (U : Set _) = connectedComponent z ∧
        IsClosed (U : Set (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme) ∧
        ConnectedSpace U.toScheme ∧ IsReduced U.toScheme ∧
        LocallyOfFiniteType
          (U.ι ≫ (pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (irreducibleComponents U.toScheme).Finite ∧
        Surjective
          (U.ι ≫ (pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫
            pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

end AlgebraicGeometry.Scheme
