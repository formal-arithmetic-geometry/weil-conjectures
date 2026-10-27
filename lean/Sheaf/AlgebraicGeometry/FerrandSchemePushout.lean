module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed

/-! # Ferrand pushouts of schemes

Source: Stacks Project, More on Morphisms, Tags 0E25, 0E26, 0E27 and 0ET0
(blueprint: lem-sfb-ferrand-scheme-pushout).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed immersion and an integral map with affine neighbourhoods of the pinched fibres
admit a Ferrand pushout, with its topology, sheaf, charts and relative properties.
Source: Stacks Project, More on Morphisms, Tags 0E25, 0E26, 0E27 and 0ET0
(blueprint: lem-sfb-ferrand-scheme-pushout).

The pullback of section rings on every open expresses the structure-sheaf fibre product:
limits of sheaves of rings are computed on sections. The chart isomorphisms use these same
section rings; their two equations specify the spectrum maps of the ring projections.
The complement cocone being a colimit says its canonical coproduct map is an isomorphism.

Proof plan from the node:
1. Form the quotient of |X| disjoint union |T| identifying i(z) with j(z). On each open,
   take pairs of sections agreeing on Z; componentwise gluing makes a sheaf of rings.
2. Use lem-sfb-integral-pinching-compatible-affines to obtain saturated affine pairs.
   The common inverse image is affine and its X-section map is surjective. Apply
   lem-sfb-ring-fibre-product-spectrum to identify their image with the fibre-product spectrum.
3. On principal opens, use lem-weil-pbc-affine-open-section-vanishing-prime and the localized
   ring identity in lem-sfb-ring-fibre-product-spectrum. These identifications respect
   restriction. The basis lem-weil-pbc-spec-localization-away-basic-open identifies the sheaves.
4. The image of Z is closed, since i is closed and j is closed by pqf-lem-integral-univclosed.
   Off this image there are no identifications. Affine charts on the two complements,
   with empty inverse images in the other component, complete an affine cover of the quotient.
5. By pqf-lem-affine-local-target, a and b are affine. The ring projection onto the T-ring
   is surjective, by lifting along the X-to-Z surjection. The quotient topology makes b a
   closed embedding; its local ring surjections make it a closed immersion.
6. For x in the X-ring, lift a monic integral equation for its image in the Z-ring.
   Its value lies in the kernel of X-to-Z. Subtract this kernel element from the constant
   coefficient, obtaining a monic equation for x over the fibre-product ring. Then use
   lem-sfb-integral-affine-cover-criterion to obtain integrality of a.
7. If I is the kernel of X-to-Z, the kernel of the projection to the T-ring is the same I.
   Thus A tensor_B E = A/I = D. Apply lem-weil-pbc-fibre-product-affine-spectra on charts
   and lem-weil-pbc-scheme-morphism-gluing to obtain the cartesian square.
8. By lem-sfb-affine-closed-pinching-pushout, every principal-open restriction is a pushout.
   Use the principal-open basis and lem-weil-pbc-scheme-morphism-gluing to glue unique maps
   to arbitrary schemes. The same argument within any open gives the open restriction clause.
9. When X and T are affine, the single affine pair gives Spec of the ring fibre product,
   with its projection maps, also by lem-sfb-affine-closed-pinching-pushout.
10. The map from X disjoint union T is surjective and universally closed: use
    pqf-lem-integral-univclosed and lem-weil-pbc-closed-immersion-integral-separated-uc.
    If X and T are separated over S, so is their coproduct, by the diagonal on its four
    clopen product components. Apply lem-weil-pbc-surjective-universally-closed-separated.
11. Under the finite-type hypotheses, refine charts over affine opens of S by principal opens.
    By pqf-lem-affine-open-locnoeth their base ring is Noetherian, and by
    lem-weil-pbc-lft-affine-pairs their section rings are of finite type over it.
    Finite algebra generators of D over E are integral, hence generate a finite E-module
    by lem-sc-finite-generated-integral-subring. Lift module generators to A.
12. Those lifts together with 1 generate A over B = A times_D E; E is cyclic over B.
    Thus A times E is module-finite over B and finite type over the Noetherian base.
    Apply lem-sfb-artin-tate-subalgebra-finite-type to conclude B is finite type.
    The affine cover proves that P is locally of finite type over S.
-/
theorem exists_ferrand_scheme_pushout
    (S : Scheme.{u}) (Z X T : Over S) (i : Z ⟶ X) (j : Z ⟶ T)
    [IsClosedImmersion i.left] [IsIntegralHom j.left]
    (h : ∀ t : T.left, ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∀ z : Z.left, j.left z = t → i.left z ∈ U) :
    ∃ (P : Over S) (a : X ⟶ P) (b : T ⟶ P),
      ∃ hs : IsPushout i.left j.left a.left b.left,
      IsPushout i.left.base j.left.base a.left.base b.left.base ∧
      IsAffineHom a.left ∧ IsIntegralHom a.left ∧ IsClosedImmersion b.left ∧
      IsPullback i.left j.left a.left b.left ∧
      (∀ W : P.left.Opens,
        IsPullback (a.left.app W) (b.left.app W) (i.left.app (a.left ⁻¹ᵁ W))
          (j.left.appLE (b.left ⁻¹ᵁ W) ((i.left ≫ a.left) ⁻¹ᵁ W)
            (le_of_eq (congrArg (fun f : Z.left ⟶ P.left ↦ f ⁻¹ᵁ W) hs.w)))) ∧
      (∃ (ι : Type u) (W : ι → P.left.Opens), iSup W = ⊤ ∧ ∀ k : ι,
        IsAffineOpen (W k) ∧ IsAffineOpen (a.left ⁻¹ᵁ W k) ∧
        IsAffineOpen (b.left ⁻¹ᵁ W k) ∧
        IsAffineOpen ((i.left ≫ a.left) ⁻¹ᵁ W k) ∧
        Function.Surjective (i.left.app (a.left ⁻¹ᵁ W k)) ∧
        ∃ e : (W k).toScheme ≅ Spec
            (pullback (i.left.app (a.left ⁻¹ᵁ W k))
              (j.left.appLE (b.left ⁻¹ᵁ W k) ((i.left ≫ a.left) ⁻¹ᵁ W k)
                (le_of_eq (congrArg (fun f : Z.left ⟶ P.left ↦ f ⁻¹ᵁ W k) hs.w)))),
          morphismRestrict a.left (W k) ≫ e.hom = (a.left ⁻¹ᵁ W k).toSpecΓ ≫
            Spec.map (pullback.fst _ _) ∧
          morphismRestrict b.left (W k) ≫ e.hom = (b.left ⁻¹ᵁ W k).toSpecΓ ≫
            Spec.map (pullback.snd _ _)) ∧
      (∃ (U : X.left.Opens) (V : T.left.Opens) (W : P.left.Opens)
          (f : U.toScheme ⟶ W.toScheme) (g : V.toScheme ⟶ W.toScheme),
        (U : Set X.left) = (Set.range i.left)ᶜ ∧
        (V : Set T.left) = (Set.range j.left)ᶜ ∧
        (W : Set P.left) = (Set.range (i.left ≫ a.left))ᶜ ∧
        f ≫ W.ι = U.ι ≫ a.left ∧ g ≫ W.ι = V.ι ≫ b.left ∧
        Nonempty (IsColimit (BinaryCofan.mk f g))) ∧
      (IsAffine X.left → IsAffine T.left → IsAffine P.left ∧
        Function.Surjective i.left.appTop ∧
        ∃ e : P.left ≅ Spec (pullback i.left.appTop j.left.appTop),
          a.left ≫ e.hom = X.left.toSpecΓ ≫ Spec.map (pullback.fst _ _) ∧
          b.left ≫ e.hom = T.left.toSpecΓ ≫ Spec.map (pullback.snd _ _)) ∧
      (∀ V : P.left.Opens,
        IsPushout
          ((Over.pullback V.ι).map
            (Over.homMk i.left rfl : Over.mk (i.left ≫ a.left) ⟶ Over.mk a.left)).left
          ((Over.pullback V.ι).map
            (Over.homMk j.left hs.w.symm : Over.mk (i.left ≫ a.left) ⟶ Over.mk b.left)).left
          (pullback.snd a.left V.ι) (pullback.snd b.left V.ι)) ∧
      (IsSeparated X.hom → IsSeparated T.hom → IsSeparated P.hom) ∧
      (IsLocallyNoetherian S → LocallyOfFiniteType X.hom → LocallyOfFiniteType T.hom →
        LocallyOfFiniteType Z.hom → LocallyOfFiniteType P.hom) := by
  sorry

end AlgebraicGeometry
