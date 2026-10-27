module

public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.SchemeTheoreticUnion
import Mathlib.Topology.Sets.Closeds

/-! # Open restriction of smooth projective SNC pairs

Source: ILO, Travaux de Gabber, Expose X 2.3, Step 1, printed p.150 and Step 3, p.152;
the relative SNC definition on p.149 and VIII Remark 4.2.2(i), p.118
(blueprint: lem-sfb-open-smooth-snc-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restricting a smooth projective SNC pair to any open preserves the pair, its surviving
components, their intersections and codimensions, and their local parameter equations.
The family `C` is any enumeration of the integral irreducible components of `E`:
`_hunion`, `_hintegral`, and `_hdistinct` specify that enumeration. The regularity assumptions
are the two factors of `IsRegularScheme R`. Stalk ideals use the existing affine-germ
construction. The canonical stalk isomorphism is `U.stalkIso`, directed from the open's
stalk to the ambient stalk; its inverse transports ambient equations to the open.
The canonical identification of each pulled-back closed subscheme with the fibre product
is `Scheme.IdealSheafData.comapIso`. The finite sup of component ideals represents their
scheme-theoretic intersection, including the empty sup, which cuts out the whole ambient.

Source: ILO Expose X 2.3, Steps 1 and 3, pp.150,152; relative SNC definition p.149;
VIII Remark 4.2.2(i), p.118 (blueprint: lem-sfb-open-smooth-snc-restriction).

Proof:
1. For every point of an open, restriction and inclusion of neighbourhoods give inverse
   maps on germs. Thus `U.stalkIso` identifies the local rings, maximal ideals and ideals.
2. An open immersion is smooth, and smooth morphisms compose
   (lem-pc-open-immersion-smooth-composition). Apply this also to every component intersection.
3. Choose a closed projective-space embedding of R (def-kun-projective). Remove from its
   target the closed image of R minus U. The restricted map is closed in this open target
   by lem-weil-pbc-thickening-open-restriction, hence is a locally closed immersion.
4. The same open-restriction lemma identifies each restricted ideal sheaf. Its closed
   subscheme represents the pullback: a map factors through it exactly when its ambient map
   factors through the original closed subscheme and through U (def-pc-fibre-product).
5. Reducedness follows from the unchanged stalks. On a principal open a Cartier generator
   f remains a nonzerodivisor: g^m*f*a=0 implies g^m*a=0. Nonempty open restrictions of the
   integral components are integral (def-nagata-effective-cartier-ideal,
   def-pc-reduced-scheme, def-pc-integral-scheme).
6. Closure and intersection with an open identify irreducible closed subsets meeting it
   (lem-weil-pbc-open-subspace-irreducible-closed-correspondence). Maximal ones are precisely
   the surviving components, and remain distinct. The union restricts because its ideal
   is the finite intersection of component ideals (lem-weil-pbc-scheme-theoretic-union).
7. The universal property identifies each restricted intersection with the pullback of the
   original intersection. Affine opens in U are affine opens in R, with the same rings and
   ideals; minimal-prime heights therefore remain the original cardinality. Under the stalk
   isomorphism the maximal ideal and Krull dimension are unchanged, so every regular
   parameter list and each of its component equations transports to the open.
8. Open subschemes remain locally Noetherian (pqf-def-locnoeth). Their local rings, and
   those of every intersection, remain regular with the same dimension formula. Radicality
   and the effective Cartier condition restrict, giving IsStrictNormalCrossingsBoundary.
   Empty U has no points or surviving components; empty E has unit ideal and no components;
   an empty index subset cuts out U with codimension zero. -/
theorem open_smooth_snc_restriction
    {F : Type u} [Field F] {R : Scheme.{u}} (f : R ⟶ Spec (.of F))
    [Smooth f] [IsHProjective f] [IsLocallyNoetherian R] [IsRegular R]
    (E : R.IdealSheafData) (_hE : E.IsSmoothStrictNormalCrossingsDivisor f)
    (_hboundary : IsStrictNormalCrossingsBoundary E)
    (n : ℕ) (C : Fin n → R.IdealSheafData)
    (_hunion : E = ⨅ i, C i) (_hintegral : ∀ i, IsIntegral (C i).subscheme)
    (_hdistinct : ∀ i j, (C i).support ≤ (C j).support → i = j)
    (_hparameters : ∀ x : R, ∃ (t : List (R.presheaf.stalk x))
      (a : {i : Fin n // x ∈ (C i).support} ↪ Fin t.length),
      IsLocalRing.IsRegularSystemOfParameters t ∧
        ∀ i, HilbertSamuel.stalkIdeal (C i.1) x = Ideal.span {t.get (a i)})
    (U : R.Opens) :
    Smooth (U.ι ≫ f) ∧
      (∃ (N : ℕ) (j : U.toScheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of F))),
        IsImmersion j ∧ j ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of F)) ↘ Spec (.of F) =
          U.ι ≫ f) ∧
      IsReduced (E.comap U.ι).subscheme ∧ (E.comap U.ι).IsInvertible ∧
      (E.comap U.ι = ⨅ i, (C i).comap U.ι) ∧
      (∀ i, Nonempty ((C i).comap U.ι).subscheme →
        IsIntegral ((C i).comap U.ι).subscheme) ∧
      (∀ i j, Nonempty ((C i).comap U.ι).subscheme →
        Nonempty ((C j).comap U.ι).subscheme →
        ((C i).comap U.ι).support = ((C j).comap U.ι).support → i = j) ∧
      (Set.image (fun Z : Set (E.comap U.ι).subscheme ↦
          (E.comap U.ι).subschemeι '' Z)
        (irreducibleComponents (E.comap U.ι).subscheme) =
          {Z | ∃ i, Nonempty ((C i).comap U.ι).subscheme ∧
            Z = (((C i).comap U.ι).support : Set U.toScheme)}) ∧
      (∀ J : Finset (Fin n),
        J.sup (fun i ↦ (C i).comap U.ι) = (J.sup C).comap U.ι ∧
        Smooth ((J.sup (fun i ↦ (C i).comap U.ι)).subschemeι ≫ U.ι ≫ f) ∧
        ∀ (V : U.toScheme.affineOpens) (p : Ideal Γ(U.toScheme, V.1)),
          p ∈ ((J.sup (fun i ↦ (C i).comap U.ι)).ideal V).minimalPrimes →
            p.height = (J.card : ℕ∞)) ∧
      (∀ x : U.toScheme,
        (∀ i, (HilbertSamuel.stalkIdeal (C i) x.1).map (U.stalkIso x).inv.hom =
          HilbertSamuel.stalkIdeal ((C i).comap U.ι) x) ∧
        ∀ t : List (R.presheaf.stalk x.1), IsLocalRing.IsRegularSystemOfParameters t →
          IsLocalRing.IsRegularSystemOfParameters (t.map (U.stalkIso x).inv.hom) ∧
          ∀ (i : Fin n) (a : Fin t.length),
            HilbertSamuel.stalkIdeal (C i) x.1 = Ideal.span {t.get a} →
              HilbertSamuel.stalkIdeal ((C i).comap U.ι) x =
                Ideal.span {(U.stalkIso x).inv.hom (t.get a)}) ∧
      IsRegularScheme U.toScheme ∧ IsStrictNormalCrossingsBoundary (E.comap U.ι) := by
  sorry

end AlgebraicGeometry
