module

public import Sheaf.AlgebraicGeometry.FiberwiseRationalMap
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.AlgebraicGeometry.AffineNonZeroDivisorComplementDense
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.AlgebraicGeometry.FinitePresentationArrowsDescent
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.RingTheory.RegularPrincipalPrimeLocalizationDvr

/-! # Local spreading over a smooth trait

Source: BLR, Néron Models, §2.5 Proposition 5, §4.3 Proposition 5, §4.4 Corollary 4,
printed pp.58, 108, 111 (blueprint: lem-sfb-smooth-trait-local-rational-spreading).

The generic fibre is the scheme-theoretic fibre at the zero prime. Its residue field is
canonically the fraction field. Agreement is expressed on the canonical fibre product of
representative domains; this avoids choosing identifications of iterated base changes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two maps with domains mapping to `X` agree on their canonical common pullback.
Source: BLR §2.5; scheme-theoretic restriction convention.
(blueprint: lem-sfb-smooth-trait-local-rational-spreading). -/
def Scheme.Hom.AgreesOnPullback {A B X Y : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ X)
    (a : A ⟶ Y) (b : B ⟶ Y) : Prop :=
  pullback.fst i j ≫ a = pullback.snd i j ≫ b

/-- The stalk base change of an arrow along the canonical local-scheme morphism.
Source: BLR §4.3 Proposition 5 and §4.4 Corollary 4.
(blueprint: lem-sfb-smooth-trait-local-rational-spreading). -/
noncomputable def Scheme.Hom.stalkBaseChange {X Z : Scheme.{u}} (v : X ⟶ Z) (x : Z) :
    pullback v (Z.fromSpecStalk x) ⟶ Spec (Z.presheaf.stalk x) :=
  pullback.snd _ _

/-- The local extension condition, either for morphisms or for birational representatives.
The complement of the closed point of the local DVR is its fraction-field generic point.
Source: BLR §4.3 Proposition 5 and §4.4 Corollary 4.
(blueprint: lem-sfb-smooth-trait-local-rational-spreading). -/
def SmoothTraitLocalExtension {R : Type u} [CommRing R] [IsDomain R]
    {Z V W : Scheme.{u}} (z : Z ⟶ Spec (.of R)) (v : V ⟶ Z) (w : W ⟶ Z)
    (h : (v ≫ z).fiber (⊥ : PrimeSpectrum R) ⟶ (w ≫ z).fiber (⊥ : PrimeSpectrum R))
    (x : Z) (birational : Bool) : Prop :=
  ∃ d : Scheme.FiberwisePartialMap (v.stalkBaseChange x) (w.stalkBaseChange x),
    (∀ a, v.stalkBaseChange x a ≠ IsLocalRing.closedPoint (Z.presheaf.stalk x) →
      a ∈ d.domain) ∧
    Scheme.Hom.AgreesOnPullback
      (d.domain.ι ≫ pullback.fst v (Z.fromSpecStalk x)) ((v ≫ z).fiberι (⊥ : PrimeSpectrum R))
      (d.hom ≫ pullback.fst w (Z.fromSpecStalk x)) (h ≫ (w ≫ z).fiberι (⊥ : PrimeSpectrum R)) ∧
    (birational = true → ∃ e : Scheme.FiberwisePartialIso
      (v.stalkBaseChange x) (w.stalkBaseChange x), e.toPartialMap = d)

/-- Local rational spreading, its birational form, uniqueness, and trait base change.
Source: BLR §2.5 Proposition 5, §4.3 Proposition 5, §4.4 Corollary 4, pp.58,108,111.
(blueprint: lem-sfb-smooth-trait-local-rational-spreading).

Proof plan (the fifteen steps of the node).
1. Choose a uniformizer pi. DVR factorization identifies R[1/pi] with its fraction field;
   principal localization and open base change identify each generic fibre with D(pi).
2. Finite-type composition and Noetherianity make Z,V,W and all their opens Noetherian,
   quasi-compact and quasi-separated; smooth restrictions are finitely presented.
3. At a component generic point of Z_k, flatness makes pi a nonzerodivisor. The reduced
   special fibre has field stalk there. The fibre-stalk quotient identifies A/pi A with
   that field, so the principal maximal-ideal DVR criterion applies to A.
4. Flatness makes the generic open schematically dense. The separated-target equality
   lemma gives uniqueness on every open, hence agreement of extensions on overlaps.
5. Smooth reduced dense pullback sends special-fibre component generic points to component
   generic points of Z_k; the local dense opens contain all such points above x.
6. Express Spec A as the limit of affine neighbourhoods. Fibre products commute with this
   limit, and quasi-compact opens descend, giving a neighbourhood domain D_N.
7. Finite-presentation arrow descent spreads the supplied local extension to D_N.
8. Limit-map equality after inverting pi arranges exact agreement with h on (D_N)_E.
9. Glue these maps with h on the entire generic fibre. The resulting domain contains all
   component generic points of V_k, so it is dense in both fibres.
10. In the birational case descend both opens and both mutually inverse local maps.
11. Descend their inverse identities and their generic-fibre agreement by limit-map equality.
12. Shrink each neighbourhood to avoid the other finitely many special-fibre components;
    distinct such neighbourhoods then intersect only in the generic fibre.
13. Glue the local isomorphisms and their inverses with h and its inverse. Both resulting
    domains are fibrewise dense. This does not require V to be separated over Z.
14. Under the point-preserving trait map, each new fibre is a residue-field extension of
    the old fibre. Its projection is open, so inverse images of dense opens are dense,
    for arbitrary X without smoothness, finite type or flatness assumptions on X.
15. Base change the representative isomorphism and its inverse; Step 14 supplies the
    required fibrewise density on both sides.
-/
theorem smooth_trait_local_rational_spreading
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z V W : Scheme.{u}} (z : Z ⟶ Spec (.of R)) (v : V ⟶ Z) (w : W ⟶ Z)
    [Smooth z] [LocallyOfFiniteType z] [QuasiCompact z]
    [Smooth v] [LocallyOfFiniteType v] [QuasiCompact v]
    [Smooth w] [LocallyOfFiniteType w] [QuasiCompact w] [IsSeparated w]
    (h : (v ≫ z).fiber (⊥ : PrimeSpectrum R) ⟶ (w ≫ z).fiber (⊥ : PrimeSpectrum R))
    (hh : h ≫ (w ≫ z).fiberι (⊥ : PrimeSpectrum R) ≫ w = (v ≫ z).fiberι (⊥ : PrimeSpectrum R) ≫ v) :
    (∀ ξ : z.fiber (IsLocalRing.closedPoint R), ξ ∈ genericPoints _ →
      ∃ hd : IsDomain (Z.presheaf.stalk (z.fiberι (IsLocalRing.closedPoint R) ξ)),
        @IsDiscreteValuationRing (Z.presheaf.stalk (z.fiberι (IsLocalRing.closedPoint R) ξ))
          _ hd) ∧
    ((∀ ξ : z.fiber (IsLocalRing.closedPoint R), ξ ∈ genericPoints _ →
      SmoothTraitLocalExtension z v w h (z.fiberι (IsLocalRing.closedPoint R) ξ) false) →
      ∃ d : Scheme.FiberwisePartialMap (v ≫ z) (w ≫ z),
        (Set.range ((v ≫ z).fiberι (⊥ : PrimeSpectrum R)) ⊆ (d.domain : Set V)) ∧
        d.hom ≫ w = d.domain.ι ≫ v ∧
        Scheme.Hom.AgreesOnPullback d.domain.ι ((v ≫ z).fiberι (⊥ : PrimeSpectrum R))
          d.hom (h ≫ (w ≫ z).fiberι (⊥ : PrimeSpectrum R))) ∧
    ((IsIso h ∧ ∀ ξ : z.fiber (IsLocalRing.closedPoint R), ξ ∈ genericPoints _ →
      SmoothTraitLocalExtension z v w h (z.fiberι (IsLocalRing.closedPoint R) ξ) true) →
      ∃ e : Scheme.FiberwisePartialIso (v ≫ z) (w ≫ z),
        (Set.range ((v ≫ z).fiberι (⊥ : PrimeSpectrum R)) ⊆ (e.domain : Set V)) ∧
        e.iso.hom ≫ e.target.ι ≫ w = e.domain.ι ≫ v ∧
        Scheme.Hom.AgreesOnPullback e.domain.ι ((v ≫ z).fiberι (⊥ : PrimeSpectrum R))
          (e.iso.hom ≫ e.target.ι) (h ≫ (w ≫ z).fiberι (⊥ : PrimeSpectrum R))) ∧
    (∀ (B : V.Opens) (a b : B.toScheme ⟶ W),
      a ≫ w = B.ι ≫ v → b ≫ w = B.ι ≫ v →
      (B.ι ≫ v ≫ z).fiberι (⊥ : PrimeSpectrum R) ≫ a =
        (B.ι ≫ v ≫ z).fiberι (⊥ : PrimeSpectrum R) ≫ b → a = b) ∧
    (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
      (b : Spec (.of R') ⟶ Spec (.of R)),
      b (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R →
      b (⊥ : PrimeSpectrum R') = (⊥ : PrimeSpectrum R) →
      (∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) (U : X.Opens),
        f.IsFiberwiseDense U →
        (pullback.snd f b).IsFiberwiseDense (pullback.fst f b ⁻¹ᵁ U)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
        (e : Scheme.FiberwisePartialIso f g),
        ∃ e' : Scheme.FiberwisePartialIso (pullback.snd f b) (pullback.snd g b),
          e'.domain = pullback.fst f b ⁻¹ᵁ e.domain ∧
          e'.target = pullback.fst g b ⁻¹ᵁ e.target ∧
          Scheme.Hom.AgreesOnPullback e.domain.ι (e'.domain.ι ≫ pullback.fst f b)
            (e.iso.hom ≫ e.target.ι)
            (e'.iso.hom ≫ e'.target.ι ≫ pullback.fst g b))) := by
  sorry

end AlgebraicGeometry
