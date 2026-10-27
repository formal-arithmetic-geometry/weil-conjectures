/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import Sheaf.TraceFormula.StrictHenselizationTensorFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.RingTheory.EquivariantFibreProductRefinement
import Sheaf.RingTheory.TransitiveProductInertiaComponent
import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting
import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint
import WeilConjectures.Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleRegularDivisorBaseChange
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClopenRestrictionRank
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Pointed etale inertia slices of finite normal quotients

Source: Stacks Project, Tag 0BST, lemma-inertia-invariants-etale, proof; normal,
generically free finite-scheme specialization and strict localization, compared with
ILO VI, paragraph after 3.5, printed p. 74
(blueprint: lem-per-finite-quotient-inertia-slice).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every prescribed pointed etale neighbourhood admits an integral affine inertia slice.
The subgroup parameter is identified with the geometric stabilizer by `hH`. The invariant
sheaf conditions compare actual pullbacks and restrictions on common subopens. The torsor
on a dense etale open is the actual base change of `p`, with its induced action, expressed
through an isomorphism of covers. The strict-local ring action is inverse pullback by the
original stabilizer action, and its structural ring map is the canonical one.

Source: Stacks Project, Tag 0BST, proof; ILO VI after 3.5, printed p. 74
(blueprint: lem-per-finite-quotient-inertia-slice).

Proof, following the accepted ten-step DAG split:
1. Choose affine pointed opens inside the prescribed neighbourhood and the base. Finiteness
   makes the inverse image affine. Etale flatness and flat base change of invariants identify
   its invariant algebra with the base. Use lem-weil-pbc-finite-morphism-permanence,
   pqf-lem-affine-open-locnoeth, lem-weil-pbc-etale-algebra-finite-presentation-localization,
   lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-etale-algebra-flat,
   lem-weil-pbc-etale-composition-cancellation and lem-dl-a1-flat-base-change-finite-invariants.
2. Apply lem-dl-a1-geometric-point-etale-idempotents to separate the geometric lifts after a
   pointed etale extension. The extension is Noetherian by finite presentation. Apply
   lem-sbc-etale-regular-divisor-base-change with auxiliary element 1 to get regularity.
   By rem-pc-regular-normal, restrict to the integral clopen component containing the point.
3. Each factor has one prime over the pointing, with purely inseparable residue extension,
   by lem-dl-a1-integral-geometric-point-existence and
   lem-dl-a1-unique-geometric-point-pure-residue; integrality uses
   lem-weil-pbc-finite-algebra-is-integral. Apply
   lem-dl-a1-equivariant-fibre-product-refinement and a principal localization so that the
   group permutes the factors. Flat base change preserves the invariant algebra.
4. By lem-dl-a1-transitive-product-inertia-component the selected factor has stabilizer H,
   and its invariant algebra is the base. Take its spectrum V and base spectrum T. Its
   inclusion into the pullback is clopen, so the map to X is pointed etale, using
   lem-weil-pbc-etale-scheme-base-change and etale composition. Projection of a finite
   generating family proves p finite, and the structural square commutes.
5. By lem-fin-etale-normal-components, rem-pc-regular-normal and Noetherian finite-type
   ascent, V is normal Noetherian. Its component containing the unique fibre point is
   H-stable. Its idempotent belongs to the invariant base domain, so equals 1: V is integral.
   The open image of v meets the dense free locus, proving faithfulness; use
   lem-weil-pbc-etale-morphism-open-map.
6. Invariant-algebra integrality and lem-weil-pbc-integral-injective-lying-over give
   surjectivity; use lem-dl-a1-finite-invariant-prime-orbits-residues. Flat invariants on
   principal opens give the invariant structure sheaf. Two geometric lifts differ by an
   element of G, which must preserve the selected factor, hence belongs to H.
7. Any dense etale open meets the open image of T. The restrictions of T and V are nonempty
   integral and thus connected. Apply lem-weil-pbc-finite-etale-clopen-restriction-rank,
   lem-weil-pbc-finite-flat-rank-iso and lem-weil-pbc-finite-etale-etale-local-split.
   Constant rank and one free fibre give rank |H|. Transitivity then gives simple
   transitivity in every fibre. Finite morphism permanence and etale base change apply.
8. If |H| is a unit at x, it is a unit at y. Restrict to the principal open D(|H|).
   All conclusions restrict; faithfulness follows again from the dense free locus.
9. lem-trf-ind-etale-strict-local-invariance identifies the two strict rings. Apply
   lem-trf-finite-base-strict-localization: the unique geometric fibre point gives one
   finite local factor. lem-sbc-affine-strict-henselization-structural-flat and flat
   base change of invariants identify the canonical image of R with C^H.
10. V has a normal domain of sections. Its strict ring is a pointed etale filtered
    colimit. lem-weil-pbc-etale-colimit-normal-local-domain gives normality and injectivity
    from that domain. Equivariance then transports faithfulness to C. Use
    def-weil-pbc-strict-henselization-limit and
    lem-weil-pbc-strict-henselization-functoriality.
-/
theorem finiteQuotient_exists_pointedEtale_inertiaSlice
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hY : IsRegularScheme Y)
    (hX : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {G : Type v} [Group G] [Finite G] (a : G →* Aut X)
    (q : X ⟶ Y) [IsFinite q] [Surjective q]
    (hinvariant : ∀ g : G, (a g).hom ≫ q = q)
    (hgeometric : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (z w : Spec (.of K) ⟶ X), z ≫ q = w ≫ q → ∃ g : G, z ≫ (a g).hom = w)
    (hsheaf : ∀ U : Y.Opens,
      Function.Injective (q.app U).hom ∧
      ∀ s : Γ(X, q ⁻¹ᵁ U),
        (s ∈ Set.range (q.app U).hom ↔
          ∀ (g : G) (W : X.Opens) (hW : W ≤ q ⁻¹ᵁ U)
            (hWg : W ≤ (a g).hom ⁻¹ᵁ (q ⁻¹ᵁ U)),
            ((a g).hom.appLE (q ⁻¹ᵁ U) W hWg).hom s =
              (X.presheaf.map (homOfLE hW).op).hom s))
    (hfree : ∃ U : X.Opens, Dense (U : Set X) ∧
      (∀ g : G, (a g).hom ⁻¹ᵁ U = U) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (z : Spec (.of K) ⟶ U.toScheme)
        (g : G), z ≫ U.ι ≫ (a g).hom = z ≫ U.ι → g = 1)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barX : Spec (.of Ω) ⟶ X)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ barX ≫ (a g).hom = barX)
    (T₀ : Scheme.PointedEtaleNeighborhood (barX ≫ q)) :
    ∃ (T V : Scheme.{u}) (r : T ⟶ T₀.1.left) (p : V ⟶ T)
      (v : V ⟶ X) (barT : Spec (.of Ω) ⟶ T) (barV : Spec (.of Ω) ⟶ V)
      (b : H →* Aut V),
      IsAffine T ∧ IsIntegral T ∧ IsRegularScheme T ∧ IsNoetherian T ∧ Etale r ∧
      barT ≫ r = T₀.2.left ∧
      IsAffine V ∧ IsNormalScheme V ∧ IsNoetherian V ∧ Etale v ∧
      barV ≫ v = barX ∧ barV ≫ p = barT ∧
      v ≫ q = p ≫ r ≫ T₀.1.hom ∧ IsFinite p ∧ Surjective p ∧
      (∀ h : H, (b h).hom ≫ v = v ≫ (a h.val).hom) ∧
      (∀ h : H, (b h).hom ≫ p = p) ∧ Function.Injective b ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (z w : Spec (.of K) ⟶ V),
        z ≫ p = w ≫ p → ∃ h : H, z ≫ (b h).hom = w) ∧
      (∀ U : T.Opens,
        Function.Injective (p.app U).hom ∧
        ∀ s : Γ(V, p ⁻¹ᵁ U),
          (s ∈ Set.range (p.app U).hom ↔
            ∀ (h : H) (W : V.Opens) (hW : W ≤ p ⁻¹ᵁ U)
              (hWh : W ≤ (b h).hom ⁻¹ᵁ (p ⁻¹ᵁ U)),
              ((b h).hom.appLE (p ⁻¹ᵁ U) W hWh).hom s =
                (V.presheaf.map (homOfLE hW).op).hom s)) ∧
      (∀ U : Y.Opens, Dense (U : Set Y) → Etale (pullback.snd q U.ι) →
        ∃ (c : Scheme.GaloisCoverAction H (pullback (r ≫ T₀.1.hom) U.ι))
          (e : c.Z ≅ pullback p (pullback.fst (r ≫ T₀.1.hom) U.ι)),
          ConnectedSpace c.Z ∧
          c.π = e.hom ≫ pullback.snd p (pullback.fst (r ≫ T₀.1.hom) U.ι) ∧
          ∀ h : H,
            c.smul h ≫ e.hom ≫ pullback.fst p (pullback.fst (r ≫ T₀.1.hom) U.ι) =
              e.hom ≫ pullback.fst p (pullback.fst (r ≫ T₀.1.hom) U.ι) ≫ (b h).hom) ∧
      (IsUnit (Nat.card H : X.residueField (barX (IsLocalRing.closedPoint Ω))) →
        IsUnit (Nat.card H : Γ(T, ⊤))) ∧
      IsIso (Scheme.strictHenselizationMap (r ≫ T₀.1.hom) barT) ∧
      IsIso (Scheme.strictHenselizationMap v barV) ∧
      ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing (barX ≫ q)))
        (_ : IsLocalRing (Scheme.strictHenselizationRing barX))
        (β : H →* (Scheme.strictHenselizationRing barX ≃+*
          Scheme.strictHenselizationRing barX)),
        IsDomain (Scheme.strictHenselizationRing barX) ∧
        IsIntegrallyClosed (Scheme.strictHenselizationRing barX) ∧
        (strictHenselizationRingMap q barX).Finite ∧
        IsLocalHom (strictHenselizationRingMap q barX) ∧ Function.Injective β ∧
        (∀ h : H, (β h).toRingHom =
          strictHenselizationRingMapEq (a (h⁻¹).val).hom barX
            ((hH (h⁻¹).val).mp (h⁻¹).property)) ∧
        Function.Injective (strictHenselizationRingMap q barX) ∧
        ∀ c : Scheme.strictHenselizationRing barX,
          (c ∈ Set.range (strictHenselizationRingMap q barX) ↔ ∀ h : H, β h c = c) := by
  sorry

end AlgebraicGeometry
