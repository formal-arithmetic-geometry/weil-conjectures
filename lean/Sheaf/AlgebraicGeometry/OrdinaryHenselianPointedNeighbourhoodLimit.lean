/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Order.Filter.IsBounded
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Sheaf.RingTheory.EtaleResidueTriplesFiltered
import WeilConjectures.RingTheory.EtaleResidueTripleUnitRefinement
import WeilConjectures.RingTheory.EtaleResidueTripleIdealRefinement
import Sheaf.RingTheory.FilteredColimitFiniteData
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-!
# Ordinary henselian limits of pointed affine étale neighbourhoods

Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), statement and proof;
Categories, Tag 0032, for directed reindexing; Limits of Schemes, Tag 01YW, for the affine
inverse limit (blueprint: lem-per-ordinary-henselian-pointed-neighbourhood-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An ordinary henselian local limit of residue-preserving affine étale neighbourhoods.
Source: Stacks Project, Tag 04GN, with Tags 0032 and 01YW
(blueprint: lem-per-ordinary-henselian-pointed-neighbourhood-limit).

The ring `H` is `c.pt.right`, with structural map `c.pt.hom`. The category
`Under (CommRingCat.of A)` is the category of commutative `A`-algebras. The isomorphisms
`e a` are required to be the residue-field maps induced by the neighbourhood morphisms,
with transport along the displayed point equalities. The last clause is precisely the
unique-factorization property of the inverse limit in schemes over `Spec A`.

Proof, following the eight steps of the node:
1. Take étale residue triples over `A` pointed into `κ(x)` by its identity map. The
   structural residue embedding and the pointing are inverse, since their composite is
   the identity and a field map is injective. An essentially small affine étale cover,
   together with the set of possible primes and pointings on each member, gives a small
   full representative category without changing the pointings or arrows.
2. This category is filtered by `etaleResidueTriples_filtered_part`, which works over an
   arbitrary field. Form its colimit in commutative `A`-algebras. Its underlying ring is
   the filtered ring colimit. The compatible pointings give a map `ψ : H → κ(x)`.
   Directed reindexing at aleph-zero gives a nonempty directed set and the same colimit.
3. Represent each `h : H` at a stage. If `ψ(h)` is nonzero, unit refinement makes its
   representative invertible at a later stage. If `ψ(h)` is zero, ideal refinement puts
   it in the extended prime at a later stage. Cocone compatibility then gives
   `ker ψ = pH`, and every element outside that proper ideal is a unit.
4. Every proper ideal is contained in `pH`, so `H` is local with that maximal ideal.
   Images of denominators outside `p` are units; the fraction formula extends `A → H`
   uniquely to `A_p → H`. Its inverse image of the maximal ideal is `pA_p`, so it is
   local. Fractions representing elements of `κ(x)` show that `ψ` is surjective, hence
   induce the canonical residue isomorphism `κ(x) ≅ H/pH`.
5. Descend the finitely many coefficients of a monic polynomial to a stage, keeping its
   leading coefficient equal to one. For a simple residue root, the standard étale
   algebra adjoining a root and inverting the derivative has a pointing into `κ(x)`.
   It is a successor residue triple. The image of its adjoined root in `H` lifts the
   chosen simple root and is a root of the original polynomial.
6. The local-ring simple-root criterion, equivalently the finite-algebra idempotent
   lifting criterion, proves `HenselianLocalRing H`.
7. Take the distinguished prime at each stage. Triple arrows preserve the primes and
   residue identifications. Since the stage pointing is the composite of its colimit
   leg with `ψ`, the closed point of `H` maps to that distinguished prime. The stage
   morphisms are étale, separated because they are maps between affine schemes, and
   of finite presentation because they are quasi-compact, quasi-separated and locally
   of finite presentation. This does not assume that `A` is Noetherian.
8. The affine spectrum of the ring colimit is the scheme inverse limit, with the
   spectrum maps of the colimit legs as projections (Tag 01YW). All arrows are over
   `Spec A`. The unique factorization of a cone over `Spec A` is again over `Spec A`:
   compose with any projection and use nonemptiness of the index set. This gives the
   final unique-factorization clause with its specified structural map.
-/
theorem exists_ordinary_henselian_pointed_neighbourhood_limit
    (A : Type u) [CommRing A] (x : Spec (CommRingCat.of A)) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ Under (CommRingCat.of A)) (c : Cocone F),
      Nonempty (IsColimit c) ∧
      ∃ hH : HenselianLocalRing c.pt.right,
        letI := hH
        ∃ (xa : ∀ a : I, Spec (F.obj a).right)
          (e : ∀ a : I, (Spec (CommRingCat.of A)).residueField x ≅
            (Spec (F.obj a).right).residueField (xa a)),
          (∀ a : I, IsSeparated (Spec.map (F.obj a).hom) ∧
            Etale (Spec.map (F.obj a).hom) ∧
            LocallyOfFinitePresentation (Spec.map (F.obj a).hom) ∧
            QuasiCompact (Spec.map (F.obj a).hom) ∧
            QuasiSeparated (Spec.map (F.obj a).hom)) ∧
          (∀ a : I, ∃ hx : Spec.map (F.obj a).hom (xa a) = x,
            eqToHom (congrArg (Spec (CommRingCat.of A)).residueField hx.symm) ≫
              (Spec.map (F.obj a).hom).residueFieldMap (xa a) = (e a).hom) ∧
          (∀ (a b : I) (f : a ⟶ b),
            ∃ hx : Spec.map (F.map f).right (xa b) = xa a,
              (e a).hom ≫
                eqToHom (congrArg (Spec (F.obj a).right).residueField hx.symm) ≫
                (Spec.map (F.map f).right).residueFieldMap (xa b) = (e b).hom) ∧
          (∀ a : I, Spec.map (c.ι.app a).right (IsLocalRing.closedPoint c.pt.right) = xa a) ∧
          (∃ g : Localization.AtPrime x.asIdeal →+* c.pt.right,
            IsLocalHom g ∧
              g.comp (algebraMap A (Localization.AtPrime x.asIdeal)) = c.pt.hom.hom) ∧
          x.asIdeal.map c.pt.hom.hom = IsLocalRing.maximalIdeal c.pt.right ∧
          (∃ eH : (Spec (CommRingCat.of A)).residueField x ≅
              CommRingCat.of (c.pt.right ⧸ x.asIdeal.map c.pt.hom.hom),
            CommRingCat.ofHom (algebraMap A x.asIdeal.ResidueField) ≫
                (Scheme.Spec.residueFieldIso (CommRingCat.of A) x).inv ≫ eH.hom =
              CommRingCat.ofHom
                ((Ideal.Quotient.mk (x.asIdeal.map c.pt.hom.hom)).comp c.pt.hom.hom)) ∧
          (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of A))
            (π : ∀ a : I, T ⟶ Spec (F.obj a).right),
            (∀ a : I, π a ≫ Spec.map (F.obj a).hom = t) →
            (∀ (a b : I) (f : a ⟶ b), π b ≫ Spec.map (F.map f).right = π a) →
            ∃! g : T ⟶ Spec c.pt.right,
              g ≫ Spec.map c.pt.hom = t ∧
                ∀ a : I, g ≫ Spec.map (c.ι.app a).right = π a) := by
  sorry

end AlgebraicGeometry
