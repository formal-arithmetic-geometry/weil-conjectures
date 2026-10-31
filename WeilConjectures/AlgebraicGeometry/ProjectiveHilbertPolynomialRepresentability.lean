/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperHilbertPresheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.NoetherianDvrProperness
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Projectivity of Hilbert polynomial components

Source: Grothendieck, Bourbaki Expose 221, Theorems 3.1--3.2, the Hilbert specialization
after Proposition 3.8, and Remark 3.9, pp.259--266. Finitely presented families give the
modern extension from locally Noetherian test schemes to all test schemes.
(blueprint: lem-sfb-projective-hilbert-polynomial-representability)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The full Hilbert functor is represented by the coproduct of its H-projective numerical
polynomial components. The representing equivalence carries the identity to the universal
closed family. Its naturality is precisely ideal-sheaf pullback. The last clause records
arbitrary base change of that family and of every component, including the representing
identification. There is no flatness hypothesis on the ambient scheme.

Source: Grothendieck, Bourbaki Expose 221, Theorems 3.1--3.2 and the Hilbert specialization
following Proposition 3.8; Remark 3.9, pp.259--266.

Proof plan (the nine steps of the node):
1. Closed immersions, flatness and finite presentation survive pullback. The locality lemma
   lem-sfb-flat-projective-hilbert-polynomial-locality decomposes each test scheme into the
   open and closed constant-polynomial loci, including the zero polynomial.
2. Choose m from lem-sfb-hilbert-uniform-section-bound and use the free ambient coordinate
   module, not sections of the possibly nonflat ambient scheme. The Grassmannian of rank
   P(m) quotients is H-projective by lem-sfb-free-quotient-grassmann-projective. Impossible
   ranks give empty parameter schemes.
3. On an affine base, express the ambient closed scheme by its homogeneous ideal using
   lem-sfb-projective-closed-subscheme-homogeneous-ideal. Quotient the polynomial algebra
   by this ideal and the universal degree-m kernel. Apply lem-sfb-graded-tail-rank-stratum
   to impose rank P(d) in all degrees d >= m.
4. By lem-sfb-flat-graded-tail-proj, Proj of this quotient is a flat finitely presented
   closed family. Conversely uniform generation of ideals produces the Grassmannian map
   and its factorization through the rank stratum.
5. The two constructions are inverse: their degree-m quotient maps are surjections between
   locally free modules of equal rank and hence isomorphisms; uniform ideal generation
   recovers the actual closed subscheme. Restriction and multiplication commute with base
   change by the uniform-section-bound and flat-graded-tail-Proj lemmas.
6. Uniqueness of representing objects and relative affine-open gluing assemble the local
   strata and universal ideals. The morphism to the Grassmannian is an immersion, and
   composition and quasi-compactness permanence give finite type over the Noetherian base.
7. Over a DVR, contract the generic-fibre ideal on every affine chart. Localization
   compatibility glues the contractions. Their quotients are torsion-free, hence flat by
   lem-trf-valuation-torsionfree-flat, and finite presentation follows from Noetherianity.
   Local constancy preserves the polynomial. Flatness forces every other extension ideal
   to equal this contraction, proving uniqueness.
8. Apply lem-sfb-noetherian-dvr-properness. A proper morphism to a separated Grassmannian
   is proper by lem-weil-pbc-proper-to-separated; a proper immersion is closed by
   lem-weil-pbc-proper-immersion-closed. Compose with the Plucker closed immersion, using
   lem-weil-pbc-closed-immersion-comp, to obtain H-projectivity and its consequences.
9. Take the coproduct of the components and their universal families. The canonical
   polynomial-locus decomposition on a test scheme gives the representing bijection.
   Iterated fibre products identify all families after arbitrary base change; uniqueness
   of representation identifies the pulled-back components and universal family. The
   empty family is retained, with zero-polynomial component the base scheme.
(blueprint: lem-sfb-projective-hilbert-polynomial-representability) -/
theorem exists_projective_hilbert_polynomial_representation
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (E : Over S) (n : ℕ) (i : E.left ⟶ ℙ(ULift.{u} (Fin (n + 1)); S))
    [IsClosedImmersion i] (hi : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) = E.hom) :
    ∃ (H : Over S) (e : (properHilbertPresheaf E.hom).RepresentableBy H)
      (HP : NumericalHilbertPolynomial → Over S) (ι : ∀ P, HP P ⟶ H),
      Nonempty (IsColimit (Cofan.mk H ι)) ∧
      (∀ P, IsHProjective (HP P).hom ∧ IsSeparated (HP P).hom ∧
        LocallyOfFiniteType (HP P).hom ∧ QuasiCompact (HP P).hom) ∧
      (∀ (P : NumericalHilbertPolynomial) (T : Over S) (k : T ⟶ H),
        HasProjectiveFibreHilbertPolynomial E.hom i T (e.homEquiv k).1 P.1 ↔
          ∃! l : T ⟶ HP P, l ≫ ι P = k) ∧
      (∀ (T : Over S) (k : T ⟶ H),
        (e.homEquiv k).1 = (e.homEquiv (𝟙 H)).1.comap (baseChangeMap E.hom k)) ∧
      (∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        ∃ (Hb : Over S') (h : Hb.left ⟶ H.left)
          (eb : (properHilbertPresheaf (pullback.snd E.hom g)).RepresentableBy Hb)
          (a : pullback (pullback.snd E.hom g) Hb.hom ⟶ pullback E.hom H.hom),
          IsPullback h Hb.hom H.hom g ∧
          a ≫ pullback.fst E.hom H.hom =
            pullback.fst (pullback.snd E.hom g) Hb.hom ≫ pullback.fst E.hom g ∧
          a ≫ pullback.snd E.hom H.hom =
            pullback.snd (pullback.snd E.hom g) Hb.hom ≫ h ∧
          (eb.homEquiv (𝟙 Hb)).1 = (e.homEquiv (𝟙 H)).1.comap a ∧
          (∀ P : NumericalHilbertPolynomial,
            ∃ (HPb : Over S') (hP : HPb.left ⟶ (HP P).left) (ιb : HPb ⟶ Hb),
              IsPullback hP HPb.hom (HP P).hom g ∧
              hP ≫ (ι P).left = ιb.left ≫ h ∧
              ∀ (T : Over S') (k : T ⟶ Hb),
                HasProjectiveFibreHilbertPolynomial (pullback.snd E.hom g)
                  (pullback.fst E.hom g ≫ i) T (eb.homEquiv k).1 P.1 ↔
                    ∃! l : T ⟶ HPb, l ≫ ιb = k)) := by
  sorry

end AlgebraicGeometry
