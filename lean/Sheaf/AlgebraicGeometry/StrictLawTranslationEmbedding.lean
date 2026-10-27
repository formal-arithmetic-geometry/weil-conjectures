module

public import Sheaf.AlgebraicGeometry.StrictBirationalLaw
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Faithful birational left translations of a strict law

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 5.2 Lemma 4 and preceding
construction, printed pp.118--119 (blueprint: lem-sfb-strict-law-translation-embedding).

The group functor is identified, at each test scheme, with the actual quotient of
relative birational charts. Composition and pullback are characterized on charts;
the natural transformation is characterized by the pulled-back universal translation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open RelativeBirational

/-- Faithful, natural left translations, with compatibility for every representing
open of the rational law and every test scheme, including nonreduced ones.
Source: BLR 5.2 Lemma 4, printed pp.118--119
(blueprint: lem-sfb-strict-law-translation-embedding).

Proof: (1) Form the group of dense-open isomorphisms modulo common-open agreement.
Compose on the intersection with the inverse image of the next domain; intersection
and pullback preserve fibrewise density by lem-sfb-strict-law-base-change and
lem-sfb-smooth-fibrewise-dense-open-base-change. Reversed charts give inverses;
identities and associativity follow from those of morphisms. Pullback of charts gives
the contravariant group functor, with the canonical iterated-pullback identifications.
(2) Pull the universal left chart back along a test point. Its domains remain dense
by the same density lemma. A different multiplication representative agrees on the
whole common domain by schematic density and the closed diagonal. Pullback of the
chart proves naturality. Smoothness of products and opens uses smooth composition
and smoothness of open immersions.
(3) Equality of two translation classes on a dense common open, followed by the
inverse universal right chart, gives equality of the two first coordinates there.
(4) Schematic density makes the equalizer ideal zero, so the coordinates agree on
all of the smooth test family; this does not assume the test scheme reduced.
(5) The smooth finite-type family with nonempty fibres is flat, quasi-compact and
surjective. Uniqueness of fpqc descent of morphisms gives equality of the test points.
(6) Associativity is an equality of morphisms on a common open of the smooth triple
product: extend equality from a fibrewise dense open using the closed diagonal and
schematic density, also for any other multiplication representative.
(7) Specialize that equality along `(a,b,id)`. The common translation domain
`D_b ∩ τ_b⁻¹(D_a) ∩ D_c` is fibrewise dense, since the translations are isomorphisms
of dense opens. Thus `τ_c = τ_a ∘ τ_b` in the quotient, for arbitrary test schemes. -/
theorem strictLaw_translation_embedding
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsStrictlyHenselianLocalRing A]
    (hnormal : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (Y : Over (Spec (CommRingCat.of A))) [Smooth Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsClosedImmersion (pullback.diagonal Y.hom)]
    (hfibres : ∀ s : Spec (CommRingCat.of A), Nonempty (Y.hom.fiber s))
    (m : StrictLaw Y) :
    ∃ (B : (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ GrpCat.{u})
      (e : ∀ T : Over (Spec (CommRingCat.of A)),
        (B.obj (op T)) ≃ SelfMap ((Over.pullback T.hom).obj Y))
      (τ : yoneda.obj Y ⟶ B ⋙ forget GrpCat),
      (∀ (T : Over (Spec (CommRingCat.of A))), Function.Injective (τ.app (op T))) ∧
      (∀ (T : Over (Spec (CommRingCat.of A))) (a : T ⟶ Y),
        ∃ f : Chart ((Over.pullback T.hom).obj Y),
          IsLeftTranslation m T a f ∧ e T (τ.app (op T) a) = f.toSelfMap) ∧
      (∀ (T : Over (Spec (CommRingCat.of A)))
        (f g : Chart ((Over.pullback T.hom).obj Y)),
        ∃ h : Chart ((Over.pullback T.hom).obj Y), IsComposite f g h) ∧
      (∀ (T : Over (Spec (CommRingCat.of A)))
        (f g h : Chart ((Over.pullback T.hom).obj Y)),
        IsComposite f g h →
          e T ((e T).symm f.toSelfMap * (e T).symm g.toSelfMap) = h.toSelfMap) ∧
      (∀ (T T' : Over (Spec (CommRingCat.of A))) (g : T' ⟶ T)
        (f : Chart ((Over.pullback T.hom).obj Y)),
        ∃ f' : Chart ((Over.pullback T'.hom).obj Y),
          RelativeBirational.IsPullback Y g f f') ∧
      (∀ (T T' : Over (Spec (CommRingCat.of A))) (g : T' ⟶ T)
        (f : Chart ((Over.pullback T.hom).obj Y))
        (f' : Chart ((Over.pullback T'.hom).obj Y)),
        RelativeBirational.IsPullback Y g f f' →
          e T' ((B.map g.op) ((e T).symm f.toSelfMap)) = f'.toSelfMap) ∧
      (∀ (T : Over (Spec (CommRingCat.of A))) (a b c : T ⟶ Y)
        (r : RelativeBirational.PartialMap (square Y) Y),
        r.Agrees m.mul → ∀ d : T.left ⟶ r.domain.toScheme,
          d ≫ r.domain.ι ≫ pullback.fst Y.hom Y.hom = a.left →
          d ≫ r.domain.ι ≫ pullback.snd Y.hom Y.hom = b.left →
          d ≫ r.hom = c.left →
          τ.app (op T) c = τ.app (op T) a * τ.app (op T) b) := by
  sorry

end AlgebraicGeometry
