/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CotangentResolutionCoherence
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.RingTheory.QuotientCotangentConormal
import WeilConjectures.RingTheory.KoszulCotangentConcentration

/-!
# The cotangent complex of a Koszul-regular quotient

Source: Stacks Project, Cotangent Complex, Tag 08SJ (lemma-mod-regular-sequence),
with the canonical conormal identification of lemma-surjection
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing).

The module `I.Cotangent` is Mathlib's `I/I²`. Its single complex in degree `-1`
is `(I/I²)[1]`. The isomorphism is normalized on standard-resolution relation
cycles, so the conclusion specifies the canonical conormal identification.

## Main declarations

* `quotientArrow`, `quotientModel`: the quotient and its recorded standard complex.
* `relationVector`, `conormalHomologyMap`: the explicit conormal normalization.
* `exists_canonical_iso_and_vanishing`: the canonical isomorphism and vanishing.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open Algebra.CotangentResolution

namespace Algebra.KoszulQuotientCotangent

private theorem lift_homology_iso {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (X : DerivedCategory A) (n : ℤ)
    [X.IsGE n] [X.IsLE n] (M : A)
    (h : (DerivedCategory.homologyFunctor A n).obj X ≅ M) :
    ∃ e : X ≅ (DerivedCategory.singleFunctor A n).obj M,
      (DerivedCategory.homologyFunctor A n).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).hom.app M = h.hom := by
  obtain ⟨N, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let H := DerivedCategory.homologyFunctor A n
  let S := DerivedCategory.singleFunctor A n
  let j := DerivedCategory.singleFunctorCompHomologyFunctorIso A n
  let k : N ≅ M := (j.app N).symm ≪≫ (H.mapIso e).symm ≪≫ h
  refine ⟨e ≪≫ S.mapIso k, ?_⟩
  change H.map (e.hom ≫ S.map k.hom) ≫ j.hom.app M = h.hom
  rw [H.map_comp, Category.assoc]
  rw [show H.map (S.map k.hom) ≫ j.hom.app M = j.hom.app N ≫ k.hom from
    j.hom.naturality k.hom]
  dsimp [k]
  simp

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The quotient ring map as an arrow of commutative rings. Source: Stacks,
Tag 08SJ (blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def quotientArrow (R : Type u) [CommRing R] (I : Ideal R) : Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The standard differential complex computing the quotient's cotangent complex.
Source: Stacks, Tags 08PN and 08SJ
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def quotientModel (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R) :=
  differentialComplex (C.differentials (C.standard (quotientArrow R I)))

/-- The relation vector `1 ⊗ d([C(a)] - [0])` in degree `-1` of the actual standard
resolution. Its two faces have zero differential for `a ∈ I`: the first evaluates
it to the base constant `a`, and the second to `[a mod I] - [0] = 0`.
It represents the conormal class of `a`. The cast uses the recorded equality
of the standard resolution's rings with the prescribed polynomial rings.
Source: Stacks, lemma-surjection, equation-comparison-map, and Tag 08SJ
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def relationVector (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R)
    (a : I) : (quotientModel C R I).X (-1) :=
  complexGenerator (C.differentials (C.standard (quotientArrow R I))) 1 1
    (_root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
      ((C.standard_spec (quotientArrow R I)).1 1).symm)
      (MvPolynomial.X (MvPolynomial.C (a : R)) -
        MvPolynomial.X (MvPolynomial.C (0 : R))))

/-- The map on degree `-1` cohomology of a proposed conormal isomorphism, expressed
on the concrete standard complex using the localization and single-complex
comparison isomorphisms. Source: Stacks, lemma-surjection and Tag 08SJ
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def conormalHomologyMap (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R)
    (e : cotangentComplex C (quotientArrow R I) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).obj
        (ModuleCat.of (R ⧸ I) I.Cotangent)) :
    (quotientModel C R I).homology (-1) ⟶ ModuleCat.of (R ⧸ I) I.Cotangent :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).inv.app
      (quotientModel C R I) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).map e.hom ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).hom.app (ModuleCat.of (R ⧸ I) I.Cotangent)

/-- A Koszul-regular quotient has cotangent complex canonically `I/I²[1]`, and
cohomology zero in every degree other than `-1`, without a Noetherian assumption.
The normalization sends the class of `1 ⊗ d([C(a)] - [0])` to `a mod I²` for every
`a ∈ I`; it also asserts that each displayed relation vector is a cycle.
Source: Stacks, Tag 08SJ, with lemma-surjection for the conormal normalization
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing).

Proof:
1. The polynomial Koszul resolution, Tor-independent cotangent base change, and
   the free conormal module of the polynomial augmentation show that the quotient
   cotangent complex is concentrated in degree minus one.
2. Independently apply the general quotient comparison to the identity presentation
   `R → R/I`. Its relative differentials vanish, so the naive comparison identifies
   degree minus one cohomology with `I/I²`. Its projection formula carries each
   standard relation cycle to the corresponding conormal class.
3. An object concentrated in one degree is isomorphic to a single module. Correct
   such an isomorphism by the single of its induced homology automorphism to realize
   precisely the prescribed conormal identification. The localization comparison
   then gives the asserted normalization on the concrete standard complex.
4. The two standard t-structure bounds give zero cohomology in every other degree.
   Empty sequences, the unit ideal, and the zero ring need no separate argument. -/
theorem exists_canonical_iso_and_vanishing (C : Coherence.{u})
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    (∃ e : cotangentComplex C (quotientArrow R (Ideal.span (Set.range f))) ≅
        (DerivedCategory.singleFunctor
          (ModuleCat.{u} (CommRingCat.of (R ⧸ Ideal.span (Set.range f)))) (-1)).obj
            (ModuleCat.of (R ⧸ Ideal.span (Set.range f))
              (Ideal.span (Set.range f)).Cotangent),
      ∀ a : Ideal.span (Set.range f),
        ∃ z : (quotientModel C R (Ideal.span (Set.range f))).cycles (-1),
          (quotientModel C R (Ideal.span (Set.range f))).iCycles (-1) z =
              relationVector C R (Ideal.span (Set.range f)) a ∧
            conormalHomologyMap C R (Ideal.span (Set.range f)) e
              ((quotientModel C R (Ideal.span (Set.range f))).homologyπ (-1) z) =
                (Ideal.span (Set.range f)).toCotangent a) ∧
      ∀ i : ℤ, i ≠ -1 → IsZero
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (CommRingCat.of (R ⧸ Ideal.span (Set.range f)))) i).obj
            (cotangentComplex C (quotientArrow R (Ideal.span (Set.range f))))) := by
  let I := Ideal.span (Set.range f)
  let A := ModuleCat.{u} (CommRingCat.of (R ⧸ I))
  let L := cotangentComplex C (quotientArrow R I)
  obtain ⟨hge, hle⟩ := koszul_cotangent_concentrated C R r f hreg
  have : L.IsGE (-1) := hge
  have : L.IsLE (-1) := hle
  obtain ⟨h, hz⟩ := quotient_conormal_homology C R I
  let t := (DerivedCategory.homologyFunctorFactors A (-1)).app (quotientModel C R I)
  obtain ⟨e, he⟩ := lift_homology_iso L (-1) (ModuleCat.of (R ⧸ I) I.Cotangent)
    (t ≪≫ h)
  have hmap : conormalHomologyMap C R I e = h.hom := by
    change t.inv ≫ (DerivedCategory.homologyFunctor A (-1)).map e.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A (-1)).hom.app
        (ModuleCat.of (R ⧸ I) I.Cotangent) = h.hom
    exact (congrArg (fun g ↦ t.inv ≫ g) he).trans (by simp)
  refine ⟨⟨e, ?_⟩, ?_⟩
  · intro a
    obtain ⟨z, hcycle, hclass⟩ := hz a
    exact ⟨z, hcycle, by rw [hmap]; exact hclass⟩
  · intro i hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact DerivedCategory.isZero_of_isGE L (-1) i hlt
    · exact DerivedCategory.isZero_of_isLE L (-1) i hgt

end Algebra.KoszulQuotientCotangent
