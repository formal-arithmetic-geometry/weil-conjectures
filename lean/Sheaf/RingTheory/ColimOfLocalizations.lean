module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! # Colimit of localizations

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/`,
node `lem-kun-colim-of-localizations`, order 1748 (blueprint: lem-kun-colim-of-localizations).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Pairs (i,g) with g a nonzero element of the i-th subalgebra. Source: blueprint
node lem-kun-colim-of-localizations (blueprint: lem-kun-colim-of-localizations). -/
abbrev LocalizationPair {K : Type v} {B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {I : Type w} (Bi : I → Subalgebra K B) :=
  {p : I × B // p.2 ∈ Bi p.1 ∧ p.2 ≠ 0}

/-- The principal localization attached to a pair. Source: blueprint
node lem-kun-colim-of-localizations (blueprint: lem-kun-colim-of-localizations). -/
abbrev PairLocalization {K : Type v} {B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {I : Type w} (Bi : I → Subalgebra K B) (p : LocalizationPair Bi) :=
  Localization.Away (⟨p.1.2, p.2.1⟩ : Bi p.1.1)

/-- Inclusion of the subalgebras and invertibility of the source denominator in the target
localization. Source: blueprint node lem-kun-colim-of-localizations
(blueprint: lem-kun-colim-of-localizations). -/
def PairLocalizationLE {K : Type v} {B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {I : Type w} (Bi : I → Subalgebra K B)
    (p q : LocalizationPair Bi) : Prop :=
  Bi p.1.1 ≤ Bi q.1.1 ∧
    ∃ x : Bi q.1.1, (x : B) = p.1.2 ∧
      IsUnit (algebraMap (Bi q.1.1) (PairLocalization Bi q) x)

/-- Source: Stacks Project, Tags 00CO, 002F, and 002V; blueprint node
`lem-kun-colim-of-localizations` (blueprint: lem-kun-colim-of-localizations).

Proof:
1. Send a fraction a/gⁿ in each principal localization to the same fraction in Frac(B).
   The localization relation implies equality in the field by cancellation in B. Conversely,
   equality in the field gives cross-multiplication in the subalgebra, proving injectivity.
2. For p ≤ q, invert the image of g in the q-stage and send a/gⁿ to a times this inverse
   to the nth power. The fraction relation proves well-definedness. A ring map extending
   the inclusion must send 1/g to this inverse, proving uniqueness. These maps preserve
   scalars and commute with the embeddings; their identities and compositions follow.
3. The relation is reflexive because g is a unit in its own localization. Transitivity
   follows by transporting inverses along transition maps. Choose (i,1) for nonemptiness.
   For (i,g) and (j,h), choose a stage containing both subalgebras and localize at gh.
   The domain condition gives gh ≠ 0, and h/(gh) and g/(gh) invert g and h. This supplies
   a common upper bound. In the associated thin category parallel arrows are equal.
4. Write any fraction as a/b with b ≠ 0. The union and directedness hypotheses put both
   a and b in one subalgebra, so this fraction comes from its localization at b.
   This includes zero by using a = 0 and b = 1.
5. Given a compatible cocone, evaluate a field element at any stage representing it.
   A common upper stage and the injective embeddings prove independence of the choice.
   Compute sums, products, zero, and one at a common stage to get a ring map. Coverage
   forces uniqueness. When the cocone maps preserve K-scalars, the same construction
   preserves them too, giving the K-algebra universal property.
-/
theorem colim_of_localizations
    {K : Type v} {B : Type u} [CommRing K] [CommRing B] [Algebra K B] [IsDomain B]
    {I : Type w} (Bi : I → Subalgebra K B)
    (hI : Nonempty I)
    (hfin : ∀ i : I, Algebra.FiniteType K (Bi i))
    (hcover : ∀ b : B, ∃ i : I, b ∈ Bi i)
    (hdirected : ∀ i j : I, ∃ k : I, Bi i ≤ Bi k ∧ Bi j ≤ Bi k) :
    ∃ (e : ∀ p : LocalizationPair Bi, PairLocalization Bi p →ₐ[K] FractionRing B)
      (t : ∀ (p q : LocalizationPair Bi),
        PairLocalizationLE Bi p q → PairLocalization Bi p →ₐ[K] PairLocalization Bi q),
      (∀ (p : LocalizationPair Bi), Function.Injective (e p)) ∧
      (∀ (p : LocalizationPair Bi) (x : Bi p.1.1),
        e p (algebraMap (Bi p.1.1) (PairLocalization Bi p) x) =
          algebraMap B (FractionRing B) (x : B)) ∧
      (∀ (p q : LocalizationPair Bi) (h : PairLocalizationLE Bi p q) (x : Bi p.1.1),
        t p q h (algebraMap (Bi p.1.1) (PairLocalization Bi p) x) =
          algebraMap (Bi q.1.1) (PairLocalization Bi q) ⟨(x : B), (h.1 x.property)⟩) ∧
      (∀ (p q : LocalizationPair Bi) (h : PairLocalizationLE Bi p q),
        ∀ f : PairLocalization Bi p →ₐ[K] PairLocalization Bi q,
          (∀ x : Bi p.1.1,
            f (algebraMap (Bi p.1.1) (PairLocalization Bi p) x) =
              algebraMap (Bi q.1.1) (PairLocalization Bi q) ⟨(x : B), (h.1 x.property)⟩) →
          f = t p q h) ∧
      (∀ (p q : LocalizationPair Bi) (h : PairLocalizationLE Bi p q),
        (e q).comp (t p q h) = e p) ∧
      (∀ x : FractionRing B,
        ∃ (p : LocalizationPair Bi) (y : PairLocalization Bi p), e p y = x) ∧
      ∃ (P : Preorder (LocalizationPair Bi))
        (D : @CategoryTheory.Functor (LocalizationPair Bi)
          (@Preorder.smallCategory (LocalizationPair Bi) P) (CommAlgCat.{u} K) inferInstance)
        (c : @Cocone _ _ _ _ D),
        (∀ p q : LocalizationPair Bi,
          @LE.le _ P.toLE p q ↔ PairLocalizationLE Bi p q) ∧
        @IsFiltered (LocalizationPair Bi)
          (@Preorder.smallCategory (LocalizationPair Bi) P) ∧
        (∀ p : LocalizationPair Bi, D.obj p = CommAlgCat.of K (PairLocalization Bi p)) ∧
        c.pt = CommAlgCat.of K (FractionRing B) ∧
        (∀ p : LocalizationPair Bi, HEq (c.ι.app p) (CommAlgCat.ofHom (e p))) ∧
        Nonempty (IsColimit c) ∧
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} K) CommRingCat).mapCocone c)) := by
  sorry

end RingTheory
