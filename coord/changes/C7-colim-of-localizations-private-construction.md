# RingTheory.colim_of_localizations

## Reason

The proof adds a local `section Construction`, its explicit `variable` context,
and `omit [IsDomain B] in` commands for private helpers. Five newly added private
constructions (`embedding`, `transition`, `ringDesc`, `ringColimit`, `algColimit`) carry
`@[irreducible]` to prevent repeated expensive unfolding. Their equations are
proved locally. Preflight conservatively classifies the added commands as an
interface change and requires this record. All existing declarations, their
visibility and signatures, and the public imports remain verbatim. There is no
change to any existing definition. No imports were changed.

## Old

The theorem has the following signature and a `sorry` proof:

```lean
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
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} K) CommRingCat).mapCocone c))
```

## New

The theorem has exactly the same signature, now with a complete proof:

```lean
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
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} K) CommRingCat).mapCocone c))
```

The new section is closed before this theorem; its variables and `omit` commands
apply only to private helpers. The irreducibility attributes affect only those
new private constructions. No private helper occurs in a public signature or
public definition body. Only the theorem proof uses these constructions.

## Users

The downstream query lists the following five modules. None needs adaptation:
the public imports, existing definitions and theorem signature are identical.
Only `NormalGenericFibreVanishing` imports this module directly; the other users
are transitive. No downstream source currently applies the theorem by name.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | K3 | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | F4 | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | A9 | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | G8 | Identical public interface; no adaptation. |
| Sheaf.Targets.BaseChangeTowardsFields | F9 | Identical public interface; no adaptation. |

No target statement or definition used by a target changes, so no mathematical
statement review is reopened.

## Status

landed 20261020T122105-L-475767 2026-10-20 (merge of deliver/C7/Sheaf.RingTheory.ColimOfLocalizations)
