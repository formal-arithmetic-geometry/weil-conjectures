# WeilConjectures.PurityFiniteSetting.frobeniusFiber_characteristic

## Reason

Give the characteristic of the chosen fibre a named proof API, and use that same
proof in the absolute Frobenius and ordinary trivialization selected before exact
descent. Previously the absolute map used a proof on the explicitly constructed
pullback's top sections, while the trivialization used the derived characteristic
of the fibre alias. Matching them repeatedly unfolded the chosen scheme pullback.
The named theorem makes these proof arguments uniform.

This changes only proofs in definition bodies. All original signatures and the
actual Frobenius morphism and trivialization are definitionally unchanged by proof
irrelevance. The new theorem is proved directly by the existing model
characteristic and restriction from top sections; it adds no hypothesis or hole.
It must be public because public definitions refer to it. Its attachment is the
existing scheme/geometric-Frobenius node. No target statement changes.

## Old

```lean
def frobeniusAbsoluteMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  (P.frobeniusFiber T₀).left.iterateFrobenius P.field.prime
    (P.field.model_characteristic
      (pullback.fst T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom)) P.field.a

def frobeniusAbsoluteTrivialization (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusAbsoluteMap T₀) ≅
      𝟭 (proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  proEtaleFrobeniusDerivedIso P.Ring
    ((absoluteFrobenius_proEtale_trivialization_pullback
      P.field.p P.field.prime P.Ring).choose_spec.2.choose_spec.2.choose (P.frobeniusFiber T₀).left
        ⟨P.field.prime, natCast_eq_zero_of_natCast_top_eq_zero
          (P.field.model_characteristic (pullback.fst T₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom))⟩
        P.field.a)
```

## New

The exact delivered definitions are below. The selected-descent wrapper unfolds
to the old formula; its extraction is recorded in
`E8-frobenius-selected-comparison-api.md`.

```lean
theorem frobeniusFiber_characteristic (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left.IsCharacteristic P.field.p :=
  ⟨P.field.prime, natCast_eq_zero_of_natCast_top_eq_zero
    (P.field.model_characteristic (pullback.fst T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom))⟩

def frobeniusAbsoluteMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  (P.frobeniusFiber T₀).left.iterateFrobenius P.field.prime
    ((P.frobeniusFiber_characteristic T₀).2 ⊤) P.field.a

def frobeniusAbsoluteTrivialization (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusAbsoluteMap T₀) ≅
      𝟭 (proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring) :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedDerivedTau P.field.p P.field.prime P.Ring (P.frobeniusFiber T₀).left
    (P.frobeniusFiber_characteristic T₀) P.field.a
```

## Users

The current downstream query finds no Lean importers of the item. All original
statements have identical meanings by proof irrelevance. The factorization and
square arguments are checked in the same delivered file; no external consumer
adaptation is needed. The DAG parents and unit route are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | Named fibre characteristic; identical absolute map and trivialization. |

## Status

landed 20261021T120348-L-3836512 2026-10-21 (merge of deliver/E8/Sheaf.SixFunctors.SchemeGeometricFrobenius)
