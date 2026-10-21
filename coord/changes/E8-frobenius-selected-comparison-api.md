# WeilConjectures.PurityFiniteSetting.frobeniusOrdinaryComposition

## Reason

Name the existing jointly selected ordinary comparison and trivialization, and
their exact descents, so the large choice term stays folded in categorical proofs.
The new coefficient-ring lemma is a proof of the same finite instance already
used by the original definitions. All five added declarations are public because
public definitions refer to them. They are attached to the existing item node.

Unfolding these wrappers gives the old definitions, with the fibre characteristic
proof made uniform as recorded separately. Finite and characteristic arguments
are propositions, so proof irrelevance identifies the old and new terms. No
ordinary comparison or trivialization is selected independently, and no new
choice or hypothesis is introduced. The normalization equations in the original
trivialization theorem determine its selected data. Existing public signatures
and target statements are unchanged.

## Old

```lean
def frobeniusOrdinaryComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingPullback P.Ring g ⋙ proEtaleConstantRingPullback P.Ring f :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  (absoluteFrobenius_proEtale_trivialization_pullback
    P.field.p P.field.prime P.Ring).choose_spec.2.choose f g

def frobeniusDerivedComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingDerivedPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback P.Ring g ⋙
        proEtaleConstantRingDerivedPullback P.Ring f :=
  proEtaleFrobeniusDerivedComp P.Ring f g (P.frobeniusOrdinaryComposition f g)

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

```lean
theorem coefficient_ring_finite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos

def selectedComp (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f :=
  (absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose f g

def selectedTau (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X : Scheme.{u}) (hX : X.IsCharacteristic p) (b : ℕ) :
    proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _ :=
  (absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose_spec.2.choose
    X hX b

def selectedDerivedComp (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingDerivedPullback A (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback A g ⋙ proEtaleConstantRingDerivedPullback A f :=
  proEtaleFrobeniusDerivedComp A f g (selectedComp p hp A f g)

def selectedDerivedTau (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X : Scheme.{u}) (hX : X.IsCharacteristic p) (b : ℕ) :
    proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _ :=
  proEtaleFrobeniusDerivedIso A (selectedTau p hp A X hX b)

def frobeniusOrdinaryComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingPullback P.Ring g ⋙ proEtaleConstantRingPullback P.Ring f :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedComp P.field.p P.field.prime P.Ring f g

def frobeniusDerivedComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingDerivedPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback P.Ring g ⋙
        proEtaleConstantRingDerivedPullback P.Ring f :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedDerivedComp P.field.p P.field.prime P.Ring f g

def frobeniusAbsoluteTrivialization (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusAbsoluteMap T₀) ≅
      𝟭 (proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring) :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedDerivedTau P.field.p P.field.prime P.Ring (P.frobeniusFiber T₀).left
    (P.frobeniusFiber_characteristic T₀) P.field.a
```

## Users

`tools/downstream.py Sheaf.SixFunctors.SchemeGeometricFrobenius --uses
frobeniusOrdinaryComposition frobeniusDerivedComposition
frobeniusAbsoluteTrivialization schemeGeometricFrobeniusComparison
schemeGeometricFrobenius_naturality` finds no current downstream Lean module.
The DAG parents and unit route are retained. Every existing statement and the
specified comparisons retain their meanings; no external adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | Completes naturality using the same selected data. |

## Status

landed 20261021T120348-L-3836512 2026-10-21 (merge of deliver/E8/Sheaf.SixFunctors.SchemeGeometricFrobenius)
