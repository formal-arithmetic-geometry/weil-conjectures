# WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportPastingHorizontal

## Reason

The old statement asserted pasting for arbitrary gamma. Negating the canonical mate on
identity squares changes the outer side by a sign and the inner composite by two signs;
on a nonzero coefficient object with 2 nonzero these differ. The source, Stacks
more-etale, lemma-shriek-proper-and-open-compose-horizontal, concerns the canonical mate.
The correction requires the canonical bridge equation already supplied by the caller.
No target signature, definition or structure field changes.

## Old

```lean
theorem integralSystemProperOpenTransportPastingHorizontal
(o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
      (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) (M : System l E A),
      (c.openComp l E i j).hom.app ((Operations.push l E o r).obj M) ≫
          (gamma (k ≫ ll) r q (i ≫ j) h).app M ≫
          (Operations.push l E o q).map ((c.openComp l E k ll).inv.app M) =
        (Operations.shriek l E o j).map ((gamma k r p i h₁).app M) ≫
          (gamma ll p q j h₂).app ((Operations.shriek l E o k).obj M)
```

## New

```lean
theorem integralSystemProperOpenTransportPastingHorizontal
(o : Operations l E) (c : Compositors l E o)
    (_a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (hgamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫ (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
      (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) (M : System l E A),
      (c.openComp l E i j).hom.app ((Operations.push l E o r).obj M) ≫
          (gamma (k ≫ ll) r q (i ≫ j) h).app M ≫
          (Operations.push l E o q).map ((c.openComp l E k ll).inv.app M) =
        (Operations.shriek l E o j).map ((gamma k r p i h₁).app M) ≫
          (gamma ll p q j h₂).app ((Operations.shriek l E o k).obj M)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingHorizontal | Q3 | Requires the canonical bridge equation and proves the resulting horizontal law. |
| Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting | unclaimed | Its signature already has b and canonical; pass them in its horizontal field call. |

These are the two modules mentioning the changed declaration in tools/downstream.py --uses.
The assembly's signature, record, and result are unchanged. Its sole direct importer,
IntegralSystemProperOpenTransport, therefore needs no source adaptation. No adopted
source-library signature, public import or declaration is changed. No unit is bypassed.

## Status

landed 20261028T081755-L-2781925 2026-10-28 (merge of deliver/Q3/Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingHorizontal)
