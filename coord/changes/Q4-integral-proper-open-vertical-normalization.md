# integralSystemProperOpenTransportPastingVertical

## Reason

The vertical theorem and the pasting package theorem quantified over arbitrary gamma.
Their source proves pasting for the canonical bridge-conjugate gamma. An arbitrary
scalar multiple need not satisfy a quadratic pasting equation: in an identity diagram,
the normalized equation requires its scalar to be idempotent. This missing hypothesis
was already flagged STATEMENT-DISPUTED in the package module.

Supply the canonical bridge and precisely the existing canonical component equation.
The original universal existence theorem is unchanged: its already constructed core
supplies this equation via hc.canonical. No target statement, operation definition,
instance, public import or unit route changes.

The new integralSystemBridgePushComposition is the comparison of the two canonical
pushforward compositors. It is independent of gamma and holds for all scheme maps.

## Old

```lean
theorem integralSystemProperOpenTransportPastingVertical
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A),
      (Operations.shriek l E o j).map ((c.pushComp l E r₁ r₂).hom.app M) ≫
          (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (c.pushComp l E p₁ p₂).inv.app ((Operations.shriek l E o k).obj M) =
        (gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
          (Operations.push l E o p₂).map ((gamma k r₁ p₁ i h₁).app M)
```

```lean
theorem integralSystemProperOpenTransportPasting (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p) :
    Nonempty (ProperOpenTransportPasting l E o c a gamma)
```

## New

```lean
theorem integralSystemProperOpenTransportPastingVertical
    (o : Operations l E) (c : Compositors l E o)
    (_a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A),
      (Operations.shriek l E o j).map ((c.pushComp l E r₁ r₂).hom.app M) ≫
          (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (c.pushComp l E p₁ p₂).inv.app ((Operations.shriek l E o k).obj M) =
        (gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
          (Operations.push l E o p₂).map ((gamma k r₁ p₁ i h₁).app M)
```

```lean
theorem integralSystemProperOpenTransportPasting (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M) :
    Nonempty (ProperOpenTransportPasting l E o c a gamma)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingVertical | Q4 | Add canonical normalization; prove vertical transport. |
| Sheaf.SixFunctors.IntegralSystemOrdinaryBridgeComposition | new in Q4 | Prove ordinary section normalization and its conjugate. |
| Sheaf.SixFunctors.IntegralSystemBridgePushComposition | new in Q4 | Compare compositors using ordinary sections, localization and mates. |
| Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting | unclaimed | Pass the bridge and canonical equation to the vertical theorem; expose the same required inputs in its own theorem. Its record type stays identical. |
| Sheaf.SixFunctors.IntegralSystemProperOpenTransport | unclaimed | Pass b and hc.canonical to the repaired package theorem; the existing public statement stays identical. |

The listed existing consumers are the complete set of occurrences of the changed
theorem names under lean/. The horizontal and base-change component statements and
their owners' modules are unchanged. Their existing general statements are specialized
to the canonical gamma by the package theorem; their missing-normalization defects
remain separate work.

## Status

landed 20261028T055737-L-803331 2026-10-28 (merge of deliver/Q4/Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingVertical)
