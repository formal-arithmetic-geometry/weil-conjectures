# Integral normalized family: kernel-efficient witness packaging

## Reason

The concurrently landed root compiled in 76 seconds, over the 60-second limit.
Profiling attributed 63.4 seconds to kernel type checking and less than one second
to tactic execution. Its new private `selectDiagonalLimit` wrapper performs the
large normalization conversion over an abstract localization instance. A first
continuation refactor retaining that wrapper still took 70 seconds.

Move the normalization conversion into the public proof after the actual
localization instances and witnesses have been selected. Retain the explicit
unfolding of all four normalization definitions introduced by the landed repair.
This is proof packaging only: no public declaration, data body, instance,
attribute, import or statement changes. The root is currently unclaimed (server claim records checked 2026-10-28).

## Old

The existing public signature is preserved verbatim:

```lean
theorem integralNormalizedFamily_exists
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    ∃ family : Family ℓ Y, IntegralFamilyReference ℓ Y family
```

Its previous final proof fragment was:

```lean
  obtain ⟨δ, hlimit⟩ := selectDiagonalLimit ℓ Y hY D hLim
  exact (diagonalTower_coefficients ℓ k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) Y hY D hcompletion hsystem δ hlimit).imp
      (fun family hfamily ↦ ⟨hY, aY, aP, aW, δ, hfamily.1⟩)

```

Private packaging before the repair, verbatim:

```lean
private theorem selectPresentation
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {E : ∀ a b c, D a b c → Sort*}
    {F : ∀ a b c d, E a b c d → Sort*}
    {G : ∀ a b c d e, F a b c d e → Sort*}
    {H : ∀ a b c d e f, G a b c d e f → Sort*}
    {I : ∀ a b c d e f g, H a b c d e f g → Sort*} {Z : Sort*}
    {p q r : ∀ a b c d, E a b c d → Prop}
    {s t v : ∀ a b c d e f g h, I a b c d e f g h → Prop}
    {w : ∀ a b c d e f g h, I a b c d e f g h → Z → Prop}
    (convert : ∀ a b c d e f g h i, v a b c d e f g h i →
      ∃ z, w a b c d e f g h i z)
    (data : ∃ a b c d e, p a b c d e ∧ q a b c d e ∧ r a b c d e ∧
      ∃ f g h i, s a b c d e f g h i ∧ t a b c d e f g h i ∧ v a b c d e f g h i) :
    ∃ z, ∃ a b c d e, p a b c d e ∧ q a b c d e ∧ r a b c d e ∧
      ∃ f g h i, (s a b c d e f g h i ∧ t a b c d e f g h i ∧
        v a b c d e f g h i) ∧ w a b c d e f g h i z := by
  obtain ⟨a, b, c, d, e, hp, hq, hr, f, g, h, i, hs, ht, hv⟩ := data
  obtain ⟨z, hz⟩ := convert a b c d e f g h i hv
  exact ⟨z, a, b, c, d, e, hp, hq, hr, f, g, h, i, ⟨hs, ht, hv⟩, hz⟩

-- Convert the normalized limit presentation before specializing localization choices.
private theorem selectDiagonalLimit (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations ℓ (diagonalSurface Y)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (h : DiagonalCompletedLimitSpec ℓ Y hY D) :
    ∃ δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
      DiagonalTrace.IsDiagonalLimit ℓ Y hY D δ := by
  unfold DiagonalCompletedLimitSpec at h
  unfold DiagonalTrace.IsDiagonalLimit DiagonalTrace.FiniteCartierNormalization
    DiagonalTrace.FiniteRootNormalization DiagonalTrace.finiteCartierClass
  exact selectPresentation (data := h)
    (fun _ _ _ _ _ _ _ _ _ hh ↦ selectEquation hh)
```

## New

The public signature above stays identical. Its final proof fragment becomes:

```lean
  refine selectPresentation (data := hLim)
    (fun _ _ _ _ _ _ _ _ _ hh ↦ selectEquation hh) ?_
  intro δ hlimit
  exact (diagonalTower_coefficients ℓ k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) Y hY D hcompletion hsystem δ (by
      unfold DiagonalTrace.IsDiagonalLimit DiagonalTrace.FiniteCartierNormalization
        DiagonalTrace.FiniteRootNormalization DiagonalTrace.finiteCartierClass
      exact hlimit)).imp
      (fun family hfamily ↦ ⟨hY, aY, aP, aW, δ, hfamily.1⟩)

```

The private `selectPresentation` uses an abstract conclusion and a continuation
instead of constructing its large concrete existential result at the call site.
The now-unused private `selectDiagonalLimit` wrapper is removed. A source search
finds no other caller; neither helper is public. All profiler options are removed.
The resulting source matches the preserved archive that previously compiled in
1.6 seconds; the full consumer chain is checked again against this packet.

Private packaging after the repair, verbatim:

```lean
private theorem selectPresentation
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {E : ∀ a b c, D a b c → Sort*}
    {F : ∀ a b c d, E a b c d → Sort*}
    {G : ∀ a b c d e, F a b c d e → Sort*}
    {H : ∀ a b c d e f, G a b c d e f → Sort*}
    {I : ∀ a b c d e f g, H a b c d e f g → Sort*} {Z : Sort*} {Result : Prop}
    {p q r : ∀ a b c d, E a b c d → Prop}
    {s t v : ∀ a b c d e f g h, I a b c d e f g h → Prop}
    {w : ∀ a b c d e f g h, I a b c d e f g h → Z → Prop}
    (convert : ∀ a b c d e f g h i, v a b c d e f g h i →
      ∃ z, w a b c d e f g h i z)
    (data : ∃ a b c d e, p a b c d e ∧ q a b c d e ∧ r a b c d e ∧
      ∃ f g h i, s a b c d e f g h i ∧ t a b c d e f g h i ∧ v a b c d e f g h i)
    (conclude : ∀ z, (∃ a b c d e, p a b c d e ∧ q a b c d e ∧ r a b c d e ∧
      ∃ f g h i, (s a b c d e f g h i ∧ t a b c d e f g h i ∧ v a b c d e f g h i) ∧
        w a b c d e f g h i z) →
      Result) : Result := by
  obtain ⟨a, b, c, d, e, hp, hq, hr, f, g, h, i, hs, ht, hv⟩ := data
  obtain ⟨z, hz⟩ := convert a b c d e f g h i hv
  exact conclude z ⟨a, b, c, d, e, hp, hq, hr, f, g, h, i, ⟨hs, ht, hv⟩, hz⟩
```

## Users

All six direct importers have been restored on main and are compiled unchanged
against the root repair before delivery. Their temporary sandbox copies are removed
after checking; none is adapted or delivered. No proof route or DAG attachment
changes: the argument still extracts the unique completed diagonal arrow and applies
`diagonalTower_coefficients` with the full normalization predicate.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.IntegralKernelFirstAmbientFormula` | unclaimed | unchanged on main; compiled against the root proof repair |
| `Sheaf.SixFunctors.IntegralKernelFirstTransport` | unclaimed | unchanged on main; compiled against the root proof repair |
| `Sheaf.SixFunctors.IntegralKernelFirstContraction` | unclaimed | unchanged on main; compiled against the root proof repair |
| `Sheaf.SixFunctors.IntegralKernelSecondContractionPostcomp` | unclaimed | unchanged on main; compiled against the root proof repair |
| `Sheaf.SixFunctors.IntegralKernelSecondContraction` | unclaimed | unchanged on main; compiled against the root proof repair |
| `Sheaf.SixFunctors.IntegralKernelContractions` | unclaimed | unchanged on main; compiled against the root proof repair |

## Status

landed 20261028T034647-L-3528504 2026-10-28 (merge of deliver/A2/WeilConjectures.SmoothPurity.Defs)
