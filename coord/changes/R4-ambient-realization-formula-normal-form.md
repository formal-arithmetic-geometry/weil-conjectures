# AlgebraicGeometry.ProEtale.AmbientClopen.ambientExactClopenComparisonLocalizes

## Reason

The literal native unit--comparison--counit equation makes kernel checking unfold the
coefficient-site abelian and derived-category presentations repeatedly. Complete proofs
using the literal conclusion exceeded the 60-second file limit (receipt
`ea0c8855124fae91d5b9d21b`, stopped at 120 seconds). Replace that clause by the named
public predicate `properMateFormula` in `AmbientExactClopenData`. Its body is exactly
that equation, with the same specified adjunctions, alpha, gamma and object. This is a
definitionally equal presentation, with no hypothesis or conclusion weakened. None of
the declarations in `Challenge.lean` is changed. All new definitions contain actual data.

## Old

```lean
theorem ambientExactClopenComparisonLocalizes
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V W Z : Scheme.{u}}
    [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
    [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (∀ n : ℕ, OrdinaryAssertion (scalarRings l E n) k r p i h) ∧
      Systems.Assertion (scalarRings l E) (scalarTransitions l E) k r p i h ∧
      (∀ (o : Operations l E) (z : Realizations l E F o) (M : System l E U),
        (z.properOpen.gamma k r p i h).app M =
          (o.direct p).adj.unit.app
            ((Operations.shriek l E o i).obj ((Operations.push l E o r).obj M)) ≫
          (Operations.push l E o p).map
            ((realizationAlpha l E o z.canonicalBridge k r p i h).app
              ((Operations.push l E o r).obj M)) ≫
          (Operations.push l E o p).map ((Operations.shriek l E o k).map
            ((o.direct r).adj.counit.app M)))
```

## New

```lean
theorem ambientExactClopenComparisonLocalizes
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V W Z : Scheme.{u}}
    [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
    [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (∀ n : ℕ, OrdinaryAssertion (scalarRings l E n) k r p i h) ∧
      Systems.Assertion (scalarRings l E) (scalarTransitions l E) k r p i h ∧
      (∀ (o : Operations l E) (z : Realizations l E F o) (M : System l E U),
        properMateFormula (o.direct r).adj (o.direct p).adj
          (realizationAlpha l E o z.canonicalBridge k r p i h)
          (z.properOpen.gamma k r p i h) M)
```

The new public definition is:

```lean
def properMateFormula
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (γ : R₁ ⋙ G ⟶ H ⋙ R₂) (M : B) : Prop :=
  γ.app M = b.unit.app (G.obj (R₁.obj M)) ≫
    R₂.map (α.app (R₁.obj M)) ≫ R₂.map (H.map (a.counit.app M))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | R4 | Complete assembly retains the named formula. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | unclaimed in current mirror | The formula is definitionally identical; original source checked unchanged. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | The formula is definitionally identical; original source checked unchanged. |

No consumer adaptation is proposed. Returned head `b5a40dded7df` lost the auxiliary
`Normalized._proof_1` named by the pasting consumer. The reviewer repaired the data
predicate's equation direction and its three proof uses, preserving that declaration;
see `R4-ambient-clopen-data-normalization.md`. These fixes are included directly in
this repair. All five fixed modules and both unchanged current consumers compiled together on the
server (receipt `baf80c4ece52f1ea4698b4b8`, exit code 0).

## Status

landed 20261026T070810-L-3659151 2026-10-26 (merge of deliver/R4/Sheaf.SixFunctors.AmbientExactClopenComparison)
