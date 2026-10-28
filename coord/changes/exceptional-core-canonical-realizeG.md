# TransportCoreData.realizeG

## Reason

The assigned adjunction theorem was false for the previous data record: the right
comparison could be chosen independently of the two adjunctions and the left
comparison. For the identity adjunction on characteristic-zero modules, minus
identity is a different comparison and changes the transported unit and counit.
Zheng's Construction 5.25 uses the induced comparison, rather than an arbitrary one.

Construct `TransportCoreData.realizeG` directly as the inverse of
`Adjunction.rightAdjointUniq` for the reconstructed adjunction, transported on the
left by `realizeF` inverse, and the specified integral operation adjunction. The
formula is an explicit composition of existing unit and counit maps. It introduces
no law hypothesis, axiom, unproved construction, or choice of an existence witness.
The remaining data fields retain their types. The data existence proof omits the
unused independently supplied `p.realizeG` component.

This is a definition repair, not a proof of the false assertion about arbitrary
comparisons. The assigned law theorem retains its written signature but refers to
the repaired data type. The generated structure constructor loses the `realizeG`
argument. `TransportCoreData.realizeG` remains available with its isomorphism type.

The former normalization now returns its input, which already has the canonical
comparison. `normalizedRealizeG` is an abbreviation for that single definition.
The three obstruction lemmas retain meaningful content by testing arbitrary
comparison families against fixed data, rather than attempting an invalid update
of a derived field. They have no callers outside their own module.

## Old

```lean
structure TransportCoreData
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s)) where
  leftShift (s : RingStage.{u} l) : (left s).hom.CommShift ℤ
  reconstruction (E : FieldStage.{u} l) (side : Bool) :
    Reconstruction l E (endpoint X Y side)
  operations (E : FieldStage.{u} l) : IntegralSystemRealization.Operations l E.carrier
  realizations (E : FieldStage.{u} l) :
    IntegralSystemRealization.Realizations l E.carrier D (operations E)
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    G E ⋙ (reconstruction E true).evaluation n ≅
      (reconstruction E false).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
```

```lean
def normalizedRealizeG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  (Adjunction.rightAdjointUniq
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm)
    (operation (.integral E)).adjunction).symm
```

```lean
def TransportCoreData.normalizeRealizeG : TransportCoreData l Ω D hl c operation left :=
  { d with realizeG := normalizedRealizeG l Ω D hl c operation left d }
```

```lean
theorem not_adjunction_law_of_realizeG_ne (E : FieldStage.{u} l)
    (h : d.realizeG E ≠ normalizedRealizeG l Ω D hl c operation left d E) :
    (operation (.integral E)).adjunction ≠
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm
```

```lean
theorem not_forall_adjunction_law_of_realizeG_twist
    (α : ∀ E : FieldStage.{u} l,
      (operation (.integral E)).G ≅ (operation (.integral E)).G)
    (E : FieldStage.{u} l) (hα : α E ≠ Iso.refl _) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      Nonempty (∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d'.reconstruction E true).equivalence
            (d'.reconstruction E false).equivalence (d'.adjunction E)).ofNatIsoLeft
            (d'.realizeF E).symm).ofNatIsoRight (d'.realizeG E).symm)
```

```lean
theorem not_forall_adjunction_law_of_neg_id_ne (E : FieldStage.{u} l)
    (K : C.{u} l Ω Y (.integral E))
    (hne : -(𝟙 ((operation (.integral E)).G.obj K)) ≠
      𝟙 ((operation (.integral E)).G.obj K)) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      Nonempty (∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d'.reconstruction E true).equivalence
            (d'.reconstruction E false).equivalence (d'.adjunction E)).ofNatIsoLeft
            (d'.realizeF E).symm).ofNatIsoRight (d'.realizeG E).symm)
```

The data constructor set `realizeG := p.realizeG,`. The law theorem was `sorry`.
The item publicly imported `Mathlib.CategoryTheory.Adjunction.Unique`.

## New

```lean
structure TransportCoreData
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s)) where
  leftShift (s : RingStage.{u} l) : (left s).hom.CommShift ℤ
  reconstruction (E : FieldStage.{u} l) (side : Bool) :
    Reconstruction l E (endpoint X Y side)
  operations (E : FieldStage.{u} l) : IntegralSystemRealization.Operations l E.carrier
  realizations (E : FieldStage.{u} l) :
    IntegralSystemRealization.Realizations l E.carrier D (operations E)
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    G E ⋙ (reconstruction E true).evaluation n ≅
      (reconstruction E false).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
```

```lean
def TransportCoreData.realizeG
    {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {D : FiniteFieldDatum.{u}} {hl : l ≠ D.p}
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : TransportCoreData l Ω D hl c operation left) (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  (Adjunction.rightAdjointUniq
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm)
    (operation (.integral E)).adjunction).symm
```

```lean
abbrev normalizedRealizeG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  d.realizeG E
```

```lean
def TransportCoreData.normalizeRealizeG : TransportCoreData l Ω D hl c operation left :=
  d
```

```lean
theorem not_adjunction_law_of_realizeG_ne (E : FieldStage.{u} l)
    (e : (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E))
    (h : e ≠ normalizedRealizeG l Ω D hl c operation left d E) :
    (operation (.integral E)).adjunction ≠
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight e.symm
```

```lean
theorem not_forall_adjunction_law_of_realizeG_twist
    (α : ∀ E : FieldStage.{u} l,
      (operation (.integral E)).G ≅ (operation (.integral E)).G)
    (E : FieldStage.{u} l) (hα : α E ≠ Iso.refl _) :
    ¬ ∀ e : ∀ E : FieldStage.{u} l,
        (operation (.integral E)).G ≅
          PurReconstruction.realized (d.reconstruction E false).equivalence
            (d.reconstruction E true).equivalence (d.G E),
      ∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
            (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
            (d.realizeF E).symm).ofNatIsoRight (e E).symm
```

```lean
theorem not_forall_adjunction_law_of_neg_id_ne (E : FieldStage.{u} l)
    (K : C.{u} l Ω Y (.integral E))
    (hne : -(𝟙 ((operation (.integral E)).G.obj K)) ≠
      𝟙 ((operation (.integral E)).G.obj K)) :
    ¬ ∀ e : ∀ E : FieldStage.{u} l,
        (operation (.integral E)).G ≅
          PurReconstruction.realized (d.reconstruction E false).equivalence
            (d.reconstruction E true).equivalence (d.G E),
      ∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
            (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
            (d.realizeF E).symm).ofNatIsoRight (e E).symm
```

The data constructor no longer supplies an independent `realizeG` value.
`ExceptionalRingTransportCoreData` now publicly imports
`Mathlib.CategoryTheory.Adjunction.Unique`, needed for the public construction.
The item's redundant direct public import of that same module is removed; it is
still publicly reexported through the data module. The source-library uniqueness
characterization remains a proof-only import of the item.

The complete proof of `exists_exceptional_transport_core_system_adjunction_law` is:

```lean
  exact ⟨normalizedRealizeG_adjunction l Ω D hl c operation left d⟩
```

Its helper is proved by `Adjunction.ofNatIsoRight_eq_iff` and reflexivity for the
explicit uniqueness isomorphism. No other law-existence theorem is used.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalRingTransportCore | unclaimed | Unchanged assembly copies the canonical right comparison into the unchanged Transported interface. |
| Sheaf.Paper.ExceptionalRingTransportCoreData | unclaimed | Repaired here: remove the independent realizeG field, define the canonical comparison, omit p.realizeG in the constructor. |
| Sheaf.Paper.ExceptionalRingTransportCoreEvaluationCounit | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreEvaluationSupport | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreEvaluationUnit | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreLaws | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization | K2 | Unchanged. Its integralLeft update preserves every input of the constructed realizeG definition. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction | G3 | Assigned item: prove the law, alias the canonical definition, make normalization identity, generalize the three diagnostics to arbitrary comparison families. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemReduction | G7 | The unchanged reductionG equation now refers to the canonical comparison. No equation is weakened or claimed proved by this repair. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportMaps | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportObjects | unclaimed | Unchanged source and statement; the derived comparison has the same isomorphism type. Checked against this delivery. |

These are all 13 textual `TransportCoreData` users, the additional core assembly
using its inferred datum, and every direct importer. The `--uses realizeG` scan
finds only the item, data, laws, system laws, system reduction and core assembly.
The three diagnostics and normalization names have no external name users.
No other existing Lean module is changed in this delivery. Temporary unchanged
consumer copies are removed after validation.

No declaration of `Challenge.lean`, source-library signature, or definition in a
target statement is changed: `TransportCoreData` occurs only in this proof-side
construction chain, and `ExceptionalIntegralScalar.Transported` is unchanged.
The unit's reconstruction/adjunction route is preserved. The change explicitly
reopens review of the data definition and its consumers, recorded in the four
existing nodes and their `statement_change` citer audits.

The other remaining arbitrary-data laws (support, reduction, evaluation and
integral-left normalization) are not proved by the present repair. In particular,
`reductionG` is still independently supplied; its existing hole must establish the
stated equation for the canonical comparison or receive its own definition repair.

## Status

landed 20261028T072413-L-1943418 2026-10-28 (merge of deliver/G3/Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction)
