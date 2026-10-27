# AlgebraicGeometry.ProEtale.FiniteScalarCompletion.quotientSequence

## Reason

The previous explicit quotient sequence repeated degree-zero complex and biproduct
normalization in naturality and limit checks. Factor the actual coefficient sequence
through the finite biproduct and single functors, and assemble its complex of diagrams
through a generic constructor. This preserves every quotient object, projection and
successor map while reducing elaboration of the limiting quotient cone. The isolated
cone check fell from 57.8 seconds for the explicit construction to 29.7 seconds for the
factored sequence, including imports. No object is selected from mere existence.

## Old

```lean
abbrev freeComplex (d : ℕ) : CochainComplex (Modules l E T) ℤ :=
  (singleFunctor (Modules l E T) 0).obj (Mod.finiteFree (ring l E T) d)

def quotientSequence (d : ℕ) : ℕᵒᵖ ⥤ CochainComplex (Modules l E T) ℤ :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ (singleFunctor (Modules l E T) 0).obj (quotientPower l E T d n))
    (fun n : ℕ ↦
    (singleFunctor (Modules l E T) 0).map (powerStep l E T d n))

/-- The strict quotient tower in degree zero, using the actual quotient transitions.
Source: blueprint Local models, free tower comparison
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def quotientTower (d : ℕ) : CochainComplex (ℕᵒᵖ ⥤ Modules l E T) ℤ where
  X k := quotientSequence l E T d ⋙ HomologicalComplex.eval (Modules l E T) (.up ℤ) k
  d k r :=
    { app := fun n ↦ ((quotientSequence l E T d).obj n).d k r
      naturality := fun _ _ f ↦ ((quotientSequence l E T d).map f).comm k r }
  shape k r h := NatTrans.ext (funext fun n ↦
    ((quotientSequence l E T d).obj n).shape k r h)
  d_comp_d' k r s _ _ := NatTrans.ext (funext fun n ↦
    ((quotientSequence l E T d).obj n).d_comp_d k r s)
```

## New

```lean
def freeComplex (d : ℕ) : CochainComplex (Modules l E T) ℤ :=
  (singleFunctor (Modules l E T) 0).obj (Mod.finiteFree (ring l E T) d)

def finiteBiproductPower {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] (d : ℕ) : A ⥤ A where
  obj M := ⨁ fun _ : Fin d ↦ M
  map f := biproduct.map fun _ : Fin d ↦ f
  map_id M := by ext i; simp
  map_comp f g := by ext i; simp

def quotientSequence (d : ℕ) : ℕᵒᵖ ⥤ CochainComplex (Modules l E T) ℤ :=
  coefficientSequence l E T ⋙ finiteBiproductPower d ⋙ singleFunctor (Modules l E T) 0

/-- Assemble a diagram of cochain complexes as a complex of diagrams.
Source: categorical interchange of functor and complex structures
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def complexOfSequence {A J : Type*} [Category A] [Category J]
    [HasZeroMorphisms A] (F : J ⥤ CochainComplex A ℤ) :
    CochainComplex (J ⥤ A) ℤ where
  X k := F ⋙ HomologicalComplex.eval A (.up ℤ) k
  d k r := { app := fun j ↦ (F.obj j).d k r
             naturality := fun _ _ f ↦ (F.map f).comm k r }
  shape k r h := NatTrans.ext (funext fun j ↦ (F.obj j).shape k r h)
  d_comp_d' k r t _ _ := NatTrans.ext (funext fun j ↦ (F.obj j).d_comp_d k r t)

/-- The strict quotient tower in degree zero, using the actual quotient transitions.
Source: blueprint Local models, free tower comparison
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def quotientTower (d : ℕ) : CochainComplex (ℕᵒᵖ ⥤ Modules l E T) ℤ :=
  complexOfSequence (quotientSequence l E T d)
```

The quotient-sequence objects are definitionally equal to the old ones. Its successor
maps agree by `quotientSequence_step`; functoriality determines every map from these.
The generic `complexOfSequence` uses precisely the previous fields of `quotientTower`.
The definitions of `quotientPower`, `powerQuotient`, `powerStep` and
`quotientChainMap` are unchanged. The theorem signature is unchanged. In particular,
its tower and augmentation still mean the actual finite coefficient quotients and
specified scalar projections.

The body and type of `freeComplex` are unchanged; it is now a `def` rather than an
`abbrev`, with local irreducibility in proofs that should treat it as an object.
This prevents repeated normalization of the monoidal finite-power construction.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteScalarLocalModelComplete` | X9 | Uses the sequence API in its strict comparison and quotient-cone proof. |
| `Sheaf.Paper.QcqsIntegralFiniteModelCompleteness` | V1 | Uses only the unchanged global-model conjunct; no changed definition is unfolded. No adaptation. |
| `Sheaf.Paper.SupportedImageDerivedCompleteness` | unclaimed | Imports the module; its statement does not mention the changed constructions. No adaptation. |
| `Sheaf.Paper.SupportedIntegralModelRestrictionTower` | H9 | Uses only the completeness assertion; no changed construction is unfolded. No adaptation. |

`tools/downstream.py --uses quotientSequence quotientTower freeComplex quotientChainMap`
finds no other declaration users. The three downstream modules above are the complete
transitive importer list. No target statement is changed.

## Status

landed 20261024T191755-L-489561 2026-10-24 (merge of deliver/X9/Sheaf.Paper.FiniteScalarLocalModelComplete)
