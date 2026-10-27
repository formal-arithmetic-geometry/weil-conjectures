# CategoryTheory.SignedDoubleRoos coordinate constructions

## Reason

The strict interchange proof and the Koszul tensor/augmentation proof must be separate
stage-3 items. They both use the original coordinate constructions, so importing the
parent theorem module would create a cycle. Move the existing 18 declarations to
`Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions` and publicly import it
from the original module. Every moved signature, body, universe, namespace and visibility
is unchanged. The original theorem signature and docstring are also unchanged. This is
an interface-preserving extraction: the original module still reexports the same names
and all original public imports through the new definitions module. No target definition
or mathematical statement changes, so no semantic target re-review is required.

## Old

In `Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchange`:

```lean
/-- The existing module category, with its coefficient universe explicit.
Source: Stacks 03EK (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev Modules := ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Unbounded complexes in the existing module category.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev Complex := CochainComplex (Modules R) ℤ

/-- Strict inverse sequences, indexed by the nonnegative integers.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev Tower := ℕᵒᵖ ⥤ Complex R

/-- The published degreewise rearrangement, made functorial using its published map.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def towerComplex : Tower R ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id X := by ext k n; rfl
  map_comp f g := by ext k n; rfl

/-- The existing strict Roos functor in the tower-of-complexes presentation.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev roos : Tower R ⥤ Complex R := towerComplex R ⋙ roosF

/-- Evaluation in Roos degree zero, using the published cone evaluation.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def evaluation (X : Tower R) (n : ℕ) : (roos R).obj X ⟶ X.obj (op n) :=
  roosEval (koszulTowerComplex R X) n

/-- The integral degree of a Roos coordinate (false = unshifted, true = shifted).
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def degree (p : Bool) : ℤ := if p then 1 else 0

/-- Projection onto one of the two specified Roos coordinates and one product factor.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def coordinate (X : Tower R) (p : Bool) (k : ℤ) (n : ℕ) :
    ((roos R).obj X).X k ⟶ (X.obj (op n)).X (k - degree p) := by
  cases p
  · simpa only [degree, Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (evaluation R X n).f k
  · exact (CochainComplex.mappingCocone.snd (roosU (koszulTowerComplex R X))).v
      k (k - 1) (by omega) ≫
      (Pi.π (fun n : ℕ ↦ (koszulTowerComplex R X).asFunctor.obj (op n)) n).f (k - 1)

/-- First take Roos in the inner index and then in the outer index.
Source: Stacks 014E, twice (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev rows : (ℕᵒᵖ ⥤ Tower R) ⥤ Complex R :=
  (Functor.whiskeringRight ℕᵒᵖ (Tower R) (Complex R)).obj (roos R) ⋙ roos R

/-- Reverse the indices before taking the same iterated Roos functor.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev columns : (ℕᵒᵖ ⥤ Tower R) ⥤ Complex R :=
  flipFunctor _ _ _ ⋙ rows R

/-- The four row coordinates, in the order (0,0), (0,1), (1,0), (1,1).
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def rowCoordinate (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((rows R).obj X).X k ⟶ ((X.obj (op n)).obj (op j)).X
      (k - degree p - degree q) :=
  coordinate R (X ⋙ roos R) p k n ≫
    coordinate R (X.obj (op n)) q (k - degree p) j

/-- The column coordinates with output indexed in the original n,j order.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def columnCoordinate (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((columns R).obj X).X k ⟶ ((X.obj (op n)).obj (op j)).X
      (k - degree p - degree q) :=
  rowCoordinate R X.flip q p k j n ≫
    eqToHom (congrArg (fun a : ℤ ↦ ((X.obj (op n)).obj (op j)).X a)
      (by omega))

/-- Evaluate the inner Roos coordinate, naturally in the remaining index.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def innerEvaluation (X : ℕᵒᵖ ⥤ Tower R) (j : ℕ) :
    X ⋙ roos R ⟶ X.flip.obj (op j) where
  app n := evaluation R (X.obj n) j
  naturality n m f := by
    exact roosEval_natural (koszulTowerComplexMap R (X.map f)) j

/-- The induced derived interchange, conjugated by the chosen normalized comparisons.
In particular, taking both comparisons from strictRoosComparison gives the signed
isomorphism of the two iterated total derived limits, with their prescribed evaluations.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def derivedInterchange [HasDerivedCategory.{w} (Modules R)]
    (X : ℕᵒᵖ ⥤ Tower R) (β : (rows R).obj X ≅ (columns R).obj X)
    {Dnj Djn : DerivedCategory.{w} (Modules R)}
    (ρnj : DerivedCategory.Q.obj ((rows R).obj X) ≅ Dnj)
    (ρjn : DerivedCategory.Q.obj ((columns R).obj X) ≅ Djn) : Dnj ≅ Djn :=
  ρnj.symm ≪≫ DerivedCategory.Q.mapIso β ≪≫ ρjn

/-- The published principal Koszul tower, tensored on the right of its input.
Source: Stacks 012Z, 03EK (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def tensorTower (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    Complex R ⥤ Tower R :=
  curriedTensor (Complex R) ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (Complex R) (Complex R)).obj (principalKoszulTower R t)

/-- Transport the published 1 tensor x augmentation by the standard signed symmetry.
Its degree-zero component is x tensor 1.
Source: Stacks 012Z, 03EK (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def strictAugmentation (P : Complex R) (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    (Functor.const ℕᵒᵖ).obj P ⟶ (tensorTower R t).obj P :=
  koszulStrictAugmentation R P t ≫
    Functor.whiskerLeft (principalKoszulTower R t)
      (BraidedCategory.tensorLeftIsoTensorRight P).inv

/-- Completion in the strict Roos model, using the actual total tensor tower.
Source: Stacks 0941, 012Z (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev completion (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    Complex R ⥤ Complex R := tensorTower R t ⋙ roos R

/-- The strict unit with the prescribed degree-zero inclusion and zero shifted component.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def augmentation (P : Complex R) (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    P ⟶ (completion R t).obj P :=
  roosAugment (X := koszulTowerComplex R ((tensorTower R t).obj P))
    (fun j ↦ (strictAugmentation R P t).app (op j))
    (fun j ↦ ((strictAugmentation R P t).naturality
      (homOfLE (Nat.le_succ j)).op).symm.trans (Category.id_comp _))

```

## New

The exact declaration block in `## Old` occurs verbatim in
`lean/Sheaf/Algebra/Homology/SignedDoubleRoosTensorExchangeDefinitions.lean`.
The original module replaces the block with:

```lean
public import Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions
```

The definitions module retains every original public import. Its unused private proof
imports of StrictRoosComparison, sheafification, products and abelian basic are omitted.
The parent proof privately imports the two new core theorem modules. The full original
block above is also the complete new signature/body specification; no declaration body
is rewritten or reconstructed. A declaration-table check verified all 18 signatures
and bodies before compilation.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchange`
and its `--uses CategoryTheory.SignedDoubleRoos.augmentation` query found no external
module users of the item (only the item itself mentions that declaration). A direct
search of both Lean roots agrees. The DAG parent still uses the item, so it is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchange | M5 | Same theorem and reexported constructions; complete assembly proof. |
| Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions | new in M5 | Owns the identical 18 definitions. |
| Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeInterchange | new in M5 | Imports the constructions to state only the signed interchange. |
| Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeTensor | new in M5 | Imports the constructions to state only tensor/augmentation coherence. |

## Status

landed 20261025T163857-L-882743 2026-10-25 (merge of deliver/M5/Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchange)
