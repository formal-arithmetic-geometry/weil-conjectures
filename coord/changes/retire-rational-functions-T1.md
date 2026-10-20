# AlgebraicGeometry.Scheme.DenseOpens and rationalFunctionRing

## Reason

Retirement item `Sheaf.AlgebraicGeometry.RationalFunctions` (SUPERSET, depth 0) in
`coord/retire-items.tsv`, following the human's 2026-10-20 duplicate retirement decision.
The upstream module defines the same dense opens, intersection, inclusion, section diagram,
and universe-polymorphic colimit ring. It additionally proves cofilteredness.
Importing it while retaining the Sheaf ring definition would redeclare
`AlgebraicGeometry.Scheme.rationalFunctionRing`. Remove both copies of the constructions.
No source-library file changes.

## Old

`lean/Sheaf/AlgebraicGeometry/RationalFunctions.lean`:

```lean
def DenseOpens (X : Scheme) := {U : X.Opens // Dense (U : Set X)}

instance (X : Scheme) : PartialOrder (DenseOpens X) := inferInstanceAs
  (PartialOrder {U : X.Opens // Dense (U : Set X)})

/-- The intersection of two dense opens is dense (Stacks, Tag 01RS;
(blueprint: def-sc-rational-functions)). -/
def DenseOpens.inter {X : Scheme} (U V : DenseOpens X) : DenseOpens X :=
  ⟨U.val ⊓ V.val, by
    change Dense ((U.val : Set X) ∩ (V.val : Set X))
    exact U.property.inter_of_isOpen_left V.property U.val.isOpen⟩

/-- The inclusion of dense opens into all opens (Stacks, Tag 01RS;
(blueprint: def-sc-rational-functions)). -/
def denseOpensInclusion (X : Scheme) : DenseOpens X ⥤ X.Opens where
  obj U := U.val
  map f := homOfLE (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The section rings over dense opens with restriction maps (Stacks, Tag 01RV;
(blueprint: def-sc-rational-functions)). -/
def denseOpenSections (X : Scheme) : (DenseOpens X)ᵒᵖ ⥤ CommRingCat :=
  (denseOpensInclusion X).op ⋙ X.presheaf

```

`lean/Sheaf/AlgebraicGeometry/RationalFunctionRing.lean`:

```lean
noncomputable def rationalFunctionRing (X : Scheme.{v}) : CommRingCat.{v} :=
  colimit (denseOpenSections X)

```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/RationalFunctions.lean` using `deleted.txt`.
The compatibility module `Sheaf.AlgebraicGeometry.RationalFunctionRing` now contains
only its header, module docstring, public section, and

```lean
public import WeilConjectures.AlgebraicGeometry.RationalFunctions
```

It re-exports the following existing upstream construction, verbatim and unmodified:

```lean
def DenseOpens (X : Scheme) := {U : X.Opens // Dense (U : Set X)}

instance (X : Scheme) : PartialOrder (DenseOpens X) := inferInstanceAs
  (PartialOrder {U : X.Opens // Dense (U : Set X)})

/-- The intersection of two dense opens is dense (Stacks, Tag 01RS;
(blueprint: def-sc-function-field)). -/
def DenseOpens.inter {X : Scheme} (U V : DenseOpens X) : DenseOpens X :=
  ⟨U.val ⊓ V.val, by
    change Dense ((U.val : Set X) ∩ (V.val : Set X))
    exact U.property.inter_of_isOpen_left V.property U.val.isOpen⟩

/-- Dense opens are cofiltered: `⊤` is dense and two dense opens contain their intersection. -/
instance (X : Scheme) : IsCofiltered (DenseOpens X) := by
  have : Nonempty (DenseOpens X) := ⟨⟨⊤, dense_univ⟩⟩
  have : IsDirected (DenseOpens X) (· ≥ ·) :=
    ⟨fun U V => ⟨U.inter V, (inf_le_left : U.val ⊓ V.val ≤ U.val),
      (inf_le_right : U.val ⊓ V.val ≤ V.val)⟩⟩
  infer_instance

/-- The inclusion of dense opens into all opens (Stacks, Tag 01RS;
(blueprint: def-sc-function-field)). -/
def denseOpensInclusion (X : Scheme) : DenseOpens X ⥤ X.Opens where
  obj U := U.val
  map f := homOfLE (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The section rings over dense opens with restriction maps (Stacks, Tag 01RV;
(blueprint: def-sc-function-field)). -/
def denseOpenSections (X : Scheme) : (DenseOpens X)ᵒᵖ ⥤ CommRingCat :=
  (denseOpensInclusion X).op ⋙ X.presheaf

/-- The ring of rational functions on a scheme is the colimit of its section rings on
 dense opens, with transition maps given by restriction. Thus elements are section classes,
 identified when they agree on a smaller dense open; addition and multiplication are induced
 by restriction to intersections and the ring operations on sections. Source: Stacks Project,
 Tags 01RT, 01RU and Lemma 01RV (blueprint: def-sc-function-field). -/
noncomputable def rationalFunctionRing (X : Scheme.{u}) : CommRingCat.{u} :=
  colimit (denseOpenSections X)

```

Redirect the `lean` attachment of `def-sc-rational-functions` to the upstream module
and declaration. Its mathematical statement, dependencies, and unit route stay identical.
The colimit uses exactly the same diagram and ring universe; this includes the empty scheme,
where the rational-function ring is the zero ring. No irreducibility assumption is added.
Target statements do not use a different mathematical definition after this deduplication;
the normal independent reader should check this replacement as a definition change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RationalFunctions | T1 | Withdraw duplicate dense-open definitions. |
| Sheaf.AlgebraicGeometry.RationalFunctionRing | unclaimed | Replace duplicate colimit definition and old import by upstream re-export. Compiles in 1.5 s. |
| Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks | unclaimed | Sole transitive consumer; original 236-line file compiles unchanged against the replacement in 4.0 s. No delivered edit. |

Source search across `lean/Sheaf` and `lean/WeilConjectures` found no further imports
or declaration uses of the retired module or its wrapper. `tools/downstream.py` is
also used to enumerate the import consumers.

## Status

landed 20261020T135426-L-1822122 2026-10-20 (merge of deliver/T1/Sheaf.AlgebraicGeometry.RationalFunctions)
