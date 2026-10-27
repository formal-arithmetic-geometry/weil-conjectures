# AlgebraicTopology.OrderedJoin constructions

## Reason

The prerequisite singleColorIdentities and functorialExpansion import the item
for its constructions. Importing their theorems to prove partialContraction
therefore creates a cycle. Extract the existing constructions verbatim into
Sheaf.AlgebraicTopology.OrderedJoinChains, owned by the new definition node
`def-sfb-ordered-join-chains`. The item publicly reexports that module.
The two prerequisites change only their public import on line 8. Their existing
signatures, visibility, definitions and proof bodies are unchanged. The import
cycle is an actual failure of lcompile.py with their original files and the
new parent: "the modules import one another in a cycle:
Sheaf.AlgebraicTopology.OrderedJoinFunctorialExpansion,
Sheaf.AlgebraicTopology.OrderedJoinPartialContraction,
Sheaf.AlgebraicTopology.OrderedJoinSingleColorIdentities".

No target changes meaning. Every constructor, definition body, universe, name,
visibility and type stays unchanged. In particular, no arbitrary witness is
introduced. This is a source-location/interface repair, not a mathematical
change of a definition. The definition node records the existing constructions;
it does not add mathematical data or an unproved result.

## Old

Constructions in `lean/Sheaf/AlgebraicTopology/OrderedJoinPartialContraction.lean`:

```lean
structure Face {r : ℕ} (X : Fin r → Type u) where
  colors : Finset (Fin r)
  vertex : ∀ i : Fin r, i ∈ colors → X i

/-- Degree-q ordered symbols: the integer cardinality condition also includes
q=-1 and excludes q<-1 and q>=r. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def Symbol {r : ℕ} (X : Fin r → Type u) (q : ℤ) : Type u :=
  {σ : Face X // (σ.colors.card : ℤ) = q + 1}

/-- The specified free integer module on the degree-q symbols, with specified
basis `Finsupp.basisSingleOne`; this is the basis notion of
`def-weil-pbc-free-module`. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
abbrev Chain {r : ℕ} (X : Fin r → Type u) (q : ℤ) : Type u :=
  Symbol X q →₀ ℤ

/-- Interpret a face as its basis vector in degree q, or zero if it has the wrong
cardinality. The test concerns only colors. Source: direct-images paragraph (3),
agent ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def symbolTerm {r : ℕ} (X : Fin r → Type u) (q : ℤ)
    (σ : Face X) : Chain X q := by
  classical
  exact if h : (σ.colors.card : ℤ) = q + 1 then Finsupp.single ⟨σ, h⟩ 1 else 0

/-- Delete the vertex of color i. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def erase {r : ℕ} {X : Fin r → Type u} (σ : Face X) (i : Fin r) : Face X where
  colors := σ.colors.erase i
  vertex j hj := σ.vertex j (Finset.mem_of_mem_erase hj)

/-- Replace precisely the vertices with colors in A by their chosen vertices.
The test uses only color membership. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def replaceColors {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (A : Finset (Fin r)) (σ : Face X) : Face X where
  colors := σ.colors
  vertex j hj := if j ∈ A then v j else σ.vertex j hj

/-- Insert the chosen vertex of color i, using increasing color order. The
existing vertex is replaced if i was already present; `insertion` uses this
only when i is missing. Source: direct-images paragraph (3), agent ordered-join
expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def insert {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (σ : Face X) : Face X where
  colors := Insert.insert i σ.colors
  vertex j hj := if h : j = i then h.symm ▸ v i
    else σ.vertex j ((Finset.mem_insert.mp hj).resolve_left h)

/-- The sign of the position of color i: the number of earlier colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
def positionSign {r : ℕ} (C : Finset (Fin r)) (i : Fin r) : ℤ :=
  (-1 : ℤ) ^ (C.filter (fun j ↦ j < i)).card

/-- Alternating deletion, extended from the specified basis. The component
from q to q-1 is d; in particular a singleton maps to the empty face and the
empty face maps to zero. Source: direct-images paragraph (3), agent ordered-join
expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def boundary {r : ℕ} (X : Fin r → Type u) (q p : ℤ) :
    Chain X q →ₗ[ℤ] Chain X p :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    ∑ i ∈ σ.val.colors, positionSign σ.val.colors i • symbolTerm X p (erase σ.val i))

/-- The signed insertion c_i, zero on faces already containing i, extended
linearly from the basis. Its degree-one component has p=q+1.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def insertion {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (q p : ℤ) : Chain X q →ₗ[ℤ] Chain X p :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    if i ∈ σ.val.colors then 0
    else positionSign σ.val.colors i • symbolTerm X p (insert v i σ.val))

/-- R_i is zero on missing-color symbols, and otherwise the original symbol
minus the symbol with its color-i vertex replaced by v_i.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def remainder {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (q : ℤ) : Chain X q →ₗ[ℤ] Chain X q :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    if i ∈ σ.val.colors then
      symbolTerm X q σ.val - symbolTerm X q (replaceColors v {i} σ.val)
    else 0)

/-- The ordered prefix R_0 composed with ... composed with R_{n-1}; the rightmost
factor acts first. The empty prefix is the identity. Only n<=r is used.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def remainderPrefix {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (n : ℕ) (q : ℤ) : Chain X q →ₗ[ℤ] Chain X q :=
  (List.range n).foldr (fun j P ↦
    if h : j < r then (remainder v ⟨j, h⟩ q).comp P else P) LinearMap.id

/-- The displayed S=sum_i (R_0 composed with ... composed with R_{i-1}) c_i.
Its degree-one component is `contraction v q (q+1)`.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def contraction {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i : Fin r, X i) (q p : ℤ) : Chain X q →ₗ[ℤ] Chain X p :=
  ∑ i : Fin r, (remainderPrefix v i.val p).comp (insertion v i q p)

/-- Apply the given maps to vertices, preserving colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
def mapFace {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i : Fin r, X i → Y i) (σ : Face X) : Face Y where
  colors := σ.colors
  vertex i hi := f i (σ.vertex i hi)

/-- The induced integer-linear map J_q(f), with no injectivity assumption.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def chainMap {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i : Fin r, X i → Y i) (q : ℤ) : Chain X q →ₗ[ℤ] Chain Y q :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦ symbolTerm Y q (mapFace f σ.val))

/-- The unreduced list of coefficients, insertion colors and replacement sets.
For each absent color i whose predecessors are present, list all subsets A of
its predecessors with sign (-1)^(position(i)+card A). This list depends only on
r and the color set C, and never examines vertices or combines equal symbols.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def expansionRecipe (r : ℕ) (C : Finset (Fin r)) :
    List (ℤ × (Fin r × Finset (Fin r))) :=
  (List.finRange r).flatMap (fun i ↦
    if i ∈ C then []
    else if (Finset.univ.filter (fun j : Fin r ↦ j < i)) ⊆ C then
      ((Finset.univ.filter (fun j : Fin r ↦ j < i)).powerset.toList.map
        (fun A ↦ (positionSign C i * (-1 : ℤ) ^ A.card, (i, A))))
    else [])
```

Both prerequisites:

```lean
public import Sheaf.AlgebraicTopology.OrderedJoinPartialContraction
```

## New

The identical constructions now occur in
`lean/Sheaf/AlgebraicTopology/OrderedJoinChains.lean`:

```lean
structure Face {r : ℕ} (X : Fin r → Type u) where
  colors : Finset (Fin r)
  vertex : ∀ i : Fin r, i ∈ colors → X i

/-- Degree-q ordered symbols: the integer cardinality condition also includes
q=-1 and excludes q<-1 and q>=r. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def Symbol {r : ℕ} (X : Fin r → Type u) (q : ℤ) : Type u :=
  {σ : Face X // (σ.colors.card : ℤ) = q + 1}

/-- The specified free integer module on the degree-q symbols, with specified
basis `Finsupp.basisSingleOne`; this is the basis notion of
`def-weil-pbc-free-module`. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
abbrev Chain {r : ℕ} (X : Fin r → Type u) (q : ℤ) : Type u :=
  Symbol X q →₀ ℤ

/-- Interpret a face as its basis vector in degree q, or zero if it has the wrong
cardinality. The test concerns only colors. Source: direct-images paragraph (3),
agent ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def symbolTerm {r : ℕ} (X : Fin r → Type u) (q : ℤ)
    (σ : Face X) : Chain X q := by
  classical
  exact if h : (σ.colors.card : ℤ) = q + 1 then Finsupp.single ⟨σ, h⟩ 1 else 0

/-- Delete the vertex of color i. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def erase {r : ℕ} {X : Fin r → Type u} (σ : Face X) (i : Fin r) : Face X where
  colors := σ.colors.erase i
  vertex j hj := σ.vertex j (Finset.mem_of_mem_erase hj)

/-- Replace precisely the vertices with colors in A by their chosen vertices.
The test uses only color membership. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def replaceColors {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (A : Finset (Fin r)) (σ : Face X) : Face X where
  colors := σ.colors
  vertex j hj := if j ∈ A then v j else σ.vertex j hj

/-- Insert the chosen vertex of color i, using increasing color order. The
existing vertex is replaced if i was already present; `insertion` uses this
only when i is missing. Source: direct-images paragraph (3), agent ordered-join
expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def insert {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (σ : Face X) : Face X where
  colors := Insert.insert i σ.colors
  vertex j hj := if h : j = i then h.symm ▸ v i
    else σ.vertex j ((Finset.mem_insert.mp hj).resolve_left h)

/-- The sign of the position of color i: the number of earlier colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
def positionSign {r : ℕ} (C : Finset (Fin r)) (i : Fin r) : ℤ :=
  (-1 : ℤ) ^ (C.filter (fun j ↦ j < i)).card

/-- Alternating deletion, extended from the specified basis. The component
from q to q-1 is d; in particular a singleton maps to the empty face and the
empty face maps to zero. Source: direct-images paragraph (3), agent ordered-join
expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def boundary {r : ℕ} (X : Fin r → Type u) (q p : ℤ) :
    Chain X q →ₗ[ℤ] Chain X p :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    ∑ i ∈ σ.val.colors, positionSign σ.val.colors i • symbolTerm X p (erase σ.val i))

/-- The signed insertion c_i, zero on faces already containing i, extended
linearly from the basis. Its degree-one component has p=q+1.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def insertion {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (q p : ℤ) : Chain X q →ₗ[ℤ] Chain X p :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    if i ∈ σ.val.colors then 0
    else positionSign σ.val.colors i • symbolTerm X p (insert v i σ.val))

/-- R_i is zero on missing-color symbols, and otherwise the original symbol
minus the symbol with its color-i vertex replaced by v_i.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def remainder {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (q : ℤ) : Chain X q →ₗ[ℤ] Chain X q :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    if i ∈ σ.val.colors then
      symbolTerm X q σ.val - symbolTerm X q (replaceColors v {i} σ.val)
    else 0)

/-- The ordered prefix R_0 composed with ... composed with R_{n-1}; the rightmost
factor acts first. The empty prefix is the identity. Only n<=r is used.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def remainderPrefix {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (n : ℕ) (q : ℤ) : Chain X q →ₗ[ℤ] Chain X q :=
  (List.range n).foldr (fun j P ↦
    if h : j < r then (remainder v ⟨j, h⟩ q).comp P else P) LinearMap.id

/-- The displayed S=sum_i (R_0 composed with ... composed with R_{i-1}) c_i.
Its degree-one component is `contraction v q (q+1)`.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def contraction {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i : Fin r, X i) (q p : ℤ) : Chain X q →ₗ[ℤ] Chain X p :=
  ∑ i : Fin r, (remainderPrefix v i.val p).comp (insertion v i q p)

/-- Apply the given maps to vertices, preserving colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
def mapFace {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i : Fin r, X i → Y i) (σ : Face X) : Face Y where
  colors := σ.colors
  vertex i hi := f i (σ.vertex i hi)

/-- The induced integer-linear map J_q(f), with no injectivity assumption.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def chainMap {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i : Fin r, X i → Y i) (q : ℤ) : Chain X q →ₗ[ℤ] Chain Y q :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦ symbolTerm Y q (mapFace f σ.val))

/-- The unreduced list of coefficients, insertion colors and replacement sets.
For each absent color i whose predecessors are present, list all subsets A of
its predecessors with sign (-1)^(position(i)+card A). This list depends only on
r and the color set C, and never examines vertices or combines equal symbols.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def expansionRecipe (r : ℕ) (C : Finset (Fin r)) :
    List (ℤ × (Fin r × Finset (Fin r))) :=
  (List.finRange r).flatMap (fun i ↦
    if i ∈ C then []
    else if (Finset.univ.filter (fun j : Fin r ↦ j < i)) ⊆ C then
      ((Finset.univ.filter (fun j : Fin r ↦ j < i)).powerset.toList.map
        (fun A ↦ (positionSign C i * (-1 : ℤ) ^ A.card, (i, A))))
    else [])
```

The item and both prerequisites publicly import the constructions:

```lean
public import Sheaf.AlgebraicTopology.OrderedJoinChains
```

The item additionally has private proof imports of the two prerequisite modules.
Their original declaration signatures and visibility remain identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicTopology.OrderedJoinPartialContraction | V3 | Public reexport of moved constructions; proves its theorem from prerequisites. |
| Sheaf.AlgebraicTopology.OrderedJoinSingleColorIdentities | unclaimed (G9 proof landed) | Required line-8 import adaptation to remove the cycle; no declaration changes. |
| Sheaf.AlgebraicTopology.OrderedJoinFunctorialExpansion | unclaimed (G7 proof landed) | Required line-8 import adaptation to remove the cycle; no declaration changes. |
| Sheaf.AlgebraicTopology.OrderedJoinCosetComparison | R5 | Unchanged: imports item and sees identical constructions by public reexport. |
| Sheaf.RepresentationTheory.FiniteIndexRectanglePrimitiveOperator | unclaimed | Unchanged: same theorem and constructions remain visible. |

The complete downstream list was obtained with tools/downstream.py before
editing. The unchanged consumers retain every imported public declaration by reexport;
their direct checks against the delivery overlay are recorded in the report.
The prerequisite DAG proof records gain the definition dependency; their mathematical
statements and proof routes are unchanged. The parent removes the abstract
prefix-telescope dependency because its proof is carried out directly for
linear maps, without converting the chain groups to a bundled chain complex.

## Status

landed 20261025T071219-L-148254 2026-10-25 (merge of deliver/V3/Sheaf.AlgebraicTopology.OrderedJoinPartialContraction)
