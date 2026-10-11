## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer` states
`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_range_eq_stabilizer`.
Its sole theorem has proof `sorry`; it introduces no global definitions.
The node's statement and all its other fields are unchanged, except for its `lean` record.

Hypotheses and objects, matched individually:

- The schemes Y' and Y are `{X Y : Scheme.{u}}`; their connectedness is
  `[ConnectedSpace X] [ConnectedSpace Y]`.
- The finite étale morphism is `(f : X ⟶ Y) [IsFinite f] [Etale f]`.
- The geometric point ybar' is `(s : Spec (.of Ω) ⟶ X)`, with explicitly bound
  `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`. Its composite ybar is `s ≫ f`.
  Algebraic closedness supplies the separable closedness required by `fiber`.
- The cover as an object of FEt(Y) is the local abbreviation
  `P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩`.
- Its finite geometric fibre is `(fiber (s ≫ f)).obj P`. The marked point is
  `a := fiberMk (s ≫ f) P s rfl`, using the actual morphism `s`.
- The fundamental groups are `(GX GY : Type u)` with group, topology, topological-group,
  compactness and fibre actions, together with `IsFundamentalGroup (fiber s) GX` and
  `IsFundamentalGroup (fiber (s ≫ f)) GY`. These are presentations of the fundamental
  groups, not extra geometric restrictions. The source's `toAutContinuousMulEquiv`
  canonically identifies each such presentation with the natural-automorphism group,
  including its evaluation topology. Its `exists_isFundamentalGroup` guarantees models
  in universe u for every scheme under consideration. All universes and variables
  are explicitly bound. The node itself uses the finite-étale description of the action;
  its proof identifies this with FLC through `thm-galois-lc-etale`.
- The homomorphism f_* is the existing
  `fundamentalGroupMap (pullbackFiberIso f s) GX GY`. It is the map characterized by
  `fundamentalGroupMap_smul`, with the canonical projection isomorphism `pullbackFiberIso`.
  `continuous_fundamentalGroupMap` already asserts its continuity: no arbitrary
  homomorphism or extra intertwining assumption replaces it.
- The subgroup U is exactly `MulAction.stabilizer GY a`.

The three conclusion clauses are, respectively:

- `(fundamentalGroupMap (pullbackFiberIso f s) GX GY).range = U`;
- `IsOpen (U : Set GY)` (U already is a subgroup by `MulAction.stabilizer`);
- `U.index = Nat.card ((fiber (s ≫ f)).obj P)`.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is a convention record, not a declaration.
  Its standard meanings are Mathlib `Scheme`, `IsFinite`, `Etale`; connectedness is
  `ConnectedSpace`, and geometric points are morphisms from Spec of algebraically closed fields.
- `def-galois-categories`: its record's note identifies FEt with
  `AlgebraicGeometry.Scheme.FiniteEtale` and the fibre with `FiniteEtale.fiber` in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`.
  I read the whole module and also `Sheaf.AlgebraicGeometry.GaloisCategories`, which
  supplies only FLC; the theorem has no sheaf-category expression requiring that import.
- `def-galois-fibre-functor`: the recorded declaration is
  `AlgebraicGeometry.Scheme.FiniteEtale.fiber` in that same source module.
  Its finite-set values, Mathlib `Aut`, evaluation topology from
  `Mathlib.CategoryTheory.Galois.Topology`, and fundamental-group characterization
  from `Mathlib.CategoryTheory.Galois.IsFundamentalgroup` are reused.
  There is no need for a private definition of a fundamental group or its action.
- `lem-galois-pi1-functoriality`: `FiniteEtale.pullback` is in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality`;
  `pullbackFiberIso`, `fundamentalGroupMap`, `fundamentalGroupMap_smul`, and
  `continuous_fundamentalGroupMap` are actually defined in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction` (read in full).
  Importing Restriction supplies all of them. The record points at Functoriality for
  the bundle; this is only a module-location imprecision, not an unusable notion.
- `fiberMk` is read in `WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover`.
  `Mathlib.GroupTheory.Index` supplies the standard subgroup index.

Edge cases checked before writing: the empty scheme admits no geometric point (and
ConnectedSpace also requires nonemptiness), so no artificial empty-cover assumption is added.
A degree-one cover, in particular the identity, has the full group as stabilizer and index one.
A disconnected finite étale cover is deliberately excluded by connectedness of X:
otherwise the index would be only the marked orbit's size. In arbitrary characteristic,
including positive characteristic, `IsAlgClosed Ω` works and no characteristic hypothesis
is imposed. No Noetherian, finite-type base, normality or properness assumption is added.
Universe u is arbitrary and the essentially-small finite étale category has fundamental
models in that universe, as documented in source Basic.lean; using these models does not
limit the geometric cases or the cardinalities of the fibres.

Searches for an existing exact theorem (2026-10-11):

- msearch LeanFinder: "fundamental group of connected finite etale cover image is open
  stabilizer of index fiber cardinality". Eight results include
  `exists_set_ker_evaluation_subset_of_isOpen`, `fiberIsoQuotientStabilizer`, and
  `IsFundamentalGroup`; none identifies the image of the cover's group map.
- msearch Loogle: "MulAction.stabilizer, Subgroup.index". Three hits include
  `MulAction.index_stabilizer_of_transitive` and `MulAction.index_stabilizer`.
  They give the cardinality clause for a transitive action, not the image equality.
- msearch Mathlib grep: "fundamentalGroupMap.*(range|stabilizer)|fiberIsoQuotientStabilizer".
  Only two hits in Galois/EssSurj; no theorem about fundamental groups of covers.
- msearch LeanSearch: "finite etale cover fundamental group image stabilizer".
  Service unavailable: Internal Server Error; no search verdict claimed.
- rg in project source and `lean/Sheaf`: "pi1|fundamentalGroup|stabilizer" and
  "lem-galois-pi1-finite-etale-image-stabilizer|range.*stabilizer|stabilizer.*range".
  Restriction.lean provides injectivity of a finite étale map, but no image/stabilizer
  theorem; other hits concern Frobenius and unrelated decomposition stabilizers.
- Exact proposed name `fundamentalGroupMap_range_eq_stabilizer` searched in Mathlib,
  source WeilConjectures, `dag/lean_names_upstream.json`, and `lean/Sheaf`: no collision.

Source checked directly at https://arxiv.org/pdf/math/0206203, Exposé V,
Proposition 6.13 (PDF page 130, printed page 114), and the beginning of §7.
The proposition is the connected-object slice statement; the scheme cover specializes it.
Its openness and stabilizer identification agree with the node. The index clause follows
from the transitivity already cited in the node. The module docstring retains all four
proof steps and their cited DAG nodes for stage 3. No statement fault or dispute was found.

Validation: server scompile completed cleanly in 2.2 seconds, without warnings.
The initial elaboration needed `inferInstanceAs (IsFinite f)` for the finite proof of P;
this is the supplied hypothesis, not a new proof or assumption.

## Second reading by E1

Independent object/hypothesis/conclusion inventory, with the node and the module open:

1. Connected schemes Y' and Y: `{X Y : Scheme.{u}} [ConnectedSpace X]
   [ConnectedSpace Y]`. PASS: these are arbitrary schemes, with no base field,
   Noetherian, normality, finite-type or properness hypothesis.
2. Finite etale map f: `(f : X ⟶ Y) [IsFinite f] [Etale f]`. PASS: Mathlib's
   scheme morphism properties are the meanings fixed by the convention dependency.
3. Geometric point ybar' and its image ybar: `{Ω : Type u} [Field Ω]
   [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)` and `s ≫ f`. PASS: the convention
   explicitly defines geometric points with an algebraically closed field, not merely
   a separably closed one. The latter property is automatically available to `fiber`.
4. Y' as a finite etale cover of Y: the let-bound
   `P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩`. PASS:
   this is the supplied map itself, not an auxiliary cover or a connected component.
5. Fibre and its marked element: `(fiber (s ≫ f)).obj P` and
   `fiberMk (s ≫ f) P s rfl`. PASS: `fiberMk` is `Over.homMk t ht`, so the element
   really is s over its composite with f. `finite_fiber` supplies finiteness.
6. Fundamental groups and their specified actions: GX and GY, their group/topology/
   compactness instances, the actions on all fibres and the two `IsFundamentalGroup`
   instances. PASS: I read Mathlib's class and the source extension's
   `toAutContinuousMulEquiv`: these data give the canonical evaluation isomorphism
   with Aut of the fibre functor, as a topological group. The actions are natural,
   continuous and faithful, not arbitrary actions substituted for the node's action.
   `FiniteEtale.exists_isFundamentalGroup` and `essentiallySmall` in Basic.lean
   supply such models in universe u for every connected scheme. Thus these binders
   choose presentations and impose no additional geometric hypothesis. The node
   explicitly allows the finite-etale fibre description, with the FLC identification
   supplied by its cited `thm-galois-lc-etale`.
7. Canonical continuous map f_*: `fundamentalGroupMap (pullbackFiberIso f s) GX GY`.
   PASS: Restriction.lean defines this by the transported action and the canonical
   equivalence to Aut. Its `fundamentalGroupMap_smul` uses the required projection
   bijection, and `continuous_fundamentalGroupMap` supplies continuity from the
   continuity already included in `IsFundamentalGroup`. No arbitrary map or extra
   intertwining hypothesis is assumed.
8. Stabilizer subgroup U: `let U := MulAction.stabilizer GY a`. PASS: the actual
   action and marked fibre point are used, and U is already a subgroup.
9. Image equals U: `(fundamentalGroupMap (pullbackFiberIso f s) GX GY).range = U`.
   PASS: full image equality, with no surjectivity hypothesis or weakened inclusion.
10. U is open: `IsOpen (U : Set GY)`. PASS: the evaluation topology is the one
    identified by the topological-group equivalence in item 6.
11. Index is the full geometric fibre size:
    `U.index = Nat.card ((fiber (s ≫ f)).obj P)`. PASS: standard subgroup index,
    not orbit size substituted for full fibre size. X's connectedness justifies
    transitivity. The conjunction gives precisely the three clauses of the node;
    all objects are introduced before those clauses, and no quantifier is reversed.

Dependencies were independently opened: the four JSON statement dependencies, the
GaloisCategories module (its new declaration is FLC, but its lean.note explicitly
reuses FiniteEtale and fiber for the clauses needed here), FiniteEtale.lean's category
and fibre definitions, Functoriality.lean's pullback, Restriction.lean's path and map
API, ConstantCover.lean's fiberMk, Basic.lean's smallness/model existence, and both
Mathlib and the source extension's IsFundamentalgroup modules. They serve the same
notions as the node. There are no new nodes or dependency modules in this delivery,
no private notion copies, no data-valued sorry, and no missing dependency to repair.

Source reading: [SGA 1](https://arxiv.org/pdf/math/0206203), Expose V.6.13,
printed p. 114 (PDF page 130), assumes an abstract Galois category, a connected
object S and a marked element a of F(S); the slice fibre is the inverse image of a.
It gives the open stabilizer image. The connected fibre's transitivity supplies
its index. I also read the beginning and final paragraph of V §7, pp. 115-116.
A detail absent from the first report is that §7 assumes locally Noetherian schemes.
This does not force a restriction of the node: V.6.13 is abstract, and
[Stacks 0BNB](https://stacks.math.columbia.edu/tag/0BNB) supplies the same Galois
category for every connected scheme; its proof identifies connected objects with
connected schemes. [Stacks 0BND](https://stacks.math.columbia.edu/tag/0BND)
provides the canonical map for arbitrary connected schemes. Applying V.6.13 to
that category and its slice gives exactly the node's general statement.
I added this generality justification to the module docstring. No Lean signature,
node statement, dependency list or proof step required alteration.

Edge cases: an empty X cannot admit s; an empty Y cannot receive s ≫ f. Thus
ConnectedSpace's nonemptiness does not discard a pointed empty case. The marked
point makes the fibre nonempty, so degree zero is impossible under these hypotheses;
there is no hidden positive-degree assumption. Identity/degree-one covers give U = GY
and index one. A disconnected cover would only give the marked orbit's size, and is
correctly excluded by the node. Empty other covers Q are still included in the
family of action instances and cause no restriction. Zero objects and empty index
sets are not parameters of this statement. Every characteristic is covered; there
is no CharZero or residue-field finiteness assumption. Universe u is bound and
arbitrary; scheme, field and small fundamental-group models can be placed in a
common universe, and Basic.lean proves the group model exists already in u.

Independent searches, 2026-10-11 (using different conceptual wording):

- LeanFinder via msearch: "image of homomorphism induced by connected covering
  equals point stabilizer"; eight hits. `fiberIsoQuotientStabilizer` concerns the
  quotient by a stabilizer in one category; the other hits concern group actions.
  None states the induced-map image equality for finite etale covers.
- Loogle via msearch: "Subgroup.index, MulAction.stabilizer"; three hits, including
  `MulAction.index_stabilizer_of_transitive` and `MulAction.index_stabilizer`.
  They supply only the group-action index calculation, not this theorem.
- Mathlib grep via msearch: "(image|range).*stabilizer|stabilizer.*(image|range)";
  seven hits in unrelated actions and Galois/IsFundamentalgroup, no exact theorem.
- LeanSearch via msearch: "etale fundamental group connected finite cover stabilizer
  subgroup"; service unavailable (Internal Server Error). No verdict claimed.
- Direct rg in source WeilConjectures, repository lean/Sheaf, and Mathlib Galois:
  `range.*stabilizer|stabilizer.*range|image.*stabilizer|stabilizer.*image|fundamentalGroupMap`.
  Restriction has injectivity and conditional surjectivity; HomotopyExactSequence
  concerns a different geometric-fibre map. No exact image/stabilizer theorem.
- Exact declaration-name rg in dag/lean_names_upstream.json, source WeilConjectures,
  Mathlib and repository lean/Sheaf found no collision.

H5-H9: sole theorem remains `by sorry`; local P/a/U definitions have actual data.
Both docstrings carry the source and blueprint id. All four proof steps and their
DAG references remain in the theorem docstring. Imports supply the actual map and
subgroup index; namespace, topic, line widths and explicit universe/binders comply.
The node's lean.statement remains verbatim the signature in the file.

Changes: source-generality explanation added to the module docstring; independent
reading and search evidence added here. No mathematical mismatch was found.
Validation: initial signature compiled cleanly on the server in 2.0 seconds; the
final docstring edit is checked again by deliver2's compile and preflight.
