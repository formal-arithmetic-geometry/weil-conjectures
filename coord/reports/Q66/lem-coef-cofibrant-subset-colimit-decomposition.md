## Worker report

The module `Sheaf.AlgebraicTopology.CofibrantSubsetColimitDecomposition` states
`SSet.ProperSubsetDiagram.cofibrant_face_decomposition`, together with
`face_decomposition_naturality` and `decompositionIso_naturality`. These are the three
postponed theorems, each with its whole proof `sorry`, associated to the same DAG node's
pushout/cofibrancy/injectivity and naturality clauses. Their docstrings give the node's
complete proof, including the finite-downset induction and shifted-face argument.
The item statement and dependency lists are unchanged. No statement dispute was found.

All auxiliary constructions belong to the objects and canonical maps explicitly introduced
by this item. They do not introduce a second simplicial-set, colimit, cofibration, or
model-category notion. In particular no independent cofibrancy predicate is introduced:
the theorem spells out the specified degreewise latching injections directly. No new node
or dependency-module repair is needed. Every definition has real data. `decompositionIso`
uses the unique colimit universal property furnished by the pushout clause, through
`IsPushout.isoPushout.symm`, so it is a canonical construction rather than a choice of an
unspecified isomorphism.

Hypothesis and clause correspondence (namespace `SSet.ProperSubsetDiagram` throughout):

| Node clause | Lean rendering |
| --- | --- |
| Small simplicial sets | `SSet.{u}`, Mathlib's functors `SimplexCategoryᵒᵖ ⥤ Type u`. |
| Ordinary small colimits formed degreewise | Mathlib `colimit`, `colimit.desc`, `colim.map`, `colimit.pre`; the functor-category colimit instances compute these pointwise in `Type u`. |
| Finite set `S` | `{ι : Type u}` and `{S : Finset ι}`. The ambient type need not be finite. Classical equality is selected within each declaration, so no decidable-equality hypothesis is added. |
| Nonempty `S` and distinguished `s ∈ S` | `(s : ι) (hs : s ∈ S)`; the membership entails nonemptiness. |
| Category of proper subsets, including the empty subset when proper | `Set.Iio S`, the subtype `{R : Finset ι // R ⊂ S}`, with its inherited partial-order category. Arrows are precisely inclusions. |
| `S' = S \ {s}` | `S.erase s`. The proof `Finset.erase_ssubset hs` makes it an object of `Set.Iio S`. |
| Arbitrary diagram `Z` | `(Z : Set.Iio S ⥤ SSet.{u})`. |
| `A_R = Z_R` with its structure maps | `faceA s Z = inclusion (Finset.erase_subset s S) ⋙ Z`. |
| `B_R = Z_{R ∪ {s}}` with its structure maps | `faceB s hs Z = containingFace s hs ⋙ Z`; `containingFace` sends `R` to `insert s R.val` and inclusions to inclusions. |
| `C = Z_{S'}` | `Z.obj ⟨S.erase s, Finset.erase_ssubset hs⟩`. |
| Canonical span map `colim A → C` | `toOppositeFace s hs Z`, defined as the latching map at `S.erase s`, using the cocone of the actual structure maps. |
| Canonical span map `colim A → colim B` | `faceColimitMap s hs Z = colim.map (faceMap s hs Z)`, where `faceMap.app R` is `Z.map` of `R ⊆ insert s R`. |
| Canonical map `colim B → colim Z` | `fromContainingFace s hs Z = colimit.pre Z (containingFace s hs)`. |
| Structure map `C → colim Z` | `colimit.ι Z ⟨S.erase s, Finset.erase_ssubset hs⟩`. |
| Natural canonical pushout isomorphism, without cofibrancy | First conjunct `IsPushout` on the four displayed canonical maps. `decompositionIso` explicitly gives `pushout (toOppositeFace ...) (faceColimitMap ...) ≅ colimit Z` with the specified coprojections. |
| Cofibrancy means every proper subset's latching map is degreewise injective | Antecedent `∀ (T : Set.Iio S) (n : ℕ), Function.Injective ((latchingMap Z T).app (.op ⦋n⦌))`. The latching diagram is `inclusion T.property.le ⋙ Z`, indexed by all `R ⊂ T.val`. |
| `A` cofibrant in the same sense | First consequent conjunct uses exactly the same `latchingMap` on `faceA s Z`, for every `T : Set.Iio (S.erase s)` and degree `n`. |
| `B` cofibrant in the same sense | Second consequent conjunct likewise uses `latchingMap (faceB s hs Z) T`. |
| Each of the three specified maps is degreewise injective | Last three consequent conjuncts apply `Function.Injective` to the degree-`n` components of `toOppositeFace`, `faceColimitMap`, and `fromContainingFace`, for every `n : ℕ`. |
| All canonical maps are natural in `Z` | `face_decomposition_naturality` gives all four edge squares for an arbitrary natural transformation `τ : Z ⟶ W`; the induced colimit maps are `colim.map` of `τ` or its whiskered restrictions. No cofibrancy assumption is imposed. |
| Pushout comparison is natural in `Z` | `decompositionIso_naturality` states the square between the two `decompositionIso.hom`s, `colim.map τ`, and `pushout.map` of the canonical induced span map. Its compatibility proofs are the first two edge-naturality equations. |
| Singleton case included | There is no cardinality lower bound beyond `hs`; when `S = {s}`, `S.erase s = ∅` and `Set.Iio ∅` is empty. No nonempty-index hypothesis is imposed on the colimits. |

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set` has the Mathlib match `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`. Its actual abbreviation and docstring
  were read. The matched `degenerate`, `nonDegenerate`, `Subcomplex`, and `SSet.Finite`
  declarations in the recorded `Degenerate`, `Subcomplex`, and `Finite` modules were also
  read; those additional aspects are not used in this node.
- `def-weil-pbc-category-colimit` records `CategoryTheory.Limits.colimit` in
  `Mathlib.CategoryTheory.Limits.HasLimits`, with `Cocone`, `IsColimit`, and
  `colimit.desc`. Their definitions and docstrings were read. The module imports that
  recorded module publicly and uses the chosen ordinary colimit and its actual
  canonical cocones, not replacement colimit data.
- Proof dependency `lem-coef-set-pushout-injective` matches
  `CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit` in
  `Mathlib.CategoryTheory.Limits.Types.Pushouts`. Its exact signature was read: the
  injectivity assumption is only on the opposite span leg. This module is a plain
  proof import and steps 4 and 8 of the proof docstring identify its uses.

Edge cases checked mathematically before writing: `S` singleton gives `a = b = ∅`,
`C = Z_∅`, and `colim Z = C`; all three maps with empty source are injective, and both
face-cofibrancy assertions are vacuous. At an empty subset of any nonempty index set,
the latching diagram is empty and imposes precisely the unique injection from the initial
simplicial set. For two-element `S`, the decomposition is the pushout of the empty-face
value into the two singleton values. Degree zero is included by `n : ℕ`; no nondegeneracy,
connectedness, objectwise finiteness, or structure-map injectivity assumption was added.
The pushout conclusion is outside the cofibrancy implication, as required. The constructions
are simplicial maps, not unrelated functions chosen separately in each degree.

Searches made with the prescribed `msearch.py` wrapper (2026-10-17):

- LeanFinder: "A cofibrant diagram on proper subsets of a finite set has a pushout
  decomposition into two face colimits and injective latching maps". Eight hits,
  including `SSet.horn.isColimit`, `SSet.Subcomplex.MulticoequalizerDiagram`, and general
  cell-attachment lemmas. None states this arbitrary proper-subset diagram theorem.
- Loogle: `SSet, IsPushout, colimit` reported unknown identifier `IsPushout`; repeated
  with `"SSet", "isPushout"`, returning eight hits on horn, subcomplex-union, and cell
  pushouts. Those require different input data and do not state this lemma.
- Mathlib grep: `latching|cofibrant|proper.*subset` under
  `AlgebraicTopology/SimplicialSet` returned only the cofibrant import in `KanComplex`.
- LeanSearch: "The colimit of a diagram over proper subsets of a finite set is the
  pushout of its two face colimits and the opposite-face value". Eight hits on general
  pushout universal properties and disjoint-union coproduct colimits, no full match.
- Direct `rg` of project `lean/Sheaf` and upstream `WeilConjectures` for
  `latching|cofibrantSubset|properSubset|subsetColimit|face.*[Cc]olimit` found generic
  incoming-arrow latching constructions and discussions in existing Rezk/simplicial
  modules, but no finite-subset face constructions or this theorem. The general
  model-category latching notions do not replace the explicit subset latching map here.
- Direct upstream search for the exact node id returned no match. Searches in
  `dag/lean_names_upstream.json`, `lean/Sheaf`, and upstream `WeilConjectures` for the
  chosen namespace and theorem/comparison names returned no collisions.

Source checked online: Rezk's `rezk-sharp-maps.pdf`, Section 6.3 on printed page 11
and Proposition 6.4 on printed page 12. The source defines the shifted face by adjoining
the distinguished element and gives the natural pushout with the latching injection.
The node's additional shifted cofibrancy and map `a → b` follow by the expanded
finite-downset argument, which is retained in the theorem docstring. Archival PDF copy
WANTED: the source was read online; this worker is authorized to write only its sandbox.

Validation: the final module is checked with the required `scompile.py` wrapper, one file
at a time, under the default 60-second limit. Only the three named theorem proofs are
postponed. The required `deliver2.py --no-push` dry run is run after compilation;
independent second reading and actual delivery belong to the next worker.

## Second reading by Q66

I independently read the node, the whole delivered module, both statement-dependency
records and their Mathlib declarations, and the proof-dependency record and declaration.
There is no repair note for this item. The source of this node is Rezk, not Stacks:
I opened `https://rezk.web.illinois.edu/rezk-sharp-maps.pdf` and read Section 6.3
(printed p. 11) and Proposition 6.4 with its proof (printed p. 12). The source works in
simplicial objects in a Grothendieck topos; its specialization to sets is exactly the
node's setting. Section 6.3 defines cofibrancy by the indicated proper-subset colimit
maps, and Proposition 6.4 gives the natural pushout with its two vertical injections.
The node explicitly includes the shifted-face and third-injection consequences of
the expanded finite latching induction. I checked that induction, including the
downward closure after deleting the maximal subset and the containing-face cocone
extension. No additional model-category hypothesis is needed for these consequences.

My list of objects, hypotheses and conclusions, checked against the Lean:

| Node item | Actual Lean rendering and verdict |
| --- | --- |
| Small simplicial sets and simplicial maps | `SSet.{u}` and its natural transformations. I read `SSet := SimplicialObject (Type u)` in the recorded Mathlib Basic module. Exact. |
| Ordinary degreewise colimits | Mathlib's `colimit`, `colimit.desc`, `colim.map`, and `colimit.pre`, with the imported functor-category colimit instances. I read the chosen-colimit interface and `IsColimit`'s existence, factorization and uniqueness fields. Exact. |
| Finite nonempty set `S` | `{ι : Type u}`, `{S : Finset ι}`, `(s : ι)`, `(hs : s ∈ S)`. Membership supplies precisely the stated nonemptiness and distinguished element. The ambient type need not be finite; no `DecidableEq` hypothesis is added. Exact. |
| Proper-subset categories and inclusion arrows | `Set.Iio S` is the subtype of finsets strictly below `S`, with inherited order category. `inclusion h` sends each subset and inclusion to itself. The empty subset is retained whenever proper. Exact. |
| `S' = S \ {s}` | `S.erase s`, with `Finset.erase_ssubset hs` placing it in the original index category. Exact. |
| Arbitrary original diagram | `(Z : Set.Iio S ⥤ SSet.{u})`, without hypotheses on its objects or transition maps. Exact. |
| Omitting face `A_R = Z_R` | `faceA s Z := inclusion (Finset.erase_subset s S) ⋙ Z`. Both objects and maps are the prescribed restriction. Exact. |
| Containing face `B_R = Z_(R ∪ {s})` | `faceB s hs Z := containingFace s hs ⋙ Z`; `containingFace.obj R` is `insert s R.val`, and its map is induced by inclusion. Its properness proof uses `R ⊂ S.erase s`. Exact. |
| Opposite-face object `C` | `Z.obj ⟨S.erase s, Finset.erase_ssubset hs⟩`. Exact. |
| Span map `colim A → C` | `toOppositeFace` is `latchingMap` at that opposite-face object. `latchingCocone` has components `Z.map (homOfLE R.property.le)`, so this is the required canonical map. Exact. |
| Span map `colim A → colim B` | `faceColimitMap := colim.map (faceMap s hs Z)`, whose components are the structure maps from `R` to `insert s R`. Exact. |
| Remaining pushout edges | `colimit.ι Z ⟨S.erase s, ...⟩` and `fromContainingFace := colimit.pre Z (containingFace s hs)`. These are precisely `C → colim Z` and `colim B → colim Z`. Exact. |
| Canonical pushout comparison without cofibrancy | First conjunct of `cofibrant_face_decomposition` is `IsPushout` of those four maps, outside the implication. `decompositionIso` is its `isoPushout.symm`. I read `IsPushout` and `isoPushout`: they use the specified cocone's colimit universal property, and its inverse respects both coprojections. Exact and non-hollow. |
| Cofibrancy assumption on every proper subset | Antecedent quantifies over all `(T : Set.Iio S)` and `(n : ℕ)` and asks injectivity of `(latchingMap Z T).app (.op ⦋n⦌)`. Its source diagram is exactly all strict subsets of `T.val`, not just codimension-one subsets. Exact. |
| Cofibrancy of `A` | First consequent repeats that same latching condition for `faceA s Z` on `Set.Iio (S.erase s)`. Exact. |
| Cofibrancy of `B` | Second consequent repeats it for `faceB s hs Z`, with no separate assumption that shifted structure maps are injections. Exact. |
| Injection `colim A → C` | Third consequent is injectivity of every degree component of `toOppositeFace`. Exact. |
| Injection `colim A → colim B` | Fourth consequent uses every degree component of `faceColimitMap`. Exact. |
| Injection `colim B → colim Z` | Fifth consequent uses every degree component of `fromContainingFace`. Exact. |
| Naturality of all canonical edges | `face_decomposition_naturality` quantifies over arbitrary `τ : Z ⟶ W` and gives the four edge squares using its component at `C` and colimit maps of the appropriate whiskerings. No cofibrancy is assumed. Exact. |
| Naturality of the comparison isomorphism | `decompositionIso_naturality` gives the square with `pushout.map`, the comparison homomorphisms and `colim.map τ`; its span-compatibility proofs are the correctly oriented first two edge equations. Exact. |
| Singleton case | There is no cardinality or nonempty-index assumption besides `hs`. Both face diagrams can be empty. Exact. |

Edge cases: `S = ∅` is excluded by the node and by `hs`, rather than silently assumed
away. For `S = {s}`, both face index categories are empty; `a` and `b` are initial,
`C = Z_∅`, the pushout is `C`, and both face cofibrancy conditions are vacuous.
For a two-element `S`, the original diagram is exactly the span from `Z_∅` to the two
singleton values, which checks all four edge orientations. At the empty proper subset,
the latching source is initial, as required. Diagrams of empty simplicial sets are
allowed. Degree zero is included by `n : ℕ`; no characteristic, scheme, nondegeneracy,
connectedness, or objectwise finiteness assumption enters. The one small universe
contains the simplices and finite indexing data, and is arbitrary; no site universe
identification or bound on the size/cardinality of the ambient type is assumed.

Independent H4 searches (2026-10-17), using different queries from the worker:

- `msearch.py ... leanfinder "A punctured finite cube of simplicial sets decomposes as
  a pushout of its two faces, and injective latching maps remain injective on the
  shifted face"`: eight hits, including `SSet.Subcomplex.BicartSq.isPushout` and
  simplex/nondegeneracy results. The former concerns specified subcomplexes of one
  simplicial set, not an arbitrary diagram on the proper subsets. No exact match.
- `msearch.py ... leansearch "Colimits over lower ideals of a finite poset embed when
  all latching morphisms are monomorphisms"`: eight hits on filtered colimits,
  `PartOrdEmb`, and small-object iterations. These do not state the finite proper-subset
  face decomposition or its shifted cofibrancy condition.
- Direct `rg` in Mathlib's AlgebraicTopology and CategoryTheory, upstream
  `WeilConjectures`, and project `lean/Sheaf`, using `punctured`, `lower.?ideal`,
  `down.?set`, `latching`, `proper.?subset` and subset/colimit combinations. I read
  the relevant declarations in `ReedyModelStructure`, `DirectWeakFactorization`,
  `SmallDirectColimitLifting`, and `CellularTree`, and the proper-subset discussion in
  `RezkDiagonalSharp`. The generic latching APIs use incoming-arrow slices (and the
  cellular-tree API uses undercategory diagrams), not the node's literal subset
  restriction. They provide no existing face construction or statement to bind this
  node to. The delivered helpers construct these explicit subset cocones using the
  recorded colimit definition; they introduce no alternative cofibrancy predicate.
- Exact searches for `ProperSubsetDiagram`, `cofibrant_face_decomposition`, and
  `CofibrantSubsetColimitDecomposition` in `dag/lean_names_upstream.json`, upstream
  `WeilConjectures`, and the project Lean tree found no name collisions.

The recorded proof dependency is usable: I read
`Types.pushoutCocone_inr_injective_of_isColimit` in Mathlib Types/Pushouts, including
its assumption solely on `f`. It has the orientation used in proof steps 4 and 8.
There are no new nodes or dependency modules to audit, no `statement_change`, and
only `lean` differs from the repository node. The recorded main signature is verbatim
equal to the module signature. Every variable and universe is bound, all lines meet
the width limit, and all declarations have the source/blueprint docstrings. The three
named theorems have whole proofs `sorry`; the definitions contain real data and only
their structural functor/cocone laws are proved. The proof docstrings collectively
cover all nine node steps and the singleton case.

Mismatches found: none. Changes: appended this independent second reading; left the
correct Lean and node record unchanged. Validation: `scompile.py Q66
lem-coef-cofibrant-subset-colimit-decomposition <module file>` completed successfully
for both the sandbox probe and library module (1.3 s and 1.5 s), with no warnings or
errors. The prescribed server dry run and delivery follow this review.
