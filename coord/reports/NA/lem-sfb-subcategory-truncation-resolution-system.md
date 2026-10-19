## Worker report

The module `lean/Sheaf/Algebra/Homology/SubcategoryTruncationResolutionSystem.lean`
states `CategoryTheory.subcategory_truncation_resolution_system`. It also defines the
canonical map `CategoryTheory.subcategoryTruncationMap`, which is the map from the good
truncation `K.truncLE n` to `K.truncLE (n + 1)`. The map is constructed from the inverse
of the canonical inclusion of `K.truncLE n` into its `(n+1)`-truncation and
`CochainComplex.truncLEMap` applied to `K.ιTruncLE n`; its data is not postponed. The
project contains a private `cutoffMap` with this construction in
`Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps`, but that private declaration is
not usable from this module, so the public helper is supplied here as part of this node's
notion. Both declarations have source and blueprint docstrings.

The theorem renders the node statement as follows.

* The abelian category is `{C : Type u}` with `[Category.{v} C] [Abelian C]`, using
  Mathlib's `CategoryTheory.Abelian`.
* `P : C → Prop` is the class of objects. `hzero : ∀ X : C, IsZero X → P X` says that
  every zero object belongs to `P`.
* `hiso : ∀ {X : C} {Y : C}, CategoryTheory.Iso X Y → P X → P Y` gives stability under
  isomorphisms.
* `hbiprod : ∀ {X : C} {Y : C}, P X → P Y → P (X ⊞ Y)` gives closure under finite
  biproducts; together with `hzero` this includes the empty finite biproduct.
* `hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p` says every object is covered
  epimorphically by an object of `P`.
* `K : CochainComplex C ℤ` is the integer-indexed cochain complex. The good truncation
  `T_n` is rendered by Mathlib's `K.truncLE n`, whose terms are `K.X i` below `n`, the
  cycle object at `n`, and zero above `n`.
* The conclusion quantifies `E : ℤ → CochainComplex C ℤ`, maps
  `e : ∀ n, E n ⟶ K.truncLE n`, and transitions
  `u : ∀ n, E n ⟶ E (n + 1)`. The maps are total integer-indexed families so that the
  guarded conditions for `n ≥ 1` are direct Lean predicates; the unconstrained negative
  stages can be filled by zero complexes.
* The compatibility square is
  `∀ n : ℤ, 1 ≤ n → u n ≫ e (n + 1) = e n ≫ subcategoryTruncationMap K n`, which is
  exactly `e_{n+1} ∘ u_n = j_n ∘ e_n` with the canonical truncation inclusion.
* For every `n ≥ 1`, the first conjunction gives an integer upper bound `b` with
  `IsZero ((E n).X i)` whenever `b < i`, membership `P ((E n).X i)` of every term,
  epimorphic components `Epi ((e n).f i)`, and `QuasiIso (e n)`. This renders bounded
  above, terms in `P`, termwise epimorphic, and quasi-isomorphic respectively.
* For every `n ≥ 1`, the final conjunction gives `IsSplitMono ((u n).f i)` for every
  degree and `P (cokernel ((u n).f i))` for every component cokernel.

The recorded dependency declarations used are:

* `def-sp-abelian`: Mathlib `CategoryTheory.Abelian` in
  `Mathlib/CategoryTheory/Abelian/Basic.lean` (the node's exact Mathlib match).
* `def-weil-abstract-derived-category`: Mathlib `DerivedCategory` and
  `HasDerivedCategory` in `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`; the
  concrete complex and quasi-isomorphism predicates in this statement are Mathlib's
  `CochainComplex`, `CochainComplex.truncLE`, `CochainComplex.ιTruncLE`, and `QuasiIso`.
  The proof-only dependencies are not imported because this stage states the theorem
  with `sorry`; their Mathlib declarations are named in the theorem docstring.

Edge cases checked: `K = 0` is resolved by zero complexes and `hzero`; the empty finite
biproduct is covered by the zero-object clause; `n = 0` is correctly outside the indexed
conclusion because the source starts at `n ≥ 1`; integer indexing is nonempty and includes
negative degrees; and the cokernel condition uses the chosen categorical cokernel, whose
object is invariant up to the supplied isomorphism stability of `P`.

Searches made before writing:

* `msearch.py leanfinder` with the node's plain-language compatible-resolution query:
  hits were ordinary/projective/injective resolutions and truncation APIs, with no
  compatible tower theorem for an arbitrary quotient-generating class.
* `msearch.py loogle` for `"CochainComplex", "resolution"` and for
  `"LeftResolution", "quasiIso"`: hits were ordinary resolution declarations, or no
  hit for the latter; no exact statement.
* `msearch.py leansearch` for compatible direct systems of bounded-above truncation
  resolutions: hits were direct limits and general localization declarations, with no
  exact statement.
* `msearch.py leanfinder` for Spaltenstein/split-inclusion resolution towers and for
  bounded-above complexes resolved by a quotient-generating class: hits were projective
  or injective resolution APIs only.
* `msearch.py grep` for `special.*direct.*system|subcategory.*resolution|trunc.*resolution|`
  `resolution.*trunc` and for `IsStrictlyLE.*flat|flat.*IsStrictlyLE|specialDirectSystem`: no matching
  declaration in Mathlib or the project.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for truncation-map names found the
  private `cutoffMap` construction noted above, but no public declaration of this node's
  compatible resolution theorem. The dependency node and item IDs were also searched
  throughout `dag/nodes`; no duplicate statement was found.

No statement correction and no `STATEMENT-DISPUTED` flag are needed.


## Second reading by NA

I independently read the node (including all eight proof steps), its sandbox module,
Stacks `derived.tex:9208-9330`, Tag 06XX, local label
`lemma-special-direct-system` (cross-document label
`derived-lemma-special-direct-system`), and the declarations described below. The
surrounding section assumes only an abelian category; the colimit and functor hypotheses
in the subsequent proposition do not apply to this lemma. There is no repair note for
this item. There are no new nodes or dependency modules in this delivery and no
`statement_change`; a correction/citer audit is therefore not applicable.

The following is my object/hypothesis/conclusion checklist against the node.

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary abelian category A | `{C : Type u} [Category.{v} C] [Abelian C]`; exact. Object and morphism universes are independent. |
| Class P of objects | `(P : C → Prop)`; exact, not a subcategory equipped with additional data. |
| Every zero object belongs to P | `hzero : ∀ X : C, IsZero X → P X`; exact. |
| Isomorphism stability | `hiso : ∀ {X} {Y}, Iso X Y → P X → P Y`; exact. This is already a hypothesis of the base DAG node, not an addition by this worker. |
| Closure under finite biproducts | `hbiprod : ∀ {X} {Y}, P X → P Y → P (X ⊞ Y)` together with `hzero`; exact, including the nullary case and iteration. |
| Every object is a quotient of an object of P | `hcover : ∀ X, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p`; exact. No projectivity or functorial choice is assumed. |
| Integer cochain complex K | `(K : CochainComplex C ℤ)`; exact. |
| Good truncation T_n, not stupid truncation | `K.truncLE n`; exact. I read `Embedding/CochainComplex.lean:41-51` and `Embedding/TruncLE.lean:39-95,181-218`: the terms identify with K below the boundary, cycles at the boundary, and zero above. The induced differential to the cycles is recorded at `TruncLE.lean:61-67`. |
| Canonical inclusion j_n | `subcategoryTruncationMap K n`; exact. Its construction uses the inverse of the truncation inclusion of the already bounded `K.truncLE n`, then `truncLEMap (K.ιTruncLE n) (n+1)`. Naturality `CochainComplex.ιTruncLE_naturality` shows its composite with `K.ιTruncLE (n+1)` is `K.ιTruncLE n`; monicity of the latter inclusion makes this the canonical map. |
| Simultaneous complexes E_n and maps e_n, u_n for n ≥ 1 | The three outer existential families `E`, `e`, `u`, followed by guarded clauses `∀ n : ℤ, 1 ≤ n → ...`; exact. Their order gives one compatible system, not unrelated choices for each clause. |
| Strict commutativity | `u n ≫ e (n+1) = e n ≫ subcategoryTruncationMap K n`; exact equality of complex morphisms, not equality in a localization or up to homotopy. |
| Each E_n bounded above | `∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)` within each n clause; exact, bounds may depend on n. |
| Every term in P | `∀ i : ℤ, P ((E n).X i)`; exact, including all negative degrees. |
| Each augmentation termwise epic | `∀ i : ℤ, Epi ((e n).f i)`; exact. |
| Each augmentation a quasi-isomorphism | `QuasiIso (e n)`; exact, all integer cohomology degrees. |
| Each transition termwise split mono | `∀ i : ℤ, IsSplitMono ((u n).f i)`; exact. `EpiMono.lean:45-59` defines this by existence of an actual retraction. |
| Every transition cokernel belongs to P | `∀ i : ℤ, P (cokernel ((u n).f i))`; exact. The node's isomorphism stability makes the chosen categorical cokernel immaterial. |

I initially questioned isomorphism stability because Stacks does not write it as a
separate phrase. On rereading, the node explicitly includes it and uses finite
biproducts; this makes the categorical convention explicit when chosen zero objects,
biproducts and cokernels replace objects specified only up to isomorphism. I made no
change to either mathematical statement. In particular, I did not remove that node
hypothesis or impose any new one.

Dependency checks: I read the two statement-dependency node records and signatures.
`CategoryTheory.Abelian` (`Abelian/Basic.lean:101-117`) supplies the intended category
structure, kernels and cokernels. `def-weil-abstract-derived-category` records
`DerivedCategory` and `HasDerivedCategory` in `DerivedCategory/Basic.lean:75-98`;
its concrete complex/cohomology notion is Mathlib's `CochainComplex` and `QuasiIso`,
not a new project-specific derived object. I read `QuasiIso.lean:65-68` for the
homology-isomorphism meaning. The present statement never forms a derived category,
so it correctly adds no `HasDerivedCategory` hypothesis. Its newly explicit public
import of `DerivedCategory.Basic` records the statement dependency without adding
such an instance to the signature.

For proof dependencies I opened their node records and the Mathlib interfaces:
`HomotopyCategory/Triangulated.lean:208` gives triangulation,
`DerivedCategory/Basic.lean:166-177` gives the triangulated localization, and
`Pretriangulated.lean:479-480` is `isIso₂_of_isIso₁₃` with both distinguished-triangle
hypotheses and the outer-component isomorphisms. The triangulated-category node's
`Pretriangulated` is the intended TR1/TR2/TR3 structure. I added the available
proof-only imports explicitly. `lem-sfb-subcategory-left-resolution` currently has
neither a Lean record nor a Mathlib match; it is a proof-only dependency, not an
object needed to type this statement, so its absent module is not invented here.
It remains named in the proof docstring for the subsequent stage.

Edge cases: the empty finite biproduct follows from `hzero`; no nonempty index family
is assumed. A zero complex is allowed and is resolved by zero complexes. `n=1` is the
first stage; `n=0` and negative stages have no asserted properties. Extending a system
on positive integers to the displayed total integer families imposes no extra content:
choose zero complexes and zero augmentations for n≤0, and zero transitions there
(including the map from stage 0 to stage 1). A complex supported in an arbitrary
negative degree is covered. There is no ring, characteristic, scheme or nonempty
scheme hypothesis to restrict. Both category universes remain arbitrary; no equality
between them, smallness, enough-projectives, enough-injectives, colimits, or boundedness
of K is assumed.

Independent H4 searches run in this reading:

- `msearch.py ... leanfinder` query: "For every complex in an abelian category choose
  bounded above resolutions of its smart truncations with split inclusions and
  epimorphic quasi-isomorphisms using an additive generating class". Eight hits, mainly
  `DerivedCategory.exists_iso_Q_obj_of_isLE` and t-structure variants; none supplies
  the compatible resolution system or the arbitrary class.
- `msearch.py ... loogle` query: `"truncLE", "map"`. Twelve hits for
  `HomologicalComplex.truncLEMap`, `truncLE'Map` and functoriality lemmas; these truncate
  a map at one fixed cutoff, not the inclusion between two cutoffs. I read their
  signatures and the existing naturality lemma used in the helper construction.
- `msearch.py ... leansearch` query: "A sequence of bounded above complexes resolving
  canonical truncations with split injective transition maps and cokernels in a given
  generating class". Eight hits: ordinary injective/projective resolution declarations,
  truncation short complexes, and monicity of truncation inclusions; no match.
- `msearch.py ... grep` query:
  `special.*(system|tower)|compatible.*resolution|resolution.*(system|tower)|truncLE.*truncLE`
  in `Algebra/Homology`. Twenty-four hits, only truncation APIs and derived fractions;
  no arbitrary-class tower statement.
- Independent `rg` searches over upstream `WeilConjectures/`, project `lean/Sheaf/`,
  `dag/nodes/`, and `dag/lean_names_upstream.json` used `specialDirect`, `cutoffMap`,
  `resolution_system`, `truncLEMap`, `compatible.*resolution`, and the item ID.
  Upstream `ResolutionByClass.lean:275-282` resolves a single bounded-above complex
  using a different lifting hypothesis, with no epic augmentation or compatible tower.
  Mathlib `Algebra/Homology/LeftResolution/Basic.lean:35-43,60-64` requires a functorial
  covering structure; `Reduced.lean` modifies it to preserve zero morphisms. Neither
  states this theorem. The project `exists_flat_truncation_tower` in
  `FlatTruncationTower.lean:61-83` is restricted to flat sheaves of modules and does not
  assert split transitions/cokernels. `SubcategoryRightResolutionSystem.lean:166-182`
  resolves one bounded-below complex into a cogenerating class, not this direct tower.
  `DoubleComplexVerticalTowerMaps.lean:73-100` has only private `cutoffMap` and
  `cutoffNatTrans`, so they cannot supply a public dependency. No usable duplicate of
  the theorem or public cutoff-to-cutoff helper was found. The helper is already listed
  in the item's `lean.declarations`, with its source/blueprint docstring and real data.

Mismatches repaired: the worker report said that proof-only dependencies were omitted
because the proof is `sorry`; this conflicts with the stage-2 import rule. I added
`DerivedCategory.Basic` as a public dependency import and
`HomotopyCategory.Triangulated` / `Triangulated.Pretriangulated` as ordinary imports.
The old compressed proof docstring did not preserve the full eight-step plan: it
omitted the separate boundedness argument for the cone, the cohomology-surjectivity
argument for the final degree, and the transition cokernel after adjoining the disk.
I replaced it by eight numbered steps with the original dependency IDs. I also supplied
the standard copyright/license header and moved the public section after the module
docstring as in the example. No declaration signature or definition body changed.
There are no hollow definitions, private definitions, local notation or local instances;
the only postponed proof is the named theorem for this DAG node.

Validation: after these edits, the prescribed `scompile.py NA
lem-sfb-subcategory-truncation-resolution-system
lean/Sheaf/Algebra/Homology/SubcategoryTruncationResolutionSystem.lean` compiled the
sandbox and library-path versions cleanly (1.0 s / 1.1 s), with no errors or warnings.
I also checked the binders by eye (`u`, `v`, `C`, `P`, `K`, and all indices bound),
verified every Lean line is at most 100 characters, and compared the extracted theorem
signature with `lean.statement` byte for byte: equal. The node record is unchanged.
