## Worker report

States `AlgebraicGeometry.Scheme.exists_lisse_open_dimension_drop` in
`Sheaf.AlgebraicGeometry.LisseOpenDimensionDrop`. Its only proof is `sorry`.
The declaration docstring contains all five steps of the current reviewed DAG proof.
No new notions or dependency modules are needed, and only the item's `lean` field changes.
The previous dispatch apparently treated this as a stage-1 split: the retained sandbox
contained only dispatcher marker files. This delivery is the missing stage-2 statement,
and does not split or alter the reviewed proof.

Read the original blueprint at
`sec-purity-real-sheaves/sk-p-real-purity/fin2-lem-lisse-dense-open.md`, order 2666,
and the current reviewed DAG node. The original proof explicitly takes U = X when X
is empty, although its displayed inequality was unconditional. The reviewed DAG has
already repaired that case. This delivery states that reviewed version verbatim in
mathematical content; it makes no further statement correction.

Hypothesis and conclusion correspondence:

| Node phrase | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| X is a scheme over k | `(X : Scheme.{u}) [X.Over (Spec (.of k))]` |
| finite type over k | `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and `[QuasiCompact (X ↘ Spec (.of k))]` |
| finite commutative ring Λ | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` |
| sheaf of Λ-modules on the small etale site | `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` |
| constructible, in the specified convention | `(hF : IsConstructibleEtaleModuleSheaf F)` |
| there exists an open subscheme U of X | `∃ U : X.Opens`; its canonical open immersion is `U.ι` |
| restriction F on U is lisse | `IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F)` |
| strict dimension drop if X is nonempty | `Nonempty X → topologicalKrullDim {x : X // x ∉ U} < topologicalKrullDim X` |
| if X is empty, choose U = X | `IsEmpty X → U = ⊤` for the same existential witness |

All binders and the universe are explicit. The coefficient universe follows the existing
small-etale module-sheaf encoding. There is no separatedness, algebraic closedness,
characteristic, nonzero-ring, nonempty-scheme, fixed-dimension, density, or prime-to-
characteristic hypothesis. Density occurs only in the proof plan, not as an additional
conclusion. The complement is a subtype with the subspace topology, exactly the dimension
convention of `def-kun-topological-krull-dimension`.

Recorded statement dependency interfaces were opened and read:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and its morphisms in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `AlgebraicGeometry.QuasiCompact`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, used as the conjunction in
  the record's note. The structure morphism is the project's accepted `X ↘ Spec (.of k)`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` is publicly imported.
  Its exported, existing `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`
  comes from `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
  Its exported `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf` comes from
  `WeilConjectures.ConstructibleSheaf.Defs`. The recorded main declaration
  `Etale.DerivedCategory.isBoundedConstructible` defines the complex clause, which
  this sheaf-level item does not use. No replacement constructibility definition is made.
  Read the actual finite-locally-constant class: it extends local constancy and
  finitely generated geometric stalks. Over the finite coefficient ring these stalks
  are finite, as required, with no constant-rank or freeness requirement.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`; `U.ι` is the canonical open immersion.
- `def-kun-topological-krull-dimension`: Mathlib `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, valued in `WithBot ℕ∞`.

The module also imports the recorded modules of all stated proof dependencies:
`LocallyClosedStratification`, `FiniteLocallyConstantModuleValues`,
`NowhereDenseDimensionDrop`, upstream `ConstructibleSheaf.Defs`,
`ConstructibleSheaf.GenericConstancy`, `Mathlib.Topology.KrullDimension` under
the upstream root, and upstream `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
The Mathlib Noetherianity leaf is supplied by `Mathlib.AlgebraicGeometry.Noetherian`.
Proof imports are non-public. No dependency is restated.

Edge cases checked before writing:

- Empty X: the last clause chooses the top open; no impossible bottom < bottom
  inequality is imposed. Local constancy and stalk finiteness are vacuous.
- Dimension zero, nonempty X: the complement must be empty (its dimension is bottom),
  consistent with constructibility on a finite zero-dimensional scheme.
- Empty complement and already-lisse F: U = top is allowed; bottom is below the
  nonnegative dimension of every nonempty finite-type X.
- Zero F and the zero coefficient ring are included; lisse means finite locally
  constant, not locally free of positive rank.
- Reducible and nonreduced schemes, components of differing dimensions, arbitrary
  fields, and positive characteristic are included. No irreducibility assumption or
  choice of a unique generic point is in the signature.

Searches actually performed through `msearch.py`, under group NC and this item:

- LeanFinder query: `A constructible etale sheaf on a scheme of finite type over a field is lisse on an open subscheme whose closed complement has smaller Krull dimension`.
  Eight hits concerned etale/unramified algebra loci; none stated the sheaf theorem.
- Loogle query: `"topologicalKrullDim", "Sheaf"`. Zero hits.
- Grep query: `IsConstructibleSheaf|IsFiniteLocallyConstantSheaf|exists_dense_open`
  in Mathlib's `AlgebraicGeometry`. Zero hits.
- LeanSearch query: `A constructible sheaf on a finite type scheme is locally constant on an open subset with smaller dimensional complement`.
  Eight hits included constant-sheaf and constructible-subset definitions and local
  sections of the structure sheaf; none stated the required result.

Additional direct source searches:

- `rg -n 'fin2-lem-lisse-dense-open'` throughout upstream `WeilConjectures`: no hits.
- `rg` for dense-open/lisse/dimension terminology in upstream `ConstructibleSheaf`
  and project `lean/Sheaf/AlgebraicGeometry`, and `topologicalKrullDim` in constructible
  sheaf modules. The upstream `Scheme.IsConstructibleSheaf.exists_dense_open` gives
  density and finite local constancy with the upstream constructibility convention;
  it does not state the dimension inequality or the explicit empty-case clause.
  Read its complete signature and proof. It is a proof dependency, not an exact
  existing declaration for this item.
- `rg` for `exists_lisse_open_dimension_drop|exists_lisse_open|lisse_open.*dim`
  in both upstream `WeilConjectures` and project `lean/Sheaf`: no naming collision.
- Read the existing finite-stalk/finite-values comparison and constructibility
  comparison modules to verify that no new notion is required.

No new statement dispute or node fault was found. The historical empty-case dispute
is already resolved by the current reviewed statement and is respected here.

Validation is through the prescribed `scompile.py` and `deliver2.py --no-push`;
the independent second reading and actual delivery remain for the second reader.

## Second reading by NC

I independently opened the reviewed node, its sandbox copy and the complete Lean
module before comparing them. I read the original blueprint item, order 2666, and
`def-weil-pbc-constructible-complexes.md` from the project's server literature copy:
the literature files are absent from this read-only local mirror. I also read the
Stacks `.tex` passages for 03RU, 03RW(3), 095E and 0055. The original item's proof
explicitly treats the empty scheme separately. The reviewed node already makes that
exception explicit, so this stage-2 delivery needs no further statement correction.
The finite-ring assumption comes from the cited coefficient definition; Stacks'
Noetherian-coefficient condition is automatic for a finite commutative ring.

Independent object, hypothesis and conclusion checklist:

| Node object or clause | Exact Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary field k | `(k : Type u) [Field k]` | Exact; no perfectness, closure or characteristic restriction. |
| Scheme X over k | `(X : Scheme.{u}) [X.Over (Spec (.of k))]` | Exact scheme and structure morphism. |
| X finite type over k | `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]` | Exact conjunction recorded by `def-weil-finite-type-morphism`; no separatedness hypothesis. |
| Finite commutative coefficient ring | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` | Exact, including the zero ring. |
| Sheaf of Λ-modules on X_et | `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` | The recorded small-etale module-sheaf category, with the same Λ. |
| F constructible in the cited convention | `(hF : IsConstructibleEtaleModuleSheaf F)` | Uses the recorded finite constructible locally closed partition and finite constant module values. |
| One open subscheme U of X | `∃ U : X.Opens` | Exact canonical representative of an open subscheme, with inclusion `U.ι`. |
| Restriction F on this U is lisse | `IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F)` | Exact inverse image in the same coefficient category; local constancy and finite geometric stalks. |
| Strict dimension drop when X is nonempty | `Nonempty X → topologicalKrullDim {x : X // x ∉ U} < topologicalKrullDim X` | Exact complement with subspace topology and chain dimension in `WithBot ℕ∞`. |
| Choose U = X when X is empty | `IsEmpty X → U = ⊤` | Exact, for the same U as both preceding clauses. |

I opened the dependency records and actual interfaces rather than relying on names.
`Scheme` is Mathlib's locally ringed-space scheme; `IsOpenImmersion` is the
open-immersion predicate for scheme morphisms, and `U.ι` is its canonical instance.
Mathlib's `LocallyOfFiniteType` and `QuasiCompact` render finite type as recorded.
`topologicalKrullDim` is the supremum of strict chains of nonempty irreducible closed
subsets, with bottom for the empty space. `BoundedConstructibleComplexes` publicly
exports the recorded `IsConstructibleEtaleModuleSheaf`; I read its definition and
its `LocallyClosedStratification`, not just the unrelated derived-complex main name.
I read upstream `IsLocallyConstantSheaf`, `IsFiniteSheaf`, and
`IsFiniteLocallyConstantSheaf`: finite generation of stalk modules is finite
cardinality over this finite ring. The delivered statement uses exactly these
recorded notions, with no private replacements. I also read the finite-values
comparison and `IsConstructibleSheaf.exists_dense_open`; the latter is a proof
dependency and lacks this item's dimension and explicit empty-case conclusion.
The proof imports include the recorded dimension, generic constancy,
stratification and finite-value comparison modules. The finite-type Noetherianity
leaf is supplied by Mathlib's Noetherian module.

Edge cases: empty X imposes no bottom < bottom comparison and chooses the top
open; empty complement and U = top are allowed. For nonempty dimension-zero X,
the strict comparison forces an empty complement, as expected. Zero F, the zero
coefficient ring, reducible or nonreduced schemes, components of unequal dimensions,
all field characteristics and finite coefficient cardinalities are included.
There is no index type or degree n in this statement; empty partitions and covers
are allowed by the dependency definitions. All variables are bound; `universe u`
is arbitrary, and the site/coefficient `u + 1` convention is the recorded interface,
not an additional mathematical size or equality hypothesis. Geometric fields in
the finite-sheaf definition use the scheme universe and supply points of every
residue characteristic. No nonemptiness assumption was accidentally added.
Density is not an extra conclusion: the node requests only lissity and the strict
complement inequality, even though its proof constructs a dense open.

My independent searches used different wording from the first reader:

- LeanFinder through `msearch.py`: `On a Noetherian scheme a constructible module
  sheaf admits a locally constant restriction outside a closed set of lower dimension`.
  Eight hits were facts about structure-sheaf restrictions and constructible subsets;
  none was this theorem.
- Loogle through `msearch.py`: `"IsFiniteLocallyConstantSheaf"`. Zero hits.
- LeanSearch through `msearch.py`: `A constructible module sheaf is a finite local
  system on an open locus with lower dimension closed complement`. Eight hits
  concerned general sheaves of modules, finite type or constructible subsets;
  none was the etale sheaf theorem.
- Grep through `msearch.py`: `lisse_open|locallyConstant.*[Dd]im|[Dd]im.*locallyConstant|constructible.*[Dd]ense`.
  Zero hits. Direct `rg` searches in Mathlib, upstream `WeilConjectures` and
  project `lean/Sheaf` found the existing constructibility/lissity interfaces and
  upstream `IsConstructibleSheaf.exists_dense_open`, whose complete signature
  I checked. None states the complete item; no declaration is duplicated.

No mathematical mismatch, missing notion, dependency repair or new node was found.
I preserved the Lean module and node record. The module has one named theorem with
`by sorry`, no definitions or additional proofs; the module and declaration
source/blueprint docstrings are present, and the theorem docstring carries all
five reviewed proof steps with their dependency ids. There are no lines over
100 characters or unbound universes. I checked that `lean.statement` equals the
file's signature verbatim, including newlines.

Validation: the prescribed `scompile.py NC fin2-lem-lisse-dense-open` compilation
of the sole delivered file succeeded without errors or warnings. The subsequent
dry run and delivery use `deliver2.py` and its current-server preflight checks.
Second reading changes only this report; the statement, module, proof plan and
node metadata remain as written.
