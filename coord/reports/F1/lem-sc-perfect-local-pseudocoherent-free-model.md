## Worker report

Module `Sheaf.RingTheory.MinimalFreeModel` states
`DerivedCategory.exists_unique_minimalFreeModel`, with only `sorry` as its proof.
Source: Stacks Project, More on Algebra, Tag 0BCC,
https://stacks.math.columbia.edu/tag/0BCC (currently numbered Lemma 15.77.6;
the node uses the older 15.75.7 numbering). The source statement and proof were opened.

Hypotheses and clauses, individually:

- Local ring `(R, m, κ)`: `{R : Type u} [CommRing R] [IsLocalRing R]`;
  `m` is `IsLocalRing.maximalIdeal R`, `κ` is `IsLocalRing.ResidueField R`,
  with quotient map `IsLocalRing.residue R`. Commutativity is the Stacks convention.
- `K ∈ D(R)`: `K : DerivedCategory (ModuleCat.{max u v} R)`, with the explicitly
  chosen `[HasDerivedCategory.{w} ...]` as the usual localization size convention.
- Pseudo-coherence, exactly the bounded-above finite-free representative condition:
  `hK : IsPseudoCoherent K` uses the existing ring definition. This is not a new predicate.
- `d_i = dim_κ H^i(K ⊗ᴸ_R κ)`: `d : ℤ → ℕ` and `hd`. The complex
  `Classical.choose hK` is the finite-free bounded-above representative provided by the
  existing predicate. `Functor.mapHomologicalComplex (ModuleCat.extendScalars
  (IsLocalRing.residue R)) (ComplexShape.up ℤ)` takes its termwise tensor with κ.
  Such a representative is K-flat, so the displayed `.homology i` is precisely
  the cohomology of the derived residue tensor. It does not depend on the chosen
  representative up to isomorphism. `Module.finrank κ` renders its finite dimension.
  Binding `d` with equality `hd` is the explicit Lean rendition of 'Put d_i = ...'.
- Finiteness of every `d_i`: `hfinite` requires `Module.Finite κ` of every displayed
  cohomology module. This is essential: finrank alone is zero on infinite-dimensional
  spaces. Thus no infinite-dimensional case is inadvertently admitted.
- Vanishing in sufficiently large degrees: `hbound : ∃ b : ℤ, ∀ i, b < i → d i = 0`.
  Both finiteness and vanishing are explicit hypotheses as in this node, although
  the source also explains that they follow from pseudo-coherence.
- Represented by a bounded-above complex: `∃ F : CochainComplex ... ℤ`,
  `(∃ b : ℤ, F.IsStrictlyLE b)` and `Nonempty (Q.obj F ≅ K)`.
- Finite free terms of the specified ranks in EACH degree:
  `∀ i, Nonempty (F.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))`.
  The finite product equals the finite direct sum; ULift only accommodates the
  arbitrary module universe and does not alter the R-module. These termwise
  isomorphisms encode the notation R^(d_i), without extra chosen bases.
- Unique up to isomorphism of COMPLEXES: for every other `G`, with bounded-above
  support, image isomorphic to K, and the same term ranks, `Nonempty (F ≅ G)`.
  This is an isomorphism in the cochain-complex category, not just in D(R).

Dependency declarations used and read with their full signatures/docstrings:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `DerivedCategory.Q`,
  in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, available via
  `Sheaf.RingTheory.RingPseudoCoherent`'s imports.
- `def-pc-ring-pseudo-coherent-complex`: `DerivedCategory.IsPseudoCoherent`,
  `Sheaf.RingTheory.RingPseudoCoherent`; definition read in full, including all
  existential bounds, termwise Module.Free/Module.Finite, and the Q-object isomorphism.
- The old dependency `AlgebraicGeometry.schemeDerivedCategory` and its docstring
  in `Sheaf.AlgebraicGeometry.DerivedCategory` were read; it is for sheaves on schemes
  and is inapplicable here. The citation correction below removes it.
- Mathlib's `ModuleCat.extendScalars` and `HomologicalComplex.homology`, and the
  residue field and quotient-map declarations were read directly in their sources.

Edge cases checked before writing: the zero derived object has all d_i = 0 and the
zero model; individual zero ranks admit zero terms via `Fin 0 → R`; no lower degree
bound is imposed (a genuinely unbounded-below pseudo-coherent object is included).
A field R is allowed, with κ canonically its residue field. No Noetherian hypothesis,
positive-rank hypothesis or boundedness-below condition is imposed. A zero ring is
not a local ring in Mathlib's proper-maximal-ideal convention, matching Stacks.
Universes u, v, w are explicit, and ULift makes the free term available in max u v.

Searches for an existing statement/notion:

- msearch LeanSearch, query 'minimal finite free complex over a local ring':
  service unavailable (Internal Server Error), recorded in searches.jsonl.
- msearch LeanFinder, query 'A pseudo-coherent complex over a local ring admits a
  unique bounded above finite free minimal complex with ranks given by residue field
  cohomology': eight general projective/injective-resolution and derived-category
  hits, including CochainComplex.IsKProjective, no minimal free model statement.
- msearch Loogle, query 'ModuleCat.baseChange': unknown identifier, zero hits;
  the source search identified Mathlib's actual name ModuleCat.extendScalars.
- msearch grep, query 'pseudo[Cc]oherent|minimal.*[Cc]omplex|derivedTensor': no Mathlib hits.
- rg over WeilConjectures for pseudoCoherent/PseudoCoherent/derivedTensor/minimal
  complexes found the site's derived tensor constructions, not the local-ring lemma.
  rg for minimal complexes/finite free models/local pseudo-coherence found no relevant
  statement; node-id search found no source declaration for this item.
- rg over lean/Sheaf found the landed `RingPseudoCoherent` predicate and the module
  derived-tensor machinery, but no minimal free model theorem. The predicate is reused.
- DAG search found the existing ring pseudo-coherence node, so no new definition node
  or duplicate predicate is needed. The upstream names index was also searched.

Validation: server scompile passed with no errors and no warnings. All binders and
universes are explicit. The theorem docstring carries the four proof steps and names
all proof dependencies. Nothing is proved in this stage. No STATEMENT-DISPUTED fault.

## Statement corrected

Old statement, verbatim:

Let $(R,\mathfrak m,\kappa)$ be a local ring and let $K\in D(R)$ [def-pc-derived-category] be pseudo-coherent, that is, isomorphic in $D(R)$ to a bounded-above complex of finite free $R$-modules. Put $d_i=\dim_\kappa H^i(K\otimes_R^{\mathbf L}\kappa)$. If the $d_i$ are finite and vanish for all sufficiently large $i$, then $K$ is represented by a bounded-above complex of finite free $R$-modules whose term in degree $i$ is $R^{\oplus d_i}$. Such a complex is unique up to isomorphism of complexes.

The citation to `def-pc-derived-category` supplies D(O_X) for a scheme, not D(R)
for ordinary modules, so it cannot type the objects used here. Following Stacks
Tag 0BCC, replace this citation by `def-weil-abstract-derived-category` and cite
`def-pc-ring-pseudo-coherent-complex` for the already explicit pseudo-coherence
condition. Only citation/dependency bookkeeping changes; every mathematical
hypothesis and conclusion remains verbatim. This helper is not a unit statement.

Citers (every stmt_deps/proof_deps occurrence was checked):

- `lem-sc-perfect-finite-free-residue-model`: holds true. The local-ring minimal finite free model is unchanged; replacing the scheme-derived-category citation by the abstract module derived category preserves the application after localizing at the point.

## Second reading by F1

I read the corrected node, its Stacks source (More on Algebra, Tag 0BCC), and
`Sheaf.RingTheory.MinimalFreeModel` item by item. The local-ring objects are rendered
by `{R : Type u} [CommRing R] [IsLocalRing R]`, with residue field
`IsLocalRing.ResidueField R`; the derived object is
`K : DerivedCategory (ModuleCat.{max u v} R)` with the explicit
`HasDerivedCategory` instance. Pseudo-coherence is exactly the existing
`DerivedCategory.IsPseudoCoherent K`. The definition of `d_i` is rendered by `d` and
`hd`, using termwise `ModuleCat.extendScalars (IsLocalRing.residue R)` and homology of
the chosen bounded-above finite-free representative. Finiteness is rendered by
`hfinite`, and eventual vanishing by `hbound`. The conclusion has a bounded-above
complex `F`, an isomorphism `Q.obj F ≅ K`, termwise isomorphisms to
`ModuleCat.of R (ULift (Fin (d i) → R))`, and uniqueness against every bounded-above
`G` with the same representation and ranks. All quantifiers and conjunctions match
the node's clauses; no stronger ring, finiteness, Noetherian, or bounded-below
hypothesis is present.

Edge cases checked: the zero object and zero ranks are represented using `Fin 0`; a
field is allowed; complexes may be unbounded below; no positive rank or characteristic
assumption is introduced; universes `u`, `v`, and `w` are explicit. The empty index
case is vacuous because the degree index is `ℤ`, and the local-ring convention excludes
the zero ring as in the source.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` for minimal finite-free models,
pseudo-coherent residue lifting, and derived tensor formulations, and ran LeanSearch,
LeanFinder, and Loogle queries recorded in `searches.jsonl`; no existing declaration
states this result. The only mismatch was the dependency citation: the old
`def-pc-derived-category` denotes sheaf modules on a scheme, while this node concerns
ordinary `R`-modules. The node was corrected to cite
`def-weil-abstract-derived-category` and `def-pc-ring-pseudo-coherent-complex`; the
Lean module already uses those meanings and required no code change. The corrected
citer `lem-sc-perfect-finite-free-residue-model` still holds. `scompile.py` completed
with no errors or warnings beyond the permitted `sorry` declaration warning.
