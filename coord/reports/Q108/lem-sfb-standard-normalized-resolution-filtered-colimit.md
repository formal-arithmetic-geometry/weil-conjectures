## Worker report

The module `Sheaf.RingTheory.StandardNormalizedResolutionFilteredColimit` states
`Algebra.StandardNormalizedResolution.filtered_colimit`. Its helpers are the canonical
adapters needed to express the very construction in this node: the algebra's ring arrow,
the standard simplicial resolution with its D-algebra structure, its strict functorial maps,
its quotient shuffle normalization, ordinary coefficient extension, and degree evaluation.
They are not independent mathematical notions or replacement resolutions. All definitions
have real data. The only postponed proof is the named theorem matching the item.

Hypotheses and clauses, read against the node:

- `universe u`, `D : Type u`, `[CommRing D]`, `S : Type u`, `[CommRing S]`, and
  `[Algebra D S]` give the rings and their homomorphism. The universe contains the index,
  both rings, and all algebra carriers; it can be enlarged as in the size convention.
  `[∀ B : CommRingCat.{u}, HasDerivedCategory.{u+1} (ModuleCat.{u} B)]` is only the
  recorded cotangent interface's localization choice, available by
  `HasDerivedCategory.standard`, not a mathematical existence restriction.
- `K : Algebra.CotangentResolution.Coherence` supplies exactly the standard resolution
  and maps of the dependency. Its `standard_spec` fixes every term, face, degeneracy,
  base map and augmentation by `IsStandard`; `standardMap_formula` fixes every map by
  `standardSquareMap`. The result holds for every such witness, so it is independent
  of the auxiliary cotangent data. Existence is the dependency's `exists_coherence`.
- `I : Type u`, `[PartialOrder I]`, `[Nonempty I]`, `[IsDirected I (· ≤ ·)]` render the
  small nonempty directed partially ordered index. `F : I ⥤ CommAlgCat.{u} D` supplies
  exactly the compatible D-algebra transition maps. There is no injectivity or flatness
  hypothesis on any of them, or on D → S.
- `c : Cocone F`, `_hc : IsColimit c` render E and its canonical maps. This allows the
  ordinary disjoint-union/eventual-equality algebra colimit specified in the node and
  any canonically identified copy. For directed algebra systems, the ordinary quotient
  presentation has precisely this universal property, and conversely the universal
  property identifies any such cocone with that presentation. This is not a derived
  or homotopy colimit.
- `standardUnder`, `standardUnderMap`, and `standard` use `K.standard` and
  `K.standardMap` directly. The equivalence `commAlgCatEquivUnder` only restores the
  already supplied D-algebra structure. In particular, B=D still has the unmodified
  `(F_D U)^(n+1) D` polynomial terms; there is no case split replacing it by constants.
- `normalized` composes with the functor from
  `exists_shuffle_normalization D`. Its existential specification determines it by
  the quotient maps and term identifications with the existing `quotient D P n`,
  naturality, the stated shuffle product, and the unit. The choice is therefore a
  choice of a specified construction up to its canonical natural isomorphism, not
  data chosen from an unconstrained existence theorem. No normalization is redefined.
- `coefficients` is ordinary `ModuleCat.extendScalars` on the normalization, lifted to
  cochain complexes by `mapHomologicalComplex` and to algebra objects by `mapMon`.
  Its terms are ordinary `S ⊗_D R_B^m`, its differential is `id_S ⊗ d`, and its product
  is induced by `(s ⊗ x)(t ⊗ y) = st ⊗ (x shuffle y)`. The monoidal scalar-extension
  structure supplies precisely this product and the unit. `Mon` in cochain complexes
  is the same associative unital dg-algebra encoding used in the recorded dg-category
  dependency; no dg law is replaced by an extra assumption.
- `ULift D` and `ULift S` are the normalization dependency's canonical scalar copies.
  The scalar map in `coefficients` is the original algebra map conjugated by
  `ULift.ringEquiv`. These are ring isomorphisms, so this is the same dg S-algebra,
  in the normalization node's size convention. `degree` explicitly restricts along
  the original map D → S followed by S → ULift S, retaining the underlying D-modules.
- The first conjunct says that the canonical coefficient cocone is a colimit of dg
  S-algebras. The second says, for every `m : ℤ`, that its actual D-module cocone is
  a colimit. Thus its colimit is degreewise, with the actual dg multiplication induced
  from the stages. The third conjunct gives an isomorphism from any supplied colimit
  cocone `l`, with its forward arrow *equal* to `hl.desc` of the functorial cocone.
  This is the specific comparison map, not the existence of an unspecified isomorphism.
- The fourth conjunct takes `n : ℕ`, `d : Fin n → ℤ`, and a family `x` of elements in
  exactly those degrees. It returns one stage `i` and elements `y` in the same degrees
  mapping to `x`. Every finite collection is enumerated this way, including n=0.
- The last conjunct takes arbitrary pairs `x a`, `y a` in the same specified degree
  at one stage `i`. If their limit images are equal, it returns one `j ≥ i` where all
  equalities hold. This is equivalent to the finite-expression clause: evaluate each
  left/right expression at i and use these values for x/y. Algebra chain maps are
  additive and linear and preserve multiplication, unit and differential; consequently
  they preserve signs and every specified S-scalar as well. Conversely, an equation
  between two arbitrary homogeneous elements is one of the permitted expressions.
  No expression class, degree, operation, or scalar case is omitted.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  the recorded API is `Algebra.CotangentResolution.Augmentation`, `AugmentedMap`,
  `Coherence.standard`,
  `Coherence.standardMap`, `Coherence.standard_spec`, `Coherence.standardMap_formula`,
  `Coherence.standardMap_id`, `Coherence.standardMap_comp`, and `exists_coherence`.
  The dependency's real `standardTerm`, `standardBase`, `standardAugmentation`,
  `standardFace`, `standardDegeneracy`, `standardSquareMap`, and `IsStandard` were read.
- `Sheaf.AlgebraicTopology.SimplicialAlgebraShuffleNormalization`:
  `AlgebraicTopology.SimplicialAlgebraShuffleNormalization.exists_shuffle_normalization`;
  its signatures of `modules`, `chains`, `degenerates`, `quotient`, `shuffle`, `mul`,
  `unit`, constants and augmentation comparisons were read in full.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`:
  `TensorProduct`, `TensorProduct.lift`, `TensorProduct.ext'`, `LinearMap.lTensor`,
  `LinearMap.rTensor`; coefficient extension uses this ordinary tensor product.
- The size convention has no declaration; explicit universe binders implement it.
- Proof-only imports retain the recorded plan: `CommAlgCat.filtered_colimit_algebras_underlying_module`
  from `WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule`,
  `TensorProduct.exists_unique_colimit_tensor_varying_rings` from
  `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`, and the Mathlib module-colimit
  representatives/equality/criterion interfaces from `ModuleCat.FilteredColimits` and
  `CategoryTheory.Limits.ConcreteCategory.Basic`. The polynomial and quotient-normalization
  dependencies are already public imports. No import cycle is introduced.

Edge cases checked before writing: empty finite collections and empty lists of equations;
singleton directed index; n=0 normalization (no degeneracy relations); positive cochain
degrees (zero); arbitrary negative degrees; zero D, S, or E; zero normalized modules;
noninjective transition maps and nonflat scalar extension. No `Nontrivial`, flatness,
injectivity, finite-generation, or positive-degree assumption occurs. In the equality
clause the later-stage relation also covers no equations, by taking j=i. The coefficient
construction has no branch treating the base algebra specially.

Searches on 2026-10-24:

- `msearch.py ... leanfinder "Shuffle normalization of standard polynomial resolutions
  commutes with filtered colimits after tensoring with a fixed algebra"`: eight hits
  on algebra presentations and polynomial tensor models; no matching statement.
- `msearch.py ... loogle '"SimplicialObject", "colimit"'`: eight simplicial/cosimplicial
  colimit existence and splitting hits; no normalization/coefficient comparison.
- `msearch.py ... grep 'standardResolution|shuffle.*colimit|normaliz.*filtered'`: five
  hits, all representation-theoretic standard resolutions, not the algebra resolution.
- `msearch.py ... leansearch "Normalized standard polynomial resolutions of algebras
  preserve directed colimits"`: eight ordinary directed-limit/polynomial hits;
  no quotient shuffle dg comparison or finite equation statement.
- `rg` with the same regular expression in both `lean/WeilConjectures` and `lean/Sheaf`:
  unrelated filtered complex and geometric normalization matches, no matching theorem.
  `grep -rn` for the item id in `lean/WeilConjectures` had no hits.

The source read was the current blueprint `literature/blueprint/latest/` and Stacks
`cotangent.tex` definition-standard-resolution and lemma-colimit-cotangent-complex,
plus `simplicial.tex` lemma-decompose-associated-complexes. The node explicitly labels
its extra dg and finite-equation conclusions as an agent refinement, retained here.
No statement correction, disputed statement, new node or dependency repair is needed.

Validation: `scompile.py Q108 lem-sfb-standard-normalized-resolution-filtered-colimit`
compiled the final module cleanly, both as a sandbox file (11.7 s) and under its library
module name (9.9 s). No errors or warnings remained. All variables and universes are
explicitly bound, with `autoImplicit false`. Independent review is performed by the maintainer;
no second worker reading is claimed.

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
