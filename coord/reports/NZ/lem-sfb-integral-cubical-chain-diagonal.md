## Worker report

The delivery states `IntegralLatticeCubical.diagonal` in
`Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal`. It gives a chain map whose
components are the explicitly constructed signed partition sums, together with
translation equivariance, the two counit identities, the double augmentation identity
as a chain-map equality, and the rank-zero normalization. The proof is `sorry`.
No mathematical statement, split, proof, dependency list or review field is changed.
The bundling helpers are in this item's module; the live dependency record is byte-identical.

The previous worker's blocking description concerns the already completed stage-1
split. I read the NP report and independent PASS review and have preserved that split.
The live item has no Lean binding, so this is its stage-2 statement delivery.

Hypotheses and clauses, in statement order:

- The only parameter is `r : ℕ`, exactly an integer rank at least zero, including zero.
  The lattice is the dependency's `Fin r → ℤ`. Its standard basis is the dependency's
  `unitVector r`. `Fin r` orders the coordinates from zero rather than one; this is
  merely the order-preserving reindexing of the ordered standard basis.
- The chains are exactly the dependency's `Chains r a`, finitely supported integral
  coefficients on `(v,I)` with `I : Directions r a`. These definitions, including
  `cell`, `boundary`, `incomingBoundary`, `augmentation` and `translate`, are imported
  unchanged. There is no second definition of the cubical cells or differential.
- `chainComplex r` bundles these existing terms in nonnegative degrees, with incoming
  boundary `incomingBoundary r n`. A Mathlib nonnegative chain complex has its usual
  zero extension in negative degrees. This loses no integer degree in this node:
  the dependency's negative-degree modules have empty bases and are zero, its boundary
  from degree zero has zero target, and tensor terms of a negative degree have a zero
  factor. Above degree `r`, `Directions` is empty as well. No truncation of a nonzero
  term or differential is made. This is the finite/nonnegative presentation explicitly
  allowed in `def-weil-pbc-module-chain-complex-homology`.
- `augmentationMap r` is the unique chain map to `ℤ[0]` whose degree-zero component
  is exactly `augmentation r`; its other components are zero by the single-complex
  constructor. Thus every vertex goes to one, independently of its lattice point.
- `HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)` is Mathlib's
  total tensor chain complex, over `ModuleCat ℤ`. Its summands are actual tensor
  products of modules with degrees `a+b=n`, not free pairs serving as a substitute
  for a tensor product. `ComplexShape.TensorSigns (down ℕ)` uses `(-1)^a`, with
  sign one on the first-factor boundary, exactly the stipulated differential.
- `directionSum r A := ∑ i ∈ A, unitVector r i` is precisely `u_A`.
- `partitionSign r A C := (-1)^((A.product C).filter (fun p => p.2 < p.1)).card`
  counts exactly the ordered pairs `(a,c)` with `c<a`. It counts all inversions,
  not just consecutive ones or positions of an individual removed coordinate.
- `tensorCell r n v w A C` is the canonical inclusion of
  `cell r |A| v A ⊗ cell r |C| w C` into total degree `n`. The standard
  `ιMapBifunctorOrZero` gives zero for an incompatible total degree. In every
  diagonal summand this zero branch is impossible: `A ∈ I.powerset` implies
  `|A| + |I \ A| = |I| = n`.
- `diagonalComponent r n` is `Finsupp.linearCombination` of the prescribed images
  of the existing free basis. Its sum runs through `A ∈ I.powerset`, with
  `C = I \ A`. This enumerates each ordered disjoint partition exactly once.
  The right basepoint is exactly `v + directionSum r A`; the left one is `v`.
  The sign, direction sets, translation, and coefficient ring are all as displayed
  in the node, without divisions or rational coefficients.
- The theorem quantifies `∃ Δ : chainComplex r ⟶ tensorObj ...` and fixes
  `(Δ.f n).hom = diagonalComponent r n` in every degree. Therefore it asserts
  that the constructed graded map is a chain map. This is not a hypothesis of
  an arbitrary diagonal or a `Nonempty` choice of unrelated maps: all components
  are fixed by an actual linear construction. Equality of the components also
  uniquely determines the chain map.
- Equivariance is the chain-map equality `translationMap r w ≫ Δ =
  Δ ≫ tensorHom (translationMap r w) (translationMap r w)`, for every lattice
  vector `w`. This is the diagonal translation action on both tensor factors.
- The first counit clause composes `Δ` with `tensorHom (augmentationMap r) (𝟙 _)`
  and Mathlib's `leftUnitor.hom`, and equates this composite with `𝟙 _`.
- The second counit clause composes `Δ` with `tensorHom (𝟙 _) (augmentationMap r)`
  and `rightUnitor.hom`, and likewise equates this composite with `𝟙 _`.
- The double augmentation clause uses `tensorHom (augmentationMap r)
  (augmentationMap r)` followed by `leftUnitor` at the tensor unit. Its equality
  with `augmentationMap r` is in the category of chain complexes, not just in
  homology or in degree zero. The tensor unit is definitionally the integers
  in degree zero, so these are the canonical unit identifications in the node.
- The last clause, under `r=0`, says that the image of the unique origin vertex
  is `tensorCell r 0 0 0 ∅ ∅`. The dependency's rank-zero augmentation equivalence
  identifies this vertex with `1`, and the tensor summand with `1 ⊗ 1`.

Dependency declarations used:

- `lem-sfb-integral-lattice-cubical-contraction`: all the existing
  `IntegralLatticeCubical` declarations listed above, and `contraction`, from
  `Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction`. The
  bundling helpers in this item's module supply `chainComplex`, `augmentationMap`,
  `translationMap` and their named proof obligations. The existing contraction module
  and NM's primary `contraction` record are preserved verbatim.
- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`, publicly imported by the original
  contraction module. The actual linear extension is Mathlib's
  `Finsupp.linearCombination`, imported there as well.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `LinearMap.rTensor`, and the module
  category tensor structure. The monoidal closed module imports the tensor API.
  I read the recorded quotient construction, universal property, and module
  tensor-functor implementations; no dependency repair is needed for that leaf.
- `def-weil-pbc-module-chain-complex-homology`: `ChainComplex`,
  `HomologicalComplex.Hom`, and the recorded `HomologicalComplex.homology`, in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, already publicly
  imported by the contraction. This node uses the chain-complex and morphism
  parts of that definition, not homology as a replacement for chain-map equality.

Edge cases checked before the statement was written:

- `r=0`: the lattice and degree-zero basis are singletons, there is exactly one
  empty partition, its sign is one, both counits send the sole term to the vertex,
  and no positive-degree terms remain.
- `I=∅` at any vertex: `A=C=∅`, the displacement is zero and the sign is one;
  hence `Δ[v,∅]=[v,∅]⊗[v,∅]` and the differential vanishes.
- A single direction: the two terms are `[v,∅]⊗[v,{i}]` and
  `[v,{i}]⊗[v+u_i,∅]`; taking the boundary gives the difference of the two
  diagonal vertices after cancelling the middle terms.
- A square: the mixed term with the larger direction in `A` and smaller in `C`
  has sign minus one, including the tensor boundary sign. This matches the
  inversion convention in the literal node and its independently reviewed split.
- Empty parts: left augmentation retains exactly `A=∅`; right augmentation
  retains exactly `C=∅`, even though the surviving right vertex is `v+u_I`.
  The augmentation of that vertex is still one.
- Top degree and out-of-range degrees: no term is discarded in degree `r`;
  above it and in negative degrees the source is zero. Positive-degree double
  augmentation vanishes because one partition part is nonempty.
- Lattice coordinates may be negative; the definitions sum basis vectors and
  translate by arbitrary integral functions, with no positivity assumption.
- All types here are the explicitly small lattice and its finite subsets; there
  is no independent universe parameter or index-size restriction on a coefficient
  ring, site, or category. The coefficient ring is exactly `ℤ` as in the node.

Searches performed for this stage-2 delivery:

- `msearch.py ... leanfinder`: “The integral cubical chains of an integer lattice
  have a counital translation equivariant chain diagonal given by signed partitions
  of the coordinate directions”. Eight hits: box-integral partitions, Dold–Kan
  summands/homotopies, and `Rep.standardComplex.d_of`. None has the cubical cells,
  signed arbitrary partitions, and two strict counits of this statement.
- `msearch.py ... loogle`: `"ChainComplex", "diagonal"`: zero hits.
- `msearch.py ... grep`:
  `(cubical|Koszul|koszul).*(diagonal|coalgebra)|(diagonal|coalgebra).*(cubical|Koszul|koszul)`:
  zero hits in Mathlib.
- `rg` in both project roots for cubical diagonals, counital maps, and the
  `IntegralLatticeCubical` namespace found the existing contraction module, but no
  diagonal or bundled cubical complex. The unrelated counital algebra and
  comonad material does not concern cubical chain maps. Exact blueprint-tag search
  in `lean/WeilConjectures` found no declaration for this item.
- Exact namespace/name search in Mathlib, both project roots and the upstream
  declaration-name index found none of the newly introduced full names. The
  NP stage-1 report also documents its independent DAG nonduplication search.

I read the full six-step proof, the independent NP PASS, every dependency statement
and recorded interface, the actual source declarations and docstrings, the current
blueprint paragraph (3), and Mathlib's actual tensor differential/unit/sign and
single-complex interfaces. The source honestly labels this finite computation
agent-written and its exact external reference WANTED; this delivery does not
attribute the arithmetic formula to the blueprint or to an external theorem.
No STATEMENT-DISPUTED flag or statement correction is needed.

Validation of the returned packet: the required initial `deliver2.py --no-push`
passed preflight and compilation, but retained the independently reported H13 defect.
The repaired module compiled cleanly with `scompile.py` in both its sandbox and
library-name checks (3.2 s and 3.5 s). No errors or warnings were emitted. The final
packet is checked and delivered using `deliver2.py`.

## Repair of H13

The return on immutable head c08bbaa6557b identified that the previous packet
replaced NM's contraction theorem record by a definition-only adapter record. Following
the first correction offered in the return, the adapter module is deleted and its six
declarations (`chainComplex_square`, `chainComplex`, `augmentationMap_condition`,
`augmentationMap`, `translationMap_condition`, `translationMap`) are moved unchanged,
including their docstrings, into `IntegralCubicalChainDiagonal.lean`. That module now
imports `IntegralLatticeCubicalContraction` and `Mathlib.Algebra.Homology.Single` directly.
The helper declarations are listed in the item's `lean.declarations`.

The sandbox dependency JSON is restored byte-for-byte from the live dependency JSON;
therefore no dependency node or dependency module is changed in the delivery. NM's
module, primary declaration, signature, file and `reviewed_lean` all remain intact.
The diagonal theorem and its formula helpers are unchanged from the returned packet;
this repair changes only their packaging. The item's non-`lean` fields are unchanged.
The item's recorded primary signature is refreshed verbatim from the file.

Every definition retains real data. The three postponed transport obligations remain
named theorems with the dependency's matching square-zero, augmentation-boundary and
translation-boundary clauses and complete proof docstrings. The diagonal theorem is
the fourth postponed theorem. `autoImplicit` is false and all lines are at most 100
characters. No new nodes, statement correction, or dependency-record repair is made.

Final dry run: `deliver2.py --no-push` returned OK for fc3617beb49. Its staged
paths were exactly the item module, item node and report; no dependency path was staged.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
