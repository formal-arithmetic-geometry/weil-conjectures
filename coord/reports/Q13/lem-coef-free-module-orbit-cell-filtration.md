## Worker report

The module `Sheaf.AlgebraicTopology.FreeModuleOrbitCellFiltration` states
`SSet.free_module_orbit_cell_filtration`, with its single proof `sorry`.
The two helper definitions have real data: `freeCellOrbitMap` is exactly
`(r,m,θ) ↦ m · θ*σᵣ`; `freeModuleBoundaryCell` applies the existing upstream
`CategoryTheory.Mod.free` to Mathlib's boundary inclusion. There are no other
postponed statements, new definition nodes, or dependency repairs. The item's
natural statement, statement dependencies, proof, and proof dependencies are unchanged.

Clause-by-clause rendering:

- Simplicial monoid M: `(M : SSet.{u}) [MonObj M]`, using Mathlib's monoid object
  in the cartesian monoidal category of simplicial sets. A left simplicial
  M-module is `CategoryTheory.Mod SSet M`; its maps are equivariant simplicial maps.
- The ordinal interval `0 ≤ α ≤ λ` is represented by the bounded small well-order
  `J : Type u` with `LinearOrder`, `OrderBot`, `OrderTop`, `SuccOrder`, and
  `WellFoundedLT`. Every small closed ordinal interval has this form, and every
  such J has a successor ordinal as its order type. `⊥` represents zero,
  `⊤` represents λ, and `Order.succ` represents α+1 away from the maximum.
  In particular a one-element J includes λ=0. This is an order-isomorphic
  encoding of the given ordinal interval, without a finiteness restriction.
- X is the module `X`; the stages are `F : J ⥤ Mod SSet M`, and their
  inclusions into X are `ι : F ⟶ (Functor.const J).obj X`. The named A is
  exactly the bottom module `F.obj ⊥`, whose inclusion is `ι.app ⊥`.
  `hmono` requires all these inclusions to be injective in every degree.
  Thus their images are actual M-stable simplicial subsets of X. Functoriality
  and naturality of ι say these subsets are increasing and all transition
  maps are their inclusions. This is equivalent to choosing actual subsets;
  there is no extra action or arbitrary replacement of a canonical map.
- `X_λ=X` is `htop : IsIso (ι.app ⊤)`, expressing that the last submodule
  is the whole target. This retains the specified inclusion into X.
- The union at every nonzero limit stage is `hcont`: each degree-k simplex
  at a limit j is the image of a simplex at some i<j. The other direction
  of the equality follows from the given inclusions. `Order.IsSuccLimit`
  excludes zero, as the ordinary limit-ordinal continuity convention does.
- The small set of cell generators is `R j : Type u`; `n j r` is its
  dimension and `σ j r` its simplex in `F.obj (Order.succ j)`. The unused
  data at the maximal j impose no condition; any family on α<λ extends
  to J by an empty family at its maximum.
- `hfaces` says that the image of σ under every nonsurjective simplex operator
  is in the range of the preceding-stage inclusion. This is equivalent to
  every proper face being old: any nonsurjective operator factors through a
  proper face, and old stages are simplicial subsets. It also handles higher
  degenerate simplices in the boundary.
- In each degree k, `freeCellOrbitMap (n j) (σ j) k` has precisely the displayed
  sigma-type domain: a generator r, a monoid k-simplex, and a surjective
  order-preserving θ:[k]→[n j r]. `horbit` requires injectivity and range
  equal to the complement of the old-stage range. This simultaneously gives
  well-definedness outside the old stage and bijectivity onto every new simplex,
  including degenerate ones. No nondegeneracy or freeness hypothesis has been
  silently substituted. Injectivity also forbids duplicate generator simplices
  in the same dimension, so an indexed small family here represents the stated set.
- The first conclusion quantifies over all nonmaximal j. Its coproducts are in
  `Mod SSet M`, and `Limits.Sigma.map` is exactly the coproduct of free boundary
  inclusions. The two maps a and b form the `IsPushout` square in that same
  category. The equation for every coproduct injection pins b down to
  `Mod.freeDesc M (SSet.yonedaEquiv.symm (σ j r))`. The upstream free-desc formula
  is multiplication after the Yoneda characteristic map, hence exactly
  `(m,τ) ↦ m · τ*σ`. The pushout's commutative-square equation pins a down to
  its boundary restriction in the old submodule; injectivity of the stage
  inclusion makes this factorization unique. Thus the attaching map is the
  one induced by faces, not an arbitrary attaching map whose pushout merely exists.
- The second conclusion provides a `RelativeCellComplex` with exactly these free
  boundary cells, for `ι.app ⊥ : A ⟶ X`. The equalities `c.F = F` and
  `HEq c.incl ι` retain the original filtration and inclusions. Mathlib's structure
  includes continuity at limits, the bottom identification, the colimit X,
  and pushouts of small coproducts at successors. This is precisely the node's
  small relative projective cell complex, with no retract closure added.
- The last implication assumes `IsInitial (F.obj ⊥)`, the empty simplicial
  module, and records the same relative cell complex from that empty source.
  The node defines a cellular weight for the one-object simplicial category
  with endomorphism monoid M by exactly this condition; no second enriched
  category or extra cofibrancy property is being chosen.

Dependencies read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Its recorded `SSet`,
  `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, and `SSet.Finite`
  declarations were read in their Basic, Degenerate, Subcomplex, and Finite modules.
  Here SSet and its maps provide all simplices/operators; the boundary is the
  existing `SSet.boundary` in `Mathlib.AlgebraicTopology.SimplicialSet.Boundary`.
- `def-coef-coherent-monad-modules`: imported
  `Sheaf.CategoryTheory.CoherentMonadModules`; read the full published source
  with `scompile.py --source`. Its `SSet.Enhanced.CoherentMonad`, action law,
  and ordinal-sum action conventions use simplicial maps and cartesian tensor.
  The general monoid/module structures are the existing Mathlib `MonObj`,
  `ModObj`, and `Mod`, rather than a copy of those notions or a specialization
  to the walking monad.
- Existing upstream module
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`: read its complete
  current source using `scompile.py --source`, especially `Mod.freeModObj`,
  `Mod.free`, `Mod.freeDesc`, and `Mod.freeForgetAdjunction`. The free-module
  construction and characteristic maps use these exact declarations. Their
  signatures have no abelian-category hypothesis in the Free section.
- That upstream module imports `Mod.Limits`; its current source was read too.
  It creates the needed module colimits from simplicial-set colimits; no
  extra colimit-existence hypothesis is imposed on M or X.
- `HomotopicalAlgebra.RelativeCellComplex` and `AttachCells` in Mathlib's
  RelativeCellComplex Basic/AttachCells modules, together with
  `CategoryTheory.TransfiniteCompositionOfShape`, provide the literal continuous
  transfinite composition and successor cell-pushout conditions.

Source check: opened the linked Riehl--Verity paper and read Proposition 5.3.3
and its proof, pp. 862--864, together with Lemma 6.1.8 and the action convention
in Observation 6.1.3. These identify free representable boundary cells and
continuous composites in the one-object case. The node's own five-step
quotient/orbit proof is preserved, in full natural language, in the theorem docstring.

Edge cases checked mathematically: λ=0 (J singleton: no successor hypotheses,
identity-type relative composite); empty R_j (no new simplices and an isomorphism
stage); dimension zero (empty boundary and unconstrained new vertex orbits);
empty A and empty X; limit λ (the top-stage union is included in hcont);
unbounded generator dimensions and arbitrary small sets of cells; genuinely
simplicial monoids with nonconstant simplices. No characteristic, Kan,
nondegeneracy, finiteness, cancellation, or discrete-monoid assumption occurs.
All universe and object variables are explicit; `autoImplicit` is false.

Searches (2026-10-17):

- `msearch.py leanfinder`: "A free simplicial monoid module with new simplices
  freely indexed by surjections has a boundary cell pushout filtration".
  Eight results: generic boundary cofibrations, subcomplex multicoequalizers,
  Cech conerves, and simplicial-set colimits; no orbit criterion.
- `msearch.py loogle`: "CategoryTheory.Mod, CategoryTheory.ModObj,
  HomotopicalAlgebra.RelativeCellComplex". Zero results.
- `msearch.py grep`: "freeModule|ModObj|orbit.*cell" in AlgebraicTopology.
  Zero results.
- `msearch.py leansearch`: "A degreewise free orbit decomposition of a simplicial
  monoid action gives a relative projective cell complex". Eight results:
  generic RelativeCellComplex declarations, simplicial cofibrations,
  epi-mono factorization, and a group-action orbit equivalence; no match.
- `msearch.py loogle`: "CategoryTheory.Mod.free". No match in Mathlib (unknown
  identifier); found and read the exact published upstream declaration instead.
- `rg` in Mathlib CategoryTheory/Monoidal and AlgebraicTopology, the upstream
  WeilConjectures tree, and `lean/Sheaf`, by the monoid/module/orbit/cell names:
  Mathlib has MonObj and ModObj/Mod; the published WalkingModuleWeightCells
  module uses Mod.free, which led to the upstream construction. Its theorem
  is a downstream special application of the present criterion, not this lemma.
  It is deliberately not imported, avoiding a dependency on the consumer.
- Literal node-id grep in upstream WeilConjectures and name checks in
  `dag/lean_names_upstream.json`: no existing criterion. The proposed three
  declaration names have no match in upstream/Mathlib or another project module.

Validation: the final mathematical signature compiled cleanly with scompile.py,
including both its sandbox name and actual module path. Required deliver2.py
dry-run preflight passed (d326fd9248), with exactly the module, node, and report
in the staged packet. No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
