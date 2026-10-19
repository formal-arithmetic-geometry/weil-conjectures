## Worker report

The module `Sheaf.Algebra.Homology.TopDegreeTensor` states
`CochainComplex.exists_topDegreeTensorIso`. Its only theorem has proof `sorry`;
there are no new definitions, auxiliary postponed theorems, or node corrections.

Hypothesis and conclusion correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`.
- The two integer-indexed cochain complexes of R-modules are
  `(P Q : CochainComplex (ModuleCat.{u} R) ℤ)`. This is the Mathlib cochain
  complex constructor recorded by def-pc-cochain-complex-modules, applied to
  ordinary modules, as the item explicitly requires.
- Finite freeness in every degree is retained as `hPfree`, `hPfinite`,
  `hQfree`, and `hQfinite`, using `Module.Free` and `Module.Finite`.
- The integer bounds are `(a b : ℤ)`; `hP` and `hQ` assert `IsZero (P.X i)`
  for `a < i` and `IsZero (Q.X i)` for `b < i`. Categorical zero means the
  zero module up to its unique isomorphism. These bounds already imply
  bounded-aboveness, so no separate boundedness condition is necessary.
- The total tensor is exactly the recorded `CochainComplex.mapBifunctor`,
  with `curriedTensor (ModuleCat R)`. Mathlib totalizes by coproducts over
  pairs of integers with sum n. Its cochain signs are ε₁ = 1 and
  ε₂(p,q) = (-1)^p (ComplexShapeSigns.lean:159), giving the required
  differential `d_P tensor 1 + (-1)^p 1 tensor d_Q`.
- The isomorphism `e` has precisely source `P.homology a ⊗ Q.homology b`
  and target the degree `a+b` homology of that direct-sum total complex.
- The phrase “canonical map induced by top-degree tensor representatives”
  is encoded by the two concluding equations, rather than by an arbitrary
  isomorphism. The witness `t` goes from the tensor of cycles into total
  cycles. Its composite with total `iCycles` is the tensor of the two cycle
  inclusions followed by the `(a,b)` summand inclusion `ιMapBifunctor`.
  The second equation says that `e.hom` composed with the tensor of the
  two class maps equals `t` followed by the total class map. Thus `[p] ⊗ [q]`
  maps to the class of the tensor in the top summand, exactly as required.
  These witnesses add no mathematical condition: the first equation
  uniquely determines t because total iCycles is mono, and the second
  uniquely determines e.hom because tensoring the surjective class maps
  gives an epimorphism (right exactness). An isomorphism satisfying them
  is equivalent to invertibility of the specified canonical map.

Dependencies read and used:

- def-pc-cochain-complex-modules: `CochainComplex`, module
  `Mathlib.Algebra.Homology.HomologicalComplex` (full constructor and
  docstring read at lines 153–158). Its general category parameter allows
  the ordinary module category appearing in this item's statement.
- def-pc-tensor-complex-sheaves: `CochainComplex.mapBifunctor` and
  `CochainComplex.ιMapBifunctor`, module
  `Mathlib.Algebra.Homology.BifunctorShift` (signatures/docstrings read at
  lines 42–64), using `CategoryTheory.MonoidalCategory.curriedTensor` and
  the existing `ModuleCat.monoidalCategory`. This is the same recorded
  totalization, specialized to ordinary modules instead of module sheaves.
  `HomologicalComplex.mapBifunctor` and its totalization source were also read.
- Proof dependency lem-weil-pbc-tensor-right-exact: import
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`, which supplies
  `LinearMap.rTensor_exact` and `LinearMap.lTensor_exact`. The module
  docstring reproduces all four proof steps from the node.
- `HomologicalComplex.cycles`, `iCycles`, `homology`, and `homologyπ` come
  from `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
  Their full definitions/docstrings were read. Abelian and colimit instances
  come from ModuleCat.Abelian and ModuleCat.Colimits; no structural data
  or canonical morphism is postulated as an extra hypothesis.

Source checked: literature/stacks-project/more-algebra.tex, Section
“Tensor products of complexes”, especially its construction by the
associated simple complex; and the item's four-step direct top-degree
quotient calculation. The sign implementation in ComplexShapeSigns.lean
was checked against that convention.

Edge cases checked mathematically before delivery: either zero complex;
the zero ring; a bound strictly above the last nonzero term; complexes
concentrated in degrees a and b; arbitrary negative integers a and b
(no Nat coercions); and two-term finite free complexes Z --n--> Z in
degrees -1 and 0. The latter have top tensor cohomology
Z/(n,m), agreeing with Z/n tensor Z/m: n=2,m=3 gives zero and n=m=2 gives
Z/2. Neither top cohomology is assumed nonzero. No bounded-below,
Noetherian, locality, or nontriviality hypothesis is imposed.

Searches performed for an existing statement:

- msearch.py leanfinder: “The highest cohomology of the total tensor of two
  bounded above cochain complexes is the tensor product of highest
  cohomologies”. Eight hits about tensor existence, good tensors, and
  Hom-complex cohomology; no exact statement.
- msearch.py loogle: `HomologicalComplex.mapBifunctor, homology` returned
  unknown identifier homology and no hits.
- msearch.py leansearch: “top cohomology tensor product bounded above
  complexes” returned tensorObj, HasTensor, and unrelated derived
  t-structure declarations, no top-degree isomorphism.
- msearch.py grep: `homology.*[Tt]ensor|[Tt]ensor.*homology` in
  Mathlib Algebra/Homology returned no hits. Direct rg searches in the
  same directory also found no such statement.
- Direct rg in WeilConjectures and lean/Sheaf for the same concepts found
  derived coefficient comparisons and the already landed consumer
  LocalDerivedTensorNonvanishing, but no exact top-degree theorem.
  Focused name search for `top_degree_tensor|topDegreeTensor|`
  `top_cohomology_tensor|topCohomologyTensor` across Mathlib, upstream,
  and lean/Sheaf found no existing declaration.
- grep -rn for the item id in upstream WeilConjectures found no match.

Validation: scompile.py compiled the sandbox and destination module
without errors or warnings after adding the existing ModuleCat colimit
instance import. The final delivery is checked again by deliver2.py.

No STATEMENT-DISPUTED or node fault was found.

## Second reading by Q156

Author self-check for direct delivery; the maintainer supplies the
independent review. I reread the node with the final Lean declaration.
All four finite/free conditions, both integer bounds, the same total
complex and its signs, the source and target of the isomorphism, and
both representative equations match the statement. The first draft
lacked the ModuleCat.Colimits import, causing failure to synthesize
HasMapBifunctor; importing the existing instance fixed compilation
without adding a hypothesis. In particular the conclusion specifies
the canonical representative map, and contains no bare Nonempty
isomorphism with an unspecified action. The auxiliary existential t
is fixed uniquely by the cycle inclusion equation and introduces no
new notion. No mathematical statement changed.
