## Worker report

The module `Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients` states
`Representation.continuousCoefficient_subquotients`, with its sole proof `sorry`.
It introduces no definitions or new nodes and changes only the item's `lean` record.
The source was read directly: Bhatt–Scholze, *The pro-étale topology for schemes*,
Corollary 6.8.5, proof, printed p. 60. The sentence about kernels and cokernels
is the source of the expanded topological linear-algebra statement in this node.

Hypotheses and clauses, matched to the node:

- The prime is `(l : ℕ) [Fact l.Prime]`. The chosen algebraic closure is
  `(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
  `E : IntermediateField ℚ_[l] Ω` with `[FiniteDimensional ℚ_[l] E]` is precisely
  a finite intermediate coefficient field, without selecting a particular extension.
- `[tE : TopologicalSpace E]` and `_hE` equate its topology to the underlying
  topology of `spectralNorm.nontriviallyNormedField ℚ_[l] E`. This is a way of
  binding exactly the prescribed topology for instance inference, not an additional
  mathematical assumption about the field. It has a canonical witness. It avoids
  file-local instances and hidden `let` binders in the theorem statement.
- `G : ProfiniteGrp.{v}` supplies the compact Hausdorff totally disconnected
  topological group, including its group operations and topological group structure.
- `V`, its additive and `E`-module structures, and `ρ : G →* (V ≃ₗ[E] V)`
  give the vector space and action by linear automorphisms.
  `hV : IsContinuousCoefficient l E G V ρ` is exactly the recorded dependency's
  finite-dimensionality and joint continuity condition. `[TopologicalSpace V]`
  and `[IsModuleTopology E V]` fix the usual finite-dimensional topology.
  The same encoding is used for `W`, `X` and `Y` in the later universal quantifiers.
- The first conjunct quantifies over every `U : Submodule E V`; `_hU` says
  `a ∈ U → ρ g a ∈ U` for every `g` and `a`, exactly invariance.
  `IsClosed (U : Set V)` states closedness.
  `IsModuleTopology E U` and `IsModuleTopology E (V ⧸ U)` compare the inherited
  subtype and quotient topologies with the usual vector-space topology. Mathlib's
  inherited topologies, rather than a replacement module topology, are used here.
- The witnesses `τ` and `κ` are actions on the actual subtype `U` and actual
  quotient `V ⧸ U`. `IsEquivariant ... U.subtype` and
  `IsEquivariant ... U.mkQ` characterize the induced actions: injectivity of
  the subtype map and surjectivity of the quotient map determine them uniquely.
  Thus these are not arbitrary unidentified actions. Their
  `IsContinuousCoefficient` conjuncts state finite-dimensionality and joint
  continuity with the recorded coefficient topology; the two explicit `Continuous`
  action conjuncts also state joint continuity for the inherited topologies.
- The inclusion and projection already have types `U →ₗ[E] V` and
  `V →ₗ[E] (V ⧸ U)`. Their `IsEquivariant` and `Continuous` conjuncts say
  precisely that they are equivariant continuous linear maps.
- The second conjunct quantifies over every continuous representation `W` and
  every equivariant linear map `h : V →ₗ[E] W`, without assuming continuity of
  `h`. The conclusion `Continuous h` supplies the automatically continuous map.
  `LinearMap.ker h`, `LinearMap.range h`, and `W ⧸ LinearMap.range h` are
  literally `K`, `I`, and `Q` in the node.
- `τK`, `τI`, and `τQ` are their induced actions, characterized by equivariance
  of `(LinearMap.ker h).subtype`, `h.rangeRestrict`,
  `(LinearMap.range h).subtype`, and `(LinearMap.range h).mkQ`.
  `IsContinuousCoefficient` states that all three are finite-dimensional continuous
  representations. The following `IsModuleTopology` and `Continuous` action
  conjuncts explicitly identify their topologies and inherited joint continuity.
- Each of the four canonical arrows has an `IsEquivariant` and a `Continuous`
  conjunct. Its type supplies linearity. The first sequence is encoded by
  `Function.Injective (LinearMap.ker h).subtype`,
  `Function.Exact (LinearMap.ker h).subtype h.rangeRestrict`, and
  `Function.Surjective h.rangeRestrict`. The second has the corresponding three
  conjuncts for `(LinearMap.range h).subtype` and `(LinearMap.range h).mkQ`.
  Injectivity and surjectivity encode exactness at the two ends adjoining zero;
  `Function.Exact` encodes image equal to kernel in the middle.
- The kernel universal property quantifies over every continuous representation
  `X`, every equivariant linear `f : X →ₗ[E] V` with `h.comp f = 0`, and asserts
  `∃! f' : X →ₗ[E] LinearMap.ker h` that is equivariant, continuous, and satisfies
  `(LinearMap.ker h).subtype.comp f' = f`.
- The cokernel universal property quantifies over every continuous representation
  `Y`, every equivariant linear `g : W →ₗ[E] Y` with `g.comp h = 0`, and asserts
  `∃! g' : (W ⧸ LinearMap.range h) →ₗ[E] Y` that is equivariant, continuous,
  and satisfies `g'.comp (LinearMap.range h).mkQ = g`.
  Separate universes `w`, `z`, `x`, `y` permit arbitrary representation sizes;
  neither universal property is restricted to the size of `V` or `W`.

Dependencies read and used:

- `Sheaf.RepresentationTheory.LAdic`: `Representation.IsContinuousCoefficient`
  and `Representation.IsEquivariant`, with their complete signatures and docstrings.
  The former explicitly uses the spectral norm on `E` and `moduleTopology E V`.
  The integral and algebraic-closure representation definitions in the same module
  were read but are not substituted for the node's clause (2).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, the recorded module for
  `def-weil-l-adic-coefficient-extension`, imports the original coefficient
  construction module `Sheaf.NumberTheory.Padics.CoefficientExtension` unchanged.
  The original `Padic.coefficientExtensionAbsoluteValue` uses the spectral norm,
  consistent with the representation definition. The finite-ring theorem of the
  new dependency module is not needed in this statement.
- `Mathlib.Topology.Algebra.Module.ModuleTopology`: `moduleTopology`,
  `IsModuleTopology`. These are reused notions, with no local duplicate.
- The three proof leaves were read at their actual Mathlib declarations:
  `LinearMap.continuous_of_finiteDimensional`,
  `Submodule.closed_of_finiteDimensional`,
  `LinearMap.isClosedEmbedding_of_injective`,
  `Submodule.isOpenQuotientMap_mkQ`, and `Submodule.isOpenMap_mkQ`.
  They are supplied by the imported finite-dimension module and its imports.
- `Mathlib.Algebra.Exact.Basic`: `Function.Exact` for the underlying sequences.
  The linear maps, kernels, ranges and quotients are Mathlib's actual constructions.

Edge cases checked mathematically before writing the statement: `U = ⊥` gives
`0 → V → V`, and `U = ⊤` gives `V → V → 0`; `V = 0` gives zero subquotients.
For `h = 0`, the kernel is all of `V`, the image is zero, and the cokernel is `W`.
For an isomorphism, the kernel and cokernel vanish; injective or surjective maps
have the expected one vanishing term. Trivial and nontrivial profinite actions
are both allowed. A unipotent continuous action on `E²` has the usual invariant
line and quotient, with no semisimplicity hypothesis. The cases `l = 2` and
`E = ℚ_[l]` are included. No basis, nonzero-space assumption, invariant complement,
common representation universe, or extra action-continuity hypothesis is imposed.

Searches for an existing whole statement:

- `msearch.py leanfinder`, query “Invariant subspaces and quotients of continuous
  finite dimensional p-adic representations have continuous actions and kernels
  and cokernels”: eight hits, including `FDRep.instHasKernels`, `Rep.mkQ`,
  `Rep.quotient`, `Representation.quotient`, and continuous invariants. These give
  algebraic constructions or invariants, not the requested topology comparisons
  and continuous subquotient universal properties.
- `msearch.py loogle`, query `Representation.quotient, Representation.subrepresentation`:
  zero hits. This is only negative combined-query evidence.
- `msearch.py grep`, query `subrepresentation|quotient|cokernel` in
  `RepresentationTheory/Continuous`: zero hits.
- `msearch.py leansearch`, query “Continuous finite dimensional representations
  over a p-adic field are closed under invariant subspaces and quotients and have
  kernel and cokernel universal properties”: eight hits, including
  `Representation.quotient`, `Rep.quotient`,
  `ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range`, and
  `Submodule.closed_of_finiteDimensional`. None is the complete statement.
- Direct `rg` of `IsContinuousCoefficient`, `subquotients`, and continuity/subspace
  expressions in project `lean/Sheaf` and upstream `WeilConjectures` found the
  already recorded `LAdic` definitions, the Galois-lisse category, algebraic
  subrepresentation lemmas and unrelated cohomology results. None states this node.
  Searching the item's exact id in upstream `WeilConjectures` returned no hits.
- Read `Representation.subrepresentation` and `Representation.quotient` in Mathlib
  `RepresentationTheory/Basic.lean`: these are algebraic induced actions on
  submodules and quotient types, not the asserted continuous coefficient theorem.

No statement correction or dispute was needed. Every postponed proof is the named
item theorem, with the complete five-step DAG proof plan in its docstring.

## Validation

Compilation uses only the prescribed `scompile.py` wrapper. The first check found
an import deprecation and a projection-line parsing error; the module now imports
`Mathlib.Algebra.Exact.Basic` and writes the topology projection as one expression.
The final compilation and delivery preflight results are recorded below.

Final `scompile.py` check: both the sandbox and library-path checks passed,
with no errors or warnings (8.1 s and 12.7 s respectively).

`deliver2.py --no-push` passed: `OK (dry run)`, commit `908d7e8f2d`,
with the module compiled and server preflight accepted. The delivery contains
exactly the module, the item's node record, and this report. Independent
mathematical review is the maintainer's review, as specified by this worker brief.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
