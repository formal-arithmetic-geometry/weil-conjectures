## Worker report

The module [FiniteSchemeCohomologyTensor.lean] defines the statement
`AlgebraicGeometry.Scheme.Modules.finiteSchemeCohomologyTensor`. It binds a field `k`, a
commutative `k`-algebra `A` with finite-dimensionality, the induced affine scheme, coherent
module `G`, and invertible module `L`. The first conjunct renders vanishing of every positive
cohomology object for `G`; the second renders the same for `G ⊗ₘ L`. The final two conjuncts
record the degree-zero cohomology objects and their tensor counterpart (the proof is `sorry`).

Dependencies used: `Mathlib.AlgebraicGeometry.Scheme`;
`WeilConjectures.AlgebraicGeometry.Modules.Invertible` (`AlgebraicGeometry.Scheme.Modules.IsInvertible`);
`WeilConjectures.AlgebraicGeometry.Cohomology.Defs` (`Scheme.Modules.H`, tensor and cohomology);
`Sheaf.AlgebraicGeometry.Coherent` (`AlgebraicGeometry.RingedSpace.IsCoherent`);
`Mathlib.LinearAlgebra.Dimension.Finrank`.

Edge cases checked: `q = 0` is excluded by `0 < q`; the tensor module is formed in the
scheme's module category; finite-dimensionality is a typeclass hypothesis, including the zero
algebra case. Searches in Mathlib and WeilConjectures for finite-scheme cohomology and tensor
invariance found no exact declaration; the stage-1 searches recorded in the node report the
same result.

## Earlier second reading (a previous round; superseded)

The statement compiles cleanly with the expected `sorry` warning; its signature and blueprint
identifier are recorded in the node JSON. The dry-run preflight's remaining checks are
satisfied by the branch and existing metadata above.

## Second reading by N1

Read the node, its eight statement-dependency records, the declarations below, and Stacks
varieties.tex, lemma-chi-tensor-finite (Tag 0AYT), including its proof, on the project server.
The local literature checkout lacks varieties.tex, so the source was read on the server.
The source assumes a field, a proper scheme, coherent modules and support of dimension at
most zero. Here Spec A is finite over k, hence proper and zero dimensional, without adding
properness or Noetherian hypotheses. The node specializes the source's finite affine support
scheme and locally free rank n tensor argument to n = 1. Its own statement is correct and
unchanged. No statement_change, new nodes or dependency modules are needed.

Object/hypothesis/conclusion checklist (in the node's order):

- Field k: `{k A : Type u} [Field k]`. Exact.
- Finite-dimensional commutative k-algebra A: `[CommRing A] [Algebra k A]
  [FiniteDimensional k A]`. Exact; `FiniteDimensional` is Mathlib's finite spanning/basis
  notion and `Module.finrank` is the recorded vector-space dimension.
- T = Spec A: `(Spec (.of A)).Modules` fixes the scheme rather than an arbitrary affine
  scheme. The canonical structure morphism is `Spec.map (CommRingCat.ofHom (algebraMap k A))`,
  supplied explicitly to every occurrence of the recorded `eulerChar` definition. Exact.
- Coherent G: `RingedSpace.IsCoherent (Spec (.of A)).toRingedSpace G`. Opened Coherent.lean:
  it states finite type and finite-type kernels of maps from finite free modules on each
  open, precisely the recorded coherent notion. Exact.
- Invertible L: `hL : L.IsInvertible`. Opened the source Modules/Invertible.lean: each point
  has a neighbourhood on which L is the structure sheaf. This is local rank-one freeness;
  on schemes it gives quasi-coherence as well. No stronger assumption. Exact.
- Vanishing for G in every positive degree: first conjunct, `∀ q : ℕ, 0 < q → IsZero
  ((RingedSpace.moduleCohomology ... q).obj G)`. Opened RingedSpaceModuleCohomology.lean:
  these are right derived functors of module-valued global sections, as pqf-def-cohomology
  requires. IsZero is used on a ModuleCat object, not on its bare carrier. Exact.
- Vanishing for G tensor L: second conjunct with `.obj (G ⊗ₘ L)`. Opened the tensor
  definition in Modules/Invertible.lean and Sheaf/Monoidal.lean, and the recorded tensor
  dependency module: this tensor is `SheafOfModules.monoidalCategory X.sheaf` and its
  `tensorObjIsoSheafification` is the sheafification of the sectionwise presheaf tensor.
  Thus this uses the shared tensor definition, not a private copy. Exact.
- Both global section spaces are finite dimensional over k: third and fourth conjuncts
  are `@FiniteDimensional k Γ(G, ⊤) ...` and its tensor analogue. Their module structure
  is explicit restriction along `(Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A)`.
  This is the k action induced by the given algebra, not an arbitrary Over instance. Exact.
- Equality of global section dimensions: fifth conjunct equates the two explicit
  `@Module.finrank` terms, tensor first, original second. Exact.
- Euler characteristics defined, chi(T,G) = dim global sections: sixth conjunct uses the
  dependency's `@eulerChar` with the canonical structure morphism and casts the finrank
  to an integer. Opened Cohomology/Defs.lean: eulerChar is the alternating finsum of
  finrankH. The positive vanishing and finite-dimensional sections ensure an actual
  finite Euler sum via the standard module/abelian-sheaf cohomology comparison. This
  comparison is stage-3 proof work, not an additional hypothesis or a new definition.
  Both modules satisfy those finiteness/vanishing conclusions. Exact.
- chi(T,G tensor L) = chi(T,G): seventh conjunct, the same recorded Euler characteristic
  with the same canonical structure morphism on both sides. Exact.

Mismatches repaired: the earlier statement's last two clauses were reflexive equalities
`G.H 0 = G.H 0` and the tensor analogue. They said nothing about finiteness, dimensions or
Euler characteristics. Replaced them with the five missing conclusions. Replaced the
underlying abelian-sheaf H in the vanishing conclusions by the recorded module-derived
cohomology. Removed the arbitrary Over hypothesis, using the algebra-induced structure
morphism explicitly instead. Expanded the docstring to all six proof steps with their
node references. Removed unused direct imports. Bare tensor notation under module-derived
cohomology could not infer the scheme's monoidal structure; the shared scoped `⊗ₘ`
notation resolves it without introducing an instance or a new definition.

Edge cases: q = 0 is excluded only from positive-degree vanishing and included by global
sections/Euler conclusions. A = 0 is allowed (no Nontrivial A); Spec A may be empty, all
module sections and cohomology then vanish, and dimensions and Euler characteristics are
zero. G = 0 is allowed. There is no index set, nonempty-spectrum assumption, characteristic
restriction, algebraic-closure assumption, Noetherian hypothesis or properness hypothesis.
The universe u is bound and arbitrary, as in the recorded scheme/Euler encoding; field,
algebra, modules and schemes share its ambient universe. No unbound variables or universes,
local notation, local instances, auxiliary definitions or additional proved theorems remain.
The sole proof is the named theorem's sorry.

Independent searches:

- LeanSearch via msearch, query "coherent sheaf finite scheme Euler characteristic line
  bundle": service returned Internal Server Error; recorded unavailable, not evidence of
  absence.
- LeanFinder via msearch, query "Euler characteristic and dimension of sections of a
  coherent module on an Artinian affine scheme": eight hits about Artinian schemes,
  finite modules, Krull dimension and module length; no exact statement.
- Loogle via msearch, query `"eulerChar"`: twelve abstract graded-object/complex Euler
  characteristic declarations, not the scheme statement.
- rg in Mathlib's AlgebraicGeometry and CategoryTheory/Sites for FiniteDimensional,
  finrank and eulerChar; rg in WeilConjectures and lean/Sheaf for the proposed full name,
  finite/tensor Euler characteristic and finite/tensor finrank. No exact declaration.
  Opened the closest source theorem `Modules.finrankH_zero_eq_finrankΓ_of_isFinite`
  in Curve/RiemannRoch.lean: it requires an invertible module and states only a degree-zero
  rank equality, not the coherent G, vanishing, finiteness and Euler conclusions here.
  Opened the project's `eulerChar_zero_dim_support`: it concerns an arbitrary proper
  scheme with zero-dimensional support, and omits the two explicit global-section
  finite-dimensionality conclusions. It is not the exact node statement, and its proof
  explicitly cites this item. The shared notions already exist; no new definition is needed.

Validation: server single-file scompile completed cleanly. The node lean.statement is
copied verbatim from the repaired signature. Delivery dry-run and final push follow below.
