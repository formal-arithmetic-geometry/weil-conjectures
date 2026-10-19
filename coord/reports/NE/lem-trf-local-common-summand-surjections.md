## Worker report

The module `Sheaf.RingTheory.LocalCommonSummandSurjections` states
`LinearMap.exists_common_summand_of_surjective_of_isLocalRing` with `sorry`.
No definitions, new nodes, dependency repairs, or statement changes are needed.
Source read: `literature/stacks-project/more-algebra.tex`, Tag 0FJK,
`lemma-homotopic-surjections`, final paragraph. It explicitly asks for a common
summand for two surjections over a local ring, first over its residue field and
then lifted. The docstring supplies all eight proof steps from the DAG.

Hypothesis and conclusion correspondence:

- A commutative local ring is `{R : Type u} [CommRing R] [IsLocalRing R]`.
  Mathlib's nontrivial local-ring predicate is equivalent to having exactly one
  maximal ideal. This excludes the zero ring exactly as the node does.
- The nonnegative integers are `(m n : ℕ)` with no positivity restriction.
- The stipulated tuple modules are literally `Fin n → R` and `Fin m → R`,
  with Mathlib's componentwise additive and module structures. These are the
  concrete finite free modules, rather than arbitrary modules with extra data.
- Both R-linear maps are `(α β : (Fin n → R) →ₗ[R] (Fin m → R))`.
- The two surjectivity hypotheses are `hα : Function.Surjective α` and
  `hβ : Function.Surjective β`.
- The common R-submodule is `∃ U : Submodule R (Fin n → R)`.
- The first restriction is `α.comp U.subtype`, and
  `Function.Bijective (α.comp U.subtype)` says it is a linear isomorphism.
  A bijective linear map has its unique linear inverse (`LinearEquiv.ofBijective`).
- The second restriction is `β.comp U.subtype`, with its separate bijectivity
  conjunct. The same existentially bound U occurs in both.
- The two internal direct sums are `IsCompl (LinearMap.ker α) U` and
  `IsCompl (LinearMap.ker β) U`. In the submodule lattice these mean intersection
  zero and sum the whole module, hence unique internal direct-sum decompositions.
  Both of the node's final equalities are explicitly retained.

Statement dependency read and used: `def-weil-pbc-free-module` records
`Module.Free` in `Mathlib.LinearAlgebra.FreeModule.Basic`; its signature and
basis docstring were read. That module is publicly imported. No private
version of free modules is introduced; the tuple module is exactly the one
specified by this item's text and carries Mathlib's standard finite basis.
Other signature notions use `Submodule.subtype` and `LinearMap.comp` from
Mathlib's submodule/linear-map API, and `IsLocalRing` from
`Mathlib.RingTheory.LocalRing.Defs`.

Proof-dependency imports retain the DAG plan: `Submodule.exists_isCompl` from
`Mathlib.LinearAlgebra.Basis.VectorSpace`, `FiniteDimensional` from
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`,
`LinearMap.finrank_range_add_finrank_ker` from
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`,
`FiniteDimensional.nonempty_linearEquiv_of_finrank_eq` from
`Mathlib.LinearAlgebra.Dimension.Free`, `LinearMap.baseChange` from
`Mathlib.LinearAlgebra.TensorProduct.Tower`, and
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_extendScalars_of_finite_free`
from `Sheaf.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso`. These signatures
and their source context were read. None is replaced with a local copy.

Edge cases checked before writing: when m = 0, U = 0 works; when n = 0,
surjectivity forces m = 0 over a nonzero local ring. When m = n, surjective
square maps are invertible and U is the whole module. Arbitrary residue fields,
including characteristic two and finite fields, are allowed: the graph
construction does not require a generic choice or division by 2. The universe
u is arbitrary. No extra nonempty-index, positive-rank, field, Noetherian,
flatness, or characteristic hypothesis occurs. No statement fault or dispute
was found.

Searches performed through `msearch.py NE lem-trf-local-common-summand-surjections`:

- LeanFinder: "Two surjective linear maps between finite free modules over a
  commutative local ring have a common submodule on which both restrictions
  are isomorphisms". Eight hits, including OrzechProperty injectivity results,
  `exists_bijective_map_powers`, and
  `LinearMap.split_surjective_of_localization_maximal`; none gives a common
  summand for two maps.
- LeanSearch: "Two surjections of finite free modules over a local ring have a
  common complementary summand". Eight hits, including
  `LinearMap.coe_equivProdOfSurjectiveOfIsCompl`,
  `LinearMap.splittingOfFinsuppSurjective`, `LinearMap.ofIsCompl`, and individual
  projection/splitting statements; none asserts this simultaneous existence.
- Loogle: `IsCompl, IsCompl`. Twelve hits giving the predicate, symmetry,
  complemented lattices, and uniqueness in distributive lattices; no match.
- Mathlib grep: `common.*complement|exists.*isCompl.*isCompl|common.*summand`
  in `LinearAlgebra`. Four hits: an individual vector-space complement and
  uniqueness of decomposition from an already given complement; no match.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for
  `common.*(summand|complement)|exists.*isCompl.*isCompl|exists_common|lem-trf-local-common-summand-surjections`:
  unrelated common-stage, geometric-refinement, field-extension, and other
  declarations, but no statement of this lemma and no occurrence of this id.
- Exact proposed declaration-name search in Mathlib, the upstream source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py NE lem-trf-local-common-summand-surjections` compiled
this delivered module successfully in both the sandbox and library checks
(1.2 s and 1.3 s), with no errors or non-sorry warnings.

## Second reading by NE

Author's separate self-reading under the dispatcher/direct-delivery brief;
the maintainer supplies the independent review. Reopened the node and the
finished Lean file. R, m, n, α and β agree exactly with the source; both
surjectivity assumptions remain separate. The module types are finite tuple
modules as the statement specifies. Checked that `U.subtype` includes U into
the source, so the composition direction renders each restriction correctly.
Bijectivity of each linear restriction is exactly isomorphism, with no extra
choice of inverse imposed. The last two conjuncts assert both kernel/U
complement relations, rather than merely existence of some complement.
No rank positivity, field, finiteness-of-ring, or characteristic assumption
was added. The proof docstring follows all eight recorded steps and every
available proof prerequisite is imported. No mismatch was found and no
statement correction was made.
