## Worker report

The module `Sheaf.RingTheory.FiniteInjectionBidualInjective` states
`LinearMap.dualMap_dualMap_injective_of_injective_of_finite`, with proof `sorry`.
No definitions, helper nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes. There is no statement dispute.

Source read: Stacks Project, `literature/stacks-project/more-algebra.tex`,
Tag 0EB8, `more-algebra-lemma-sequence-reflexive`, especially the claim that `j`
is injective (lines 5286–5305). The source first shows the dual-map cokernel is
torsion after passing to the fraction field, then dualizes again. Its injectivity
claim uses finiteness and the Noetherian-domain assumptions, but neither
reflexivity of the larger module nor torsion-freeness of the quotient. The five
DAG proof steps are recorded in order in the theorem docstring, including the
localization/tensor comparison, its naturality, extension over the field,
clearing denominators, and domain cancellation.

Each hypothesis and clause matches as follows:

- A commutative ring `R` is `{R : Type u} [CommRing R]`.
- The integral-domain hypothesis is `[IsDomain R]`, including `0 ≠ 1`.
- The Noetherian hypothesis is `[IsNoetherianRing R]`.
- The modules are `{U : Type v} [AddCommGroup U] [Module R U]` and
  `{V : Type w} [AddCommGroup V] [Module R V]`.
- Finite generation of each is `[Module.Finite R U]` and `[Module.Finite R V]`.
- The given linear map is `(f : U →ₗ[R] V)` and its injectivity is
  `(hf : Function.Injective f)`.
- The dual `W* = Hom_R(W,R)` is Mathlib's `Module.Dual R W`, an abbreviation
  for `W →ₗ[R] R`. Its definition and the full dual-map signature were read
  in `Mathlib/LinearAlgebra/Dual/Defs.lean`.
- The prescribed `f*` is `f.dualMap`: `LinearMap.dualMap_apply'` says
  `f.dualMap φ = φ.comp f`.
- Thus the prescribed `f**` is `f.dualMap.dualMap`, a map from
  `Module.Dual R (Module.Dual R U)` to `Module.Dual R (Module.Dual R V)`.
  Applying `LinearMap.dualMap_apply` twice gives exactly
  `f.dualMap.dualMap x φ = x (φ.comp f)`. These are the existing canonical
  constructions, with no arbitrary map or added comparison assumption.
- The entire conclusion is `Function.Injective f.dualMap.dualMap`.

The ring and the two modules have independent explicitly declared universes
`u v w`; no size equality or smallness hypothesis is imposed. All variables
are bound in the theorem signature.

Statement dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, publicly imported. Its docstring and
  definition say all ideals are finitely generated, exactly the node's notion.
- `def-weil-finitely-generated-module`: `Module.Finite` from
  `Mathlib.RingTheory.Finiteness.Defs`, publicly imported. Its field is that
  the top submodule is finitely generated, exactly generation by finitely many
  elements. No finite-underlying-set assumption is substituted.

The five proof dependencies are Mathlib leaves. Their recorded declarations
and source signatures were read, and their modules are plain proof imports:

- `lem-trf-vector-subspace-complement`: `Submodule.exists_isCompl`,
  `Mathlib.LinearAlgebra.Basis.VectorSpace`.
- `lem-weil-pbc-flat-base-change-hom-finitely-presented`:
  `Module.FinitePresentation.isBaseChange_map` and
  `Module.finitePresentation_of_finite`, `Mathlib.Algebra.Module.FinitePresentation`.
- `lem-weil-pbc-localization-flat`: `IsLocalization.flat`,
  `Mathlib.RingTheory.Flat.Localization`.
- `lem-weil-pbc-localization-module-exact`: `LocalizedModule.map_exact`,
  `Mathlib.Algebra.Module.LocalizedModule.Exact`.
- `lem-weil-pbc-localization-tensor-product`: the tensor-localization instance,
  `IsLocalization.moduleTensorEquiv` and `IsLocalizedModule.of_linearEquiv`,
  via `Mathlib.RingTheory.Localization.BaseChange`.

Edge cases were checked mathematically before writing:

- `U = 0`, `V = 0`, and the zero map when injective: the zero domain of the
  bidual map is permitted. Nothing requires nonzero modules.
- Finite torsion modules such as `U = V = Z/n`: their duals into `Z` vanish,
  so the double-dual map is injective without imposing torsion-freeness.
- Over `Z`, multiplication by a nonzero integer on `Z` is injective and its
  double dual is the same multiplication. Its single dual need not be
  surjective, so a single-dual surjectivity theorem cannot replace this node.
- A field is included as a Noetherian domain, recovering the usual vector-space
  result. The excluded zero ring is correctly excluded by the word domain.
- No free, projective, reflexive, or finite-presentation hypothesis is added.

Searches made through `msearch.py` with group Q97 and this item:

- LeanFinder: `An injective linear map between finitely generated modules over
  a Noetherian integral domain induces an injective map on double duals`.
  Eight hits included `LinearMap.dualMap_injective_of_surjective`,
  `Module.dualMap_dualMap_eq_iff_of_injective`, and field-only dual-map results;
  none is an exact match.
- Loogle: `LinearMap.dualMap, Function.Injective`. Six hits: single-dual
  injectivity from a surjection; equality detection by the bidual under a
  reflexivity hypothesis; field-only surjectivity/injectivity equivalences;
  and the topological `SeparatingDual` result. None states this node.
- LeanSearch: `An injection of finitely generated modules over a Noetherian
  domain induces an injection on double duals`. Eight hits included
  character-module duality into Q/Z, field-only duality, reflexivity, and
  fractional-ideal duality. None matches the general finite-module statement.
- Mathlib grep via the wrapper: `dualMap.*injective|injective.*dualMap|dualMap.*dualMap`
  in `LinearAlgebra/Dual`, ten hits. Read the actual definitions and candidate
  signatures; no existing theorem has the present hypotheses and conclusion.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `dualMap.*injective|injective.*dualMap|double.dual.*inject|bidual.*inject`:
  uses of the field and surjection results only; no double-dual injection
  theorem over a Noetherian domain.
- Direct `grep -rn` for the exact node id in `lean/WeilConjectures`: no match.
  Direct searches of `dag/lean_names_upstream.json` and algebra/ring/linear
  algebra modules find only unrelated bidualities and characteristic-polynomial
  results. The new full declaration name and module name have no existing match
  in Mathlib or either project source tree.

Validation: the prescribed `scompile.py` compiled this one module in both
sandbox and library mode on the server with no errors or warnings (1.7 s and
2.2 s respectively). The only theorem has a `sorry` proof; all lines are at
most 92 characters. The node's recorded signature is verbatim from the module.

## Second reading by Q97

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
