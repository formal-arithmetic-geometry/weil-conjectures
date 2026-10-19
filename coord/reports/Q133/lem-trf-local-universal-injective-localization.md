## Worker report

The module `Sheaf.RingTheory.UniversalInjectiveLocalization` states
`LinearMap.universally_injective_localizedModule_map`, with exactly one postponed
proof (`by sorry`). There are no new definitions or nodes and no dependency repairs.
Only the item's `lean` field changes. The statement is the first assertion of
Stacks Algebra Tag 05CM(1), specialized to the multiplicative subset `{1}` in the
base ring. I read `literature/stacks-project/algebra.tex`, lines 20160–20187,
including the source proof.

The hypothesis/clause correspondence is:

| Node | Lean |
| --- | --- |
| Commutative rings R and S | `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` |
| A ring homomorphism R → S | `[Algebra R S]`, whose ring map is `algebraMap R S` |
| S-modules M and M' | Independent types `Type w`, `Type x`, additive commutative groups and `[Module S M] [Module S M']` |
| Regard them as R-modules via the given ring map | `[Module R M] [Module R M'] [IsScalarTower R S M] [IsScalarTower R S M']` |
| Multiplicative subset T of S | `(T : Submonoid S)`, including the unit and closure under products |
| The S-linear module map u | `(f : M →ₗ[S] M')` (the name `f` avoids shadowing universe `u`) |
| Universal R-injectivity of u | `hf : ∀ (L : Type (max u v w x y)) [AddCommGroup L] [Module R L], Function.Injective ((f.restrictScalars R).lTensor L)` |
| Localized modules T⁻¹M and T⁻¹M' | `LocalizedModule T M` and `LocalizedModule T M'`, the domain and codomain of `LocalizedModule.map T f` |
| The canonical localized map T⁻¹u | `LocalizedModule.map T f`, sending `m/t` to `f(m)/t` |
| Universal R-injectivity of that localized map | The conclusion quantifies over every such `L` and asserts `Function.Injective (((LocalizedModule.map T f).restrictScalars R).lTensor L)` |

The compatible R-module structures are only restriction-of-scalars bookkeeping:
`IsScalarTower.algebraMap_smul` forces `r • m = algebraMap R S r • m`.
They always exist by `Module.compHom` and impose no extra mathematical condition.
The localized R-action is the existing Mathlib action through the same tower.
In particular no flatness, injectivity of R → S, nonzero-ring hypothesis,
nonzero-denominator hypothesis, or finiteness assumption is introduced.

All five universe parameters are explicitly declared, and auto-implicit insertion
is disabled. The test module universe `max u v w x y` dominates both rings and
both modules and includes an arbitrary further universe `y`; it is not a possibly
vacuous universe below the rings. No equality of module or ring universes is imposed.
`LinearMap.lTensor` sends `l ⊗ m` to `l ⊗ f(m)`, so the order of the tensor factors
agrees with the node. It is ordinary module tensor product, not algebra tensor.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `LocalizedModule` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, with `LocalizedModule.mk`,
  `LocalizedModule.mk_eq`, `LocalizedModule.mkLinearMap`, and the fraction kernel
  criterion. The canonical localized linear map is `LocalizedModule.map` from
  `Mathlib.RingTheory.Localization.Module`, with its formula `LocalizedModule.map_mk`.
  The latter module is needed because the Basic module alone does not define that map.
- Proof dependency `lem-weil-pbc-localization-tensor-over-base` is a Mathlib leaf;
  I read its `mathlib_match` and the signatures/docstrings of
  `IsLocalizedModule.rTensor` and `IsLocalizedModule.map_lTensor` in
  `Mathlib.RingTheory.Localization.BaseChange`. The module is imported for the
  proof plan, without `public`. No unsupported dependency interface is assumed.

The theorem docstring gives every step of the node's proof: the natural S-actions
on the tensored modules; injectivity of `1_L ⊗ f`; the tensor-localization
isomorphisms and their explicit fraction formula; commutativity on generators;
and injectivity after localization by the fraction kernel criterion.

Edge cases checked before writing and again on the final statement:
`T = {1}` recovers the original assertion; `0 ∈ T` gives zero localized modules;
either module may be zero; `f = id` is included; the zero rings are allowed;
`L = 0` is allowed; `L` need not be flat (e.g. `ℤ/2ℤ` over `ℤ`); and R → S need
not be injective. Neither a converse nor injectivity of a localization map is
asserted. Arbitrary T includes prime complements without requiring primality.

Searches (all performed through the prescribed wrapper where applicable):

- `msearch.py ... leansearch "Localization of a universally injective map of modules is universally injective over the base ring"`:
  8 hits, headed by `IsLocalizedModule.map_injective`, the comparison with
  `LocalizedModule.map`, and `LocalizedModule.map_injective`; none quantifies
  over arbitrary test R-modules for an S-linear map.
- `msearch.py ... leanfinder "Localization preserves injectivity of a module map after tensoring with every module over a base ring"`:
  8 hits, including the same injectivity lemmas, invertible-module tensor
  criteria, and faithfully-flat tensor criteria. None is this theorem.
- `msearch.py ... loogle "IsLocalizedModule.map_injective, TensorProduct.map"`:
  0 hits.
- `msearch.py ... grep "universally.*injective|[Pp]ure.*localiz|localiz.*[Pp]ure" RingTheory`:
  0 hits.
- Direct `rg` in Mathlib RingTheory, Algebra/Module and LinearAlgebra for
  universal injectivity/purity found no module-map universal localization
  theorem. The pure-ideal API concerns flat quotients of ideals, not this map.
- Direct `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for
  `universally.*injective`, `universal.*injective`, `LocalizedModule.map`,
  and the item's id found no exact existing statement. The side
  `UniversalInjectiveCheckStalks` is a different prime-local criterion; its
  interface also uses explicit compatible R-actions and the dominating test
  universe. Existing localization-exactness modules only state exactness or
  ordinary injectivity.
- Direct name searches in `dag/lean_names_upstream.json`, upstream and
  `lean/Sheaf` found no pre-existing
  `LinearMap.universally_injective_localizedModule_map`.

No statement dispute or node fault was found. The final delivered module passed
`scompile.py` in both its sandbox check and its named-library check, without
errors or warnings (9.4 s and 10.0 s respectively). The prescribed
`deliver2.py Q133 lem-trf-local-universal-injective-localization --no-push`
also printed `OK (dry run)`: its packet passed the server preflight and compiled.
The final delivery invocation repeats these checks before pushing.

## Second reading by Q133

This is the author's second reading, not an independent worker review; the
maintainer supplies the independent review under the direct-delivery brief.
I reopened the node, source and final module. The table above accounts for every
hypothesis and clause. In particular the conclusion still tensors over R after
localizing at T in S; it does not accidentally change the base to S or T⁻¹S.
The fraction map is the canonical Mathlib map, not an arbitrary linear map.
The test module is unrestricted, and the original and localized tensor maps
have the same left factor L. Compatible R-actions are uniquely forced by the
ring map, as explained above. Initial elaboration exposed missing restricted
scalar actions; the final statement binds the conventional compatible actions
explicitly and uses Mathlib's existing localization instances. It contains no
file-local instances, notation, auxiliary assumptions, or helper definitions.
The proof remains `sorry` and the statement record is verbatim from the final
file. No correction to the mathematical statement was needed.
