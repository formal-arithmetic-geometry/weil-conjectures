## Worker report

The module `lean/Sheaf/Algebra/Criterion.lean` states the Noetherian fibre criterion
of flatness from Stacks Tag 00MP. It uses `IsNoetherianRing` for all three commutative
rings, `IsLocalRing` and `IsLocalHom` for the two ring maps, and explicit algebra and
scalar-tower structures to express restriction of scalars. `Module.Finite S' M` renders
finite generation, and `[Nontrivial M]` renders `M ≠ 0`. The closed fibre is rendered by
`(S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) ⊗[S] M`, the canonical tensor
presentation of `M / mM`; `hfibre` says it is flat over `S / mS`. `hflat` says `M` is flat
over `R`. The conclusion is `Module.Flat R S ∧ Module.Flat S M`, exactly the two conclusions
of the node. The proof is `sorry` as required at stage 2.

The dependencies used are Mathlib's `IsNoetherianRing` (module
`Mathlib.RingTheory.Noetherian.Defs`), `Module.Finite` (the dependency node's
`mathlib_match`, `Mathlib.RingTheory.Finiteness.Defs`), and `Module.Flat`/`RingHom.Flat`
(`Mathlib.RingTheory.Flat.Basic` and `Mathlib.RingTheory.RingHom.Flat`). The local map is
expressed through `IsLocalHom (algebraMap R S)` and `IsLocalHom (algebraMap S S')`.

Edge cases checked include arbitrary universes for all rings and modules, the zero/empty
fibre possibility (excluded only by the stated `Nontrivial M` hypothesis), and the case of
zero maximal ideal (a field), where the quotient is the residue field and the tensor fibre
has the expected meaning. No characteristic or finiteness-of-the-ring assumption was added.

Searches made: `msearch.py ... leanfinder "local criterion flatness fibres Noetherian local rings module"`
returned only unrelated smoothness/localization results; `msearch.py ... loogle
"IsNoetherianRing IsLocalRing Module.Flat"` returned no match; `msearch.py ... grep
"flatness.*fibre|criterion.*flat" RingTheory` found only the generic equational criterion.
`rg` over `WeilConjectures/` found no declaration of Tag 00MP. The existing project module
`Sheaf/RingTheory/FlatOfFlatClosedFiber.lean` states the different finite-presentation
criterion (Tag 00R7), so it is not the same statement. The Stacks source confirms the four
hypotheses and two conclusions at Tag 00MP lines 23--39.

No statement correction or new definition node was needed. `Module.Finite` already has the
recorded Mathlib match in `def-weil-finitely-generated-module`; no dependency module is
required. The tensor presentation is definitionally the standard closed-fibre module and
keeps the `S / mS` base ring explicit.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The source and node were read against the module:
each Noetherian/local-ring hypothesis, both local homomorphisms, finite/nonzero module
conditions, fibre flatness, base flatness, and both flatness conclusions are present.

## Second reading by C1

I independently read the item node, its three statement dependencies, the Lean
module, and the Stacks source. The local checkout lacks `literature/stacks-project/`;
I obtained the actual `algebra.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex in this
sandbox's `scratchpad/algebra.tex`. Its conventions (lines 33ff.) require commutative
unital rings; Tag 00MP at lines 23977--24034 introduces exactly the objects and four
hypotheses below. There is no surrounding field, characteristic, finite-type or
finite-presentation hypothesis.

The complete list of introduced objects, hypotheses, and conclusion clauses is:

| Node/source item | Lean rendering | Verdict |
| --- | --- | --- |
| Three commutative unital rings R, S, S' | `(R : Type u) (S : Type v) (S' : Type w)` and the three `CommRing` instances | Exact; Stacks' ring convention |
| Each ring Noetherian | The three `IsNoetherianRing` instances | Exact; all three, including R |
| Each ring local | The three `IsLocalRing` instances | Exact; unique proper maximal ideal, hence nonzero rings |
| Maps R → S → S' | `Algebra R S`, `Algebra S S'` | Exact; arbitrary unital homomorphisms of commutative rings admit these algebra structures |
| Both maps local | `IsLocalHom (algebraMap R S)` and `IsLocalHom (algebraMap S S')` | Exact; unit reflection is equivalent to mapping maximal ideals into maximal ideals by `IsLocalRing.local_hom_TFAE` |
| Composite R → S' | `Algebra R S'` and `IsScalarTower R S S'` | Compatible composite, determined by the two maps; no extra algebraic hypothesis |
| Maximal ideal m of R | `IsLocalRing.maximalIdeal R` | Same canonical unique maximal ideal |
| M an S'-module | `(M : Type z)`, `AddCommGroup M`, `Module S' M` | Exact |
| M restricted to S and R | `Module S M`, `Module R M`, `IsScalarTower S S' M`, `IsScalarTower R S M` | The tower identities force the S action and then the R action to be the restricted actions; no independent action is allowed |
| (1) M finitely generated over S' | `Module.Finite S' M` | Exact; no finiteness of M as a set and no finite presentation |
| (2) M ≠ 0 | `Nontrivial M` | Exact for an additive group; its zero module is the subsingleton case |
| (3) M/mM flat over S/mS | `hfibre : Module.Flat (S ⧸ (maximalIdeal R).map (algebraMap R S)) ((S ⧸ (maximalIdeal R).map (algebraMap R S)) ⊗[S] M)` | Exact via the canonical quotient/tensor identification discussed below |
| (4) M flat over R | `hflat : Module.Flat R M` | Exact with the already restricted R action |
| S flat over R | First clause `Module.Flat R S` | Exact; equivalent to flatness of the given algebra map |
| M flat over S | Second clause `Module.Flat S M` | Exact; both conclusions appear in the source order |

All the object binders precede the assumptions; the conclusion is their conjunction,
with no existential choice or altered quantifier order. The auxiliary algebra and
module instances express the composite and restricted structures every source object
has, rather than adding Noetherian, finiteness, injectivity or field assumptions.

Dependency signatures opened and checked:

* `def-weil-pbc-noetherian-ring` records `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`. At lines 62--63, `IsNoetherian R M` means
  every submodule is finitely generated; lines 196--197 specialize to `M = R`.
  Thus this is exactly every ideal finitely generated.
* `def-weil-finitely-generated-module` records the Mathlib match `Module.Finite`.
  `Mathlib.RingTheory.Finiteness.Defs:117--119` gives `fg_top : (⊤ : Submodule R M).FG`.
  This is exactly the notion used here; the node's finite-ring/field observations
  impose no extra assumption on its general definition. The imported modules
  supply this declaration transitively.
* `def-weil-pbc-flat-ring-map` records `RingHom.Flat` and `Module.Flat` in
  `Mathlib.RingTheory.RingHom.Flat`. `RingHom.Flat` at lines 27--29 is flatness
  of the codomain for the induced algebra structure; `flat_algebraMap_iff` at
  lines 31--33 identifies it with `Module.Flat`. I also read
  `Mathlib.RingTheory.Flat.Basic:107--124`: its finite-submodule test implies
  preservation of arbitrary injective linear maps, as the node requires.

For the fibre, write `I = (maximalIdeal R).map (algebraMap R S)`.
`TensorProduct.quotTensorEquivQuotSMul` in
`Mathlib.LinearAlgebra.TensorProduct.Quotient:153--158` gives
`(S ⧸ I) ⊗[S] M ≃ₗ[S] M ⧸ (I • ⊤)`. Its formula sends
`[s] ⊗ x` to `[s • x]` (lines 169--181), so it respects the induced S/I action
as well. The image of m generates I; scalar compatibility and distributing
finite sums give `IM = mM`. Consequently flatness of this tensor module over
S/I is precisely the source's fibre flatness. No private fibre definition or
new definition node is needed. The worker report's claim that this identification
is *definitional* was incorrect: it is a canonical isomorphism, sufficient for
exact equivalence of the hypotheses. The theorem signature itself needed no change.

Edge cases: all four universes `u v w z` are independently declared and bound;
no same-universe restriction appears. Empty index sets, schemes, n and characteristic
do not occur. Stacks allows the zero ring in general but a local ring has a unique
maximal ideal, so it is nonzero, matching `IsLocalRing`'s `Nontrivial` superclass.
The zero module is excluded by the source's explicit (2). No nonzero fibre binder
was added: fibre nonzeroness follows from local maps, finite M and Nakayama.
For a field R, m is zero and the tensor fibre is canonically M over S, so the
statement includes this case. All characteristics are covered.

Independent searches, using different wording from the first worker:

* `msearch.py ... leansearch "For local homomorphisms A B C of noetherian rings and nonzero finite C module N, flatness of N over A and of its closed fiber over B implies B and N flat"`:
  the service returned Internal Server Error; recorded as unavailable, no verdict.
* `msearch.py ... leanfinder "Noetherian local ring flat module criterion residue quotient restriction scalars"`:
  eight hits, including smooth-algebra flatness, adic-completion flatness,
  localization criteria and `Module.faithfullyFlat_iff`; none states 00MP.
* `msearch.py ... grep "flat.*(closedFiber|closed_fiber|quotient)|criterion.*flatness" RingTheory`:
  only the equational criterion (Tag 00HK), a different statement.
* Direct `rg` on Mathlib, `WeilConjectures/`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` checked the declaration name, Tag 00MP,
  fibre-criterion wording and closed-fibre wording. No existing 00MP declaration.
  I opened `Sheaf/RingTheory/FlatOfFlatClosedFiber.lean` and its theorem
  `Module.flat_of_flat_closedFiber`: it assumes essentially finitely presented
  maps and a finitely presented module (00R7), not the Noetherian hypotheses
  of this node. The other source hits concern sheaf fibres, a different notion.

Mismatches repaired: H8, no copyright/module header and a compressed proof docstring
that did not explicitly carry every step of the node; H9, generic file name and
`Algebra` topic rather than `RingTheory`. The file is now
`lean/Sheaf/RingTheory/FlatAndFlatOfFlatFibreNoetherian.lean`, with the required
header, module source docstring, and all seven proof steps with their dependency
ids. The node's `lean.module` and `lean.file` follow that move, and
`lean.statement` is now the verbatim multiline signature, ending before `:=`.
The declaration name and mathematical signature are unchanged. The old report's
path refers to the superseded worker file. No new nodes, dependency modules,
statement correction, hollow definitions or proofs were introduced; the only
proof is the named theorem's `sorry`. All lines are at most 100 characters,
all universes/variables are explicitly bound, and the declaration has no `Sheaf.` prefix.

Validation: `scompile.py C1 lem-weil-pbc-criterion-flatness-fibre-noetherian
lean/Sheaf/RingTheory/FlatAndFlatOfFlatFibreNoetherian.lean` compiled on the server
in 1.5 seconds, exit 0, with no warnings or errors.

## Reviewer R-cfn0951 (stage 2, FIX)

Statement checked hypothesis by hypothesis against the node: correct. One fix, for
consistency with the landed non-Noetherian sibling `Module.flat_of_flat_closedFiber`
(E1 fd047eff9, lean/Sheaf/RingTheory/FlatOfFlatClosedFiber.lean): the fibre hypothesis is
now `h_fibre` with the sibling's spelling `Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)`,
and flatness of M over R is the instance argument `[Module.Flat R M]` as there. Same
mathematical content. Note the worker report above names a superseded path
(`Sheaf/Algebra/Criterion.lean`) and wrongly calls the fibre identification definitional;
it is the canonical isomorphism `TensorProduct.quotTensorEquivQuotSMul`. Sanity example:
R = S = S' = M = a field instantiates the theorem with all instances found.
