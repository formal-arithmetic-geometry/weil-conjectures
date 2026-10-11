## Worker report

The module states the local criterion of flatness modulo a nonzerodivisor from Stacks
Tag 00ML and its following remark. It binds commutative rings `A`, `B`, an additive
commutative group `M`, a ring homomorphism `φ`, Noetherian and local ring structures,
a local-homomorphism structure on `φ`, a `B`-module structure and finite generation of
`M`, and the compatible `A`-algebra/module structures. The equality `hφ` identifies the
chosen algebra map with the stated `φ`. The element hypotheses render `x ∈ m_A`,
`IsRegular x` on `A`, and injectivity of multiplication by `φ x` on `M`. The instance
`Module.Flat (A ⧸ Ideal.span {x}) (M ⧸ (Ideal.span {x} • ⊤))` renders flatness of
`M/xM` over `A/xA`; the conclusion is `Module.Flat A M`.

The statement proof is `sorry`, as required for stage 2. Its proof docstring records the
principal-ideal multiplication argument and the application of the local criterion node.
The dependency notions are Mathlib declarations: `IsNoetherianRing` in
`Mathlib.RingTheory.Noetherian.Defs`, `Module.Finite` in
`Mathlib.RingTheory.Finiteness.Defs`, and `Module.Flat`/`RingHom.Flat` in
`WeilConjectures.Mathlib.RingTheory.Filtration` and Mathlib flatness modules.

Edge cases checked: `x` is allowed to be any regular element in the maximal ideal (so
zero is excluded whenever the ring is nontrivial); no nonzero or domain assumption is
added; arbitrary universes are bound explicitly; quotient modules and empty/zero modules
are represented by the standard ideal and submodule quotients.

Searches made: `msearch.py C1 ... leanfinder` for the local criterion (no match);
`msearch.py ... loogle "Module.Flat, IsSMulRegular, IsLocalRing"` (no match);
`msearch.py ... grep` for local-criterion and 00ML/00MK names in Mathlib (no match in
base Mathlib); `rg` over `WeilConjectures` found the exact theorem
`Module.Flat.of_flat_quotient_of_lTensor_injective` in
`WeilConjectures/Mathlib/RingTheory/Filtration.lean`, but it is the general ideal
criterion and does not state this principal nonzerodivisor specialization, so a new
statement is required. Searches over `lean/Sheaf` and DAG nodes found no existing
statement.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

Reading the node and module side by side, every node hypothesis is present: local
homomorphism (`IsLocalHom φ`), Noetherian local rings (the four typeclass binders), finite
`B`-module (`Module.Finite B M`), `x ∈ m_A`, regularity (`IsRegular x`), and injective
multiplication (`hxM`). The quotient-flatness clause is exactly the ideal-span quotient
and its generated submodule quotient. The conclusion is precisely flatness of `M` over
`A`. The module adds only explicit algebra/module compatibility data needed to type the
standard Mathlib quotient and flatness structures, together with `hφ` identifying the
chosen algebra map with `φ`; no mathematical hypothesis or conclusion is changed.

## Second reading by C1

I read the sandbox node and Lean independently against Stacks Algebra,
`lemma-variant-local-criterion-flatness` (00ML), its following principal-ideal
remark, and `remark-Tor-ring-mod-ideal` (00M6). The local copy of the Stacks source
read was `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 23751–23807 and
18690–18698 (the repository's literature checkout is absent on this machine).
The lemma itself supplies local Noetherian rings, a proper ideal and a finite
module; the following remark supplies the regular-element specialization.
There is no omitted standing field, characteristic, domain or finiteness
hypothesis. No statement correction is needed, and the node has none.

Object/hypothesis/conclusion checklist, in the node's order:

1. Commutative rings A and B: `(A : Type u) (B : Type v)` and `[CommRing A]
   `[CommRing B]`. Exact; neither is restricted to a field or a domain.
2. Ring homomorphism φ: `(φ : A →+* B)`. Exact.
3. Noetherian local rings: `[IsNoetherianRing A] [IsNoetherianRing B]`
   `[IsLocalRing A] [IsLocalRing B]`. Exact. I opened
   `def-weil-pbc-noetherian-ring` and its recorded Noetherian/Defs declaration:
   `IsNoetherianRing R := IsNoetherian R R`, equivalent to every ideal being FG.
   LocalRing/Defs defines local rings as nontrivial with the local unit property,
   the usual Stacks convention of a unique maximal ideal.
4. Locality φ(m_A) ⊆ m_B: `[IsLocalHom φ]`. Exact, rather than an extra
   assumption. Units/Hom defines this by reflecting units; LocalRing/RingHom/Basic's
   `local_hom_TFAE` equates it with mapping the maximal ideal into the maximal ideal.
5. Finite B-module M: `(M : Type w) [AddCommGroup M] [Module B M]`
   `[Module.Finite B M]`. Exact. I opened `def-weil-finitely-generated-module`
   and Finiteness/Defs: `Module.Finite` says `(⊤ : Submodule B M).FG`.
   It does not require the underlying set M or B to be finite.
6. M regarded as an A-module via φ: `[Algebra A B] [Module A M]`
   `[IsScalarTower A B M] (hφ : algebraMap A B = φ)`. Exact compatibility data.
   Algebra/Tower's `algebraMap_smul` gives `(algebraMap A B a) • m = a • m`;
   hφ thus identifies the A-action with restriction along φ. These structures
   always exist for any given φ and B-module, so they add no mathematical
   restriction. No alternative action on the quotient is supplied as a binder.
7. Element of the maximal ideal: `(x : A)` and
   `(hx_mem : x ∈ IsLocalRing.maximalIdeal A)`. Exact; `(x)` is therefore proper.
8. Nonzerodivisor on A: `(hx_reg : IsRegular x)`. Exact. Algebra/Regular/Defs
   defines injectivity of left and right multiplication; commutativity identifies
   these conditions, so this is precisely a nonzerodivisor, not a regular local
   ring or a regular sequence.
9. Injective multiplication by φ(x) on M:
   `(hxM : Function.Injective (DistribSMul.toLinearMap B M (φ x)))`.
   Exact: LinearMap/End defines this map with function `m ↦ φ x • m`.
10. Flat M/xM over A/xA: the instance
    `[Module.Flat (A ⧸ Ideal.span {x})
      (M ⧸ (Ideal.span {x} • (⊤ : Submodule A M)))]`.
    Exact canonical quotient ring and quotient module; the submodule is xM
    because the scalar action is the action via φ. I opened
    `def-weil-pbc-flat-ring-map` and Flat/Basic: its recorded `Module.Flat`
    is equivalent to tensoring preserving injectivity, including arbitrary
    modules, not just finite modules. The ring-map part of that dependency
    is not needed here. All three dependency records are usable unchanged.
11. Conclusion: `Module.Flat A M`. Exact; no freeness, faithfulness or
    finite generation over A is concluded or assumed. All data precede the
    hypotheses and the implication concludes flatness of the same M.

Edge cases: M may be zero, since neither `Nontrivial M` nor faithfulness is
assumed; injectivity and flatness of its zero quotient are then appropriate.
Zero rings are excluded by the source's local-ring convention and by
`IsLocalRing`, not by an added assumption. For nontrivial A, x = 0 fails
regularity; for A a field, membership in the maximal ideal forces x = 0,
so there are no such parameters, exactly as in the node. No characteristic
condition is imposed. The three carrier universes u, v, w are independent
and explicitly bound; there is no lower-universe quantification over test
modules. Empty index sets, schemes and n = 0 do not occur in this statement.

Independent searches used wording different from the worker's queries:

- `msearch.py ... leansearch "A finite module over a local noetherian algebra
  is flat when its reduction modulo a regular parameter is flat and the
  parameter acts injectively"`: unavailable (Internal Server Error), recorded
  by the search tool; no mathematical verdict inferred from this failure.
- `msearch.py ... leanfinder "lifting flatness across a principal ideal
  generated by a regular element in the maximal ideal"`: eight results,
  consisting of localization criteria, torsion-free criteria and preservation
  of regular sequences under flat base change; none states this node.
- `msearch.py ... loogle 'Module.Flat, "quotient"'`: zero hits.
- `msearch.py ... grep 'flat.*(regular|nonZeroDivisor|quotSMulTop)|regular.*flat|00ML|localCriterion'
  RingTheory`: preservation of regularity by flatness and regular-sequence
  tensor lemmas; no converse principal-ideal local flatness criterion.
- Direct rg in the source WeilConjectures and repository lean/Sheaf for
  nonzerodivisor/quotient flatness and 00ML found the general theorem
  `Module.Flat.of_flat_quotient_of_lTensor_injective` (Filtration.lean:532),
  which I opened. Its hypothesis is injectivity on tensoring an arbitrary
  ideal inclusion plus a Jacobson-radical condition, not the current regular
  element hypothesis. It is a proof tool, not an existing statement of this
  node. Flat/Equalizer's `Ideal.Quotient.flat_span_singleton_mul` and
  `includeLeftRingHom_mem_nonZeroDivisors_of_flat` concern different quotient
  or base-change properties. Sheaf's other matches cite this node rather
  than defining its statement. No existing declaration replaces this module.

Mismatch repaired: H8, the theorem docstring merely named the multiplication
argument and local criterion instead of carrying both proof steps. Expanded
it to describe I proper, A ≃ I, the tensor isomorphism β, μ ∘ β equal to
multiplication by φ(x), injectivity of μ, identification of the quotient,
and application of `lem-weil-pbc-flat-variant-local-criterion`, with the
flatness dependency and Stacks 00M6 identified. Also added the standard
copyright/license/authorship header (H9). The theorem signature, node record,
module path and import are unchanged. The import supplies the Mathlib
flatness, quotient-module, regularity and Noetherian infrastructure used here.
No definition, private notion, new node or dependency module is required;
there is one theorem with `sorry` and nothing proved.

Validation: scompile.py compiled the delivered module cleanly on the server
(exit code 0, 1.5 seconds). All universes and variables are explicitly bound,
all Lean lines fit 100 characters, and the node's lean.statement matches the
unchanged theorem signature verbatim up to its `:=`.

## Reviewer fix (R-fln1040, stage 2)

The delivered signature was mathematically right but carried the local map twice: a
bare `φ : A →+* B` with `[IsLocalHom φ]` beside `[Algebra A B]` and `hφ : algebraMap A B = φ`
(two maps for one notion, H4/H12), and it did not use the landed spellings of the
flatness-criterion family (E1 fd047eff9, C1 a3715b2f7, E1 6ca3360c7; J1 dd13edb4f).
Repaired: `φ`, `hφ` dropped, locality is `[IsLocalHom (algebraMap A B)]`; nonzerodivisor on A
is `x ∈ nonZeroDivisors A` (equivalent to `IsRegular x`, `isRegular_iff_mem_nonZeroDivisors`);
injectivity of `φ(x)` on `M` is `IsSMulRegular M x` (equivalent to the old `hxM` through the
scalar tower, checked in Lean); flatness of `M/xM` over `A/xA` is the explicit hypothesis
`Module.Flat (A ⧸ Ideal.span {x}) (QuotSMulTop x M)` (`QuotSMulTop x M` is the old
`M ⧸ (Ideal.span {x} • ⊤)` by `Submodule.ideal_span_singleton_smul`). Declaration name and
module path unchanged. The second reading's item 6 accepted `hφ` as harmless compatibility
data instead of removing the duplicate map.
