## Worker report

The module states the Cech equalizer assertion for a finite family `f : Fin n → R` whose
principal elements generate the unit ideal, with `LocalizedModule.Away` as the module
localization. The first conjunct renders injectivity of the diagonal localization map:
for every `m`, vanishing of all `m/1` implies `m = 0`. The second conjunct renders
exactness in the middle: every compatible family in the localizations glues to a unique
module element. `Fin n` allows the empty-index edge case: the span hypothesis then forces the zero
ring and the zero module. `n = 1`, zero modules, and zero localizing elements are permitted.

After the second reading, the canonical maps are the recorded Mathlib
`IsLocalizedModule.lift`, used directly in the statement. The named theorem
`localizationAway_map_units_of_dvd` supplies the required invertibility proof; it is the
notation step of this node, with a complete proof docstring. Both it and
`RingTheory.coverModuleExact` have `sorry` proofs at stage 2. There is no new definition.

The only dependency is the Mathlib declaration `LocalizedModule.Away` from
`Mathlib.Algebra.Module.LocalizedModule.Basic` (the dependency node
`def-weil-pbc-module-localization-away` records this declaration and its `mkLinearMap`).

Searches: the node's recorded LeanSearch, LeanFinder, Loogle, and Mathlib grep searches
found `LocalizedModule.Away`, `LocalizedModule.mkLinearMap`, and `IsLocalizedModule.lift`,
but no Cech gluing theorem for modules. `rg` over `WeilConjectures/` and `lean/Sheaf/`
found no existing cover-module exactness declaration. The statement follows Stacks
Algebra Lemma 00EK; no statement fault was found.

## Earlier second reading (a previous round; superseded)

I opened the node and module. The `CommRing R`, `AddCommGroup M`, and `Module R M`
hypotheses are explicit; `n`, `f`, and the unit-ideal span hypothesis match the finite
principal cover. The first conclusion matches injectivity componentwise, and the second
quantifies compatible local sections and gives existence and uniqueness of a single glued
`m`. The two canonical maps are cast to the common product localization using commutativity.
No mismatch was found.


## Second reading by C1

I independently opened the delivered node, its module, and the sole statement dependency
`def-weil-pbc-module-localization-away`, including its Mathlib declarations rather than
relying on the first report. The Stacks sources are absent from this machine; I read the
server's `literature/stacks-project/algebra.tex` lines 4300–4365 (00EK) and 1150–1205
(07JZ/07K0) over SSH. The source introduces a ring, finitely many generators of the unit
ideal, and an arbitrary module; it has no Noetherian, field, finite-generation, or
nonzero hypothesis. Its canonical maps are explicitly those of the module universal
property. The node correctly spells out commutativity and the equalizer interpretation.
There is no `statement_change`; no statement correction or citer review is needed.

Object/hypothesis/conclusion checklist, written before repairing the file:

- Commutative ring R: `{R : Type u} [CommRing R]`. Exact; no `Nontrivial R`.
- Finite list f_1,...,f_n: `(n : ℕ) (f : Fin n → R)`. Exact; every finite list,
  including the empty list, is admitted. A separate index universe is unnecessary.
- The elements generate the unit ideal: `hspan : Ideal.span (Set.range f) = ⊤`.
  Exact; neither individual invertibility nor nonvanishing is assumed.
- Arbitrary R-module M: `{M : Type v} [AddCommGroup M] [Module R M]`.
  Exact; `v` is independent of `u`, with no finiteness or torsion constraint.
- M_f: `LocalizedModule.Away (f i) M`. Exact; Mathlib's abbreviation is
  `LocalizedModule (Submonoid.powers (f i)) M` (Basic.lean:1475), as recorded by
  the dependency. Its fraction construction and the `mkLinearMap` signature
  (Basic.lean:489–496) implement the dependency's objects and m/1 map.
- M_(f_i f_j): both sides of the compatibility equation have precisely
  `LocalizedModule.Away (f i * f j) M` as target. Exact; no iterated-localization
  object or cast between unequal types is substituted.
- Canonical overlap maps: the local abbreviation `ρ` applies the dependency's
  `IsLocalizedModule.lift` (Basic.lean:928) to the two recorded `mkLinearMap`s.
  `localizationAway_map_units_of_dvd` supplies exactly its invertibility argument;
  `dvd_mul_right` and `dvd_mul_left` give the two divisibility proofs. The helper
  is a proof of the node's notation step, not a new notion or a new assumption.
  `lift_comp`, `lift_apply`, and `lift_unique` (Basic.lean:932–957) verify that these
  are precisely the unique canonical maps sending m/1 to m/1. Exact.
- Alpha injective / exactness at M: the first conjunct says
  `∀ m, (∀ i, mkLinearMap ... m = 0) → m = 0`. Exact for a linear map.
- Beta's kernel / exactness in the middle: the second conjunct quantifies every
  dependent family `s`, then equality of its two canonical images for every `i j`,
  then `∃! m, ∀ i, mkLinearMap ... m = s i`. Exact, including uniqueness.
  Equality of the images is exactly vanishing of their difference. Finite products
  and finite direct sums have the same families, so the node's explicit “That is”
  formulation is rendered without changing its strength or quantifier order.
- No final surjectivity clause is required: 00EK and the node assert exactness at M
  and the middle term, with no trailing zero. The Lean has exactly those clauses.

Edge cases: for n = 0, `Ideal.span ∅ = ⊤` forces 1 = 0. Every unital R-module is
then subsingleton, so the unique empty family glues to the unique module element;
no `[Nonempty (Fin n)]` or `[Nontrivial R]` excludes this case. For n = 1 the generator
is a unit and the theorem is the expected localization isomorphism. Zero M is admitted.
Zero localizing elements are admitted (their localizations are zero); repeated generators
and pairs with i = j are admitted. The empty spectrum is the zero-ring case. All
characteristics and independent ring/module universes are covered. Neither scheme nor
geometric hypotheses occur here.

Independent searches on 2026-10-11 (actual results are also in searches.jsonl):

- LeanSearch: “Compatible sections of localizations of an arbitrary module on a finite
  principal cover glue uniquely”. Service returned Internal Server Error; no mathematical
  verdict is based on this unavailable service.
- Loogle: `LocalizedModule, ExistsUnique`. Zero hits.
- LeanFinder: “Every compatible family in modules localized at finitely many generators
  of the unit ideal comes from a unique module element”. Hits concern finite presentation,
  lifting linear maps, and clearing denominators (`exist_integer_multiples_of_finite`),
  not this arbitrary-module equalizer statement.
- LeanFinder: “Scalar multiplication by a divisor of f is invertible on the localized
  module M_f”. Hits include `IsLocalizedModule.map_units`, `divBy_mul_by`, and
  `mul_by_divBy`; they concern elements of the localized submonoid, not this divisor
  argument. The helper records that remaining elementary proof.
- Mathlib grep: `awayToAway|existsUnique.*span|coverModuleExact` found ring and monoid
  maps and the ring-only `Localization.existsUnique_algebraMap_eq_of_span_eq_top`.
  No matching arbitrary-module gluing theorem. Additional grep of LocalizedModule
  and LocalProperties found no module-specific invertibility-of-divisor theorem.
- Independent rg of `WeilConjectures/` and the repository's `lean/Sheaf/` with
  `awayToAway|canonicalLocalization|coverModuleExact|compatible.*localiz|glue.*localiz`
  found unrelated stalk/base-change, formal glueing, and sheaf-site statements,
  not this principal-cover equalizer theorem. I also checked upstream names.

Mismatches and repairs:

1. H4/H8: the first file defined its own chosen canonical map instead of using the
   dependency's recorded `IsLocalizedModule.lift`; its auxiliary declarations carried
   the dependency's blueprint tag although the file belongs to this item. Removed both
   `exists_canonicalLocalizationMap` and `canonicalLocalizationMap`. Used Mathlib's
   lift directly and stated the missing invertibility proof as the named
   `localizationAway_map_units_of_dvd`, tagged to this node's notation step.
2. H8: the main docstring merely named common denominators and partition of unity.
   Replaced that summary with all six proof steps, including the common exponents,
   annihilator identity, construction, verification, and uniqueness, citing the node's
   actual proof dependencies. The helper has its own full natural-language proof.
3. H9: added the standard copyright/license header and removed unused BigOperators scope.
4. The report incorrectly said hspan excludes empty covers. Corrected it to include
   the zero ring and zero module; documented the empty branch of the proof explicitly.
5. The original recorded signature did not verbatim match the file's line wrapping.
   Regenerated `lean.statement` directly from the final signature and recorded both
   theorem names in `lean.declarations`.

The main mathematical statement and stmt_deps remain unchanged. No new definition node
or dependency module is needed: the sole dependency's Mathlib record is usable after all.
There is no hollow definition (no global definition remains), nothing is proved (both
named theorems are `by sorry`), and all variables/universes are explicitly bound.
Compilation through scompile.py on the server passed with exit code 0, no errors or
warnings. Both imports are used. The delivery dry run is checked after this report.
