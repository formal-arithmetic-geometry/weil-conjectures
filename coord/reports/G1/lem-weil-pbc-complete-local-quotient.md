## Worker report

The module `Sheaf.RingTheory.CompleteLocalQuotient` states
`quotient_complete_local` with a `sorry` proof. It uses Mathlib's `CommRing`,
`IsNoetherianRing`, `IsLocalRing`, `IsAdicComplete`, `Ideal.Quotient`, and
`IsLocalRing.maximalIdeal`; no new definitions or dependency modules were needed.

The hypotheses and clauses are rendered as follows:

- A commutative ring R is `(R : Type u) [CommRing R]`, with an explicit universe.
- R is Noetherian is `[IsNoetherianRing R]`.
- R is local is `[IsLocalRing R]`.
- Completeness at its maximal ideal is
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
- I is an ideal is `(I : Ideal R)` and properness is `(hI : I ≠ ⊤)`.
- The quotient is made nontrivial by the local `letI`
  `Ideal.Quotient.nontrivial_iff.mpr hI`, exactly expressing I ≠ R.
- The quotient local-ring structure is the local `letI`
  `IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`.
- Noetherianity of R/I is `IsNoetherianRing (R ⧸ I)`.
- Locality of R/I is `IsLocalRing (R ⧸ I)`.
- Its maximal ideal is identified with the image m/I by
  `IsLocalRing.maximalIdeal (R ⧸ I) =
  (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)`.
- Completeness is
  `IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I)`.
  Together with the preceding equality this is completeness for m/I.

The dependency nodes are both Mathlib declarations: `def-weil-pbc-noetherian-ring`
uses `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs`, and
`def-weil-pbc-adically-complete-ring` uses `IsAdicComplete` from
`Mathlib.RingTheory.AdicCompletion.Basic`. Their signatures and docstrings were
read. The quotient map is `Ideal.Quotient.mk I` and its surjectivity theorem is
`Ideal.Quotient.mk_surjective`.

Edge cases checked: I = ⊥ gives the original ring quotient; I = ⊤ is excluded by
hI; the zero ring is excluded from the quotient by the explicit nontriviality
instance; arbitrary universe `u` is retained; no domain, characteristic, or
finite-generation hypothesis was added. The maximal-ideal equality records the
paper's explicit `m/I` clause rather than merely asserting locality.

Searches for an existing statement were made with `msearch.py` LeanFinder for
“quotient of a complete Noetherian local ring is complete”, Loogle for
`IsAdicComplete` and quotient maps, and grep/rg over Mathlib,
`WeilConjectures`, and `lean/Sheaf`; these found only the separate quotient-local,
quotient-Noetherian, and adic-completeness ingredients, not this conjunction.
The exact declaration name `quotient_complete_local` was also searched and had no
collision. `scompile.py` compiled the module on the server with no errors or
warnings.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The worker checked the complete node and
module together: each source hypothesis and each conclusion clause is represented
above, with the quotient's properness supplying the required nontrivial instance.

## Second reading by G1

I independently opened the item node, its Lean file, both statement-dependency
nodes and their Mathlib declarations. The Stacks TeX is absent in this checkout;
I read the local source copy `/home/ubuntu/c1-stacks-review/algebra.tex` at
lines 44779–44823 (complete local rings and lemma-quotient-complete-local),
22626–22638 (definition-complete), and 22901–22918 (lemma-completion-tensor).
The source introduces a Noetherian complete local ring, with no additional
field, characteristic, domain or finite-type assumption. The node selects the
proper-quotient assertion, not the subsequent assertion about arbitrary finite
ring maps. No statement correction is needed or present.

Object, hypothesis and conclusion checklist (all pass):

- Commutative ring R: `(R : Type u) [CommRing R]`. An arbitrary explicitly
  bound universe is used.
- Noetherian R: `[IsNoetherianRing R]`. The dependency
  `def-weil-pbc-noetherian-ring` records `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`. I read its abbreviation as
  `IsNoetherian R R` and `isNoetherianRing_iff_ideal_fg`: every ideal is
  finitely generated, exactly the node's notion.
- Local R with its unique maximal ideal m: `[IsLocalRing R]` and
  `IsLocalRing.maximalIdeal R`. I read `LocalRing/Defs.lean`,
  `LocalRing/MaximalIdeal/Defs.lean` and `MaximalIdeal/Basic.lean`:
  locality includes nontriviality; the nonunits form the unique maximal ideal.
- m-adic completeness of R: `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
  The dependency `def-weil-pbc-adically-complete-ring` records
  `IsAdicComplete` in `Mathlib.RingTheory.AdicCompletion.Basic`. I read its
  Hausdorff/precomplete fields and `AdicCompletion.of_bijective_iff`:
  completeness includes separatedness and is exactly bijectivity of the
  canonical inverse-limit map, not only surjectivity.
- Proper ideal I: `(I : Ideal R) (hI : I ≠ ⊤)`. No prime or maximal ideal
  assumption is imposed on I. The quotient object is Mathlib's `R ⧸ I`.
- Quotient nontriviality: the first `letI` is
  `Ideal.Quotient.nontrivial_iff.mpr hI`; this derives nontriviality from
  properness, rather than introducing a further hypothesis.
- Quotient local structure: the second `letI` applies
  `IsLocalRing.of_surjective'` to `Ideal.Quotient.mk I` and
  `Ideal.Quotient.mk_surjective`. I read its signature in `LocalRing/Basic.lean`;
  it only requires the already derived quotient nontriviality.
- Quotient Noetherian: `IsNoetherianRing (R ⧸ I)`, the first conjunct.
- Quotient local: `IsLocalRing (R ⧸ I)`, the second conjunct. Although already
  supplied by the local binder, this is the explicit conclusion clause; the
  binder is an existing Mathlib theorem application, not an assumption.
- Maximal ideal m/I: the third conjunct is
  `IsLocalRing.maximalIdeal (R ⧸ I) =
  (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)`.
  Since a proper ideal of a local ring lies in m, this mapped ideal is m/I.
- Completeness of the quotient at m/I: the final conjunct is
  `IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I)`.
  Together with the equality, it is precisely the node's completeness clause.
  The order is R, its structures, I, properness, then all conclusions.

Edge cases: I = bottom is included; I = m is included and gives a residue field
complete at zero; a field R is allowed. I = top is excluded exactly as the node
requires. A zero ring has no proper ideal and is not a local ring in these
conventions, so no applicable case is lost. There are no scheme or index-set
objects. The completion includes n = 0; both filtrations then give the entire
quotient, so the corresponding quotient is zero and the limit is unaffected.
All characteristics and arbitrary universe u are admitted; there are no hidden
unbound variables or additional instances in the signature.

Independent searches, using wording beyond the worker's searches:

- LeanFinder through `msearch.py`: “surjective image of a Noetherian complete
  local ring is complete at its maximal ideal” returned
  `AdicCompletion.of_surjective_iff`, `AdicCompletion.map_surjective`,
  `surjective_of_mk_map_comp_surjective`, and completion-locality results.
  None states the node's conjunction or its quotient-completeness assertion.
- Loogle through `msearch.py`: `IsAdicComplete, Ideal.map` returned
  `IsAdicComplete.map_algebraMap_iff`, `IsAdicComplete.congr_ringEquiv`, and
  `AdicCompletion.isAdicComplete_self`. I inspected the returned signatures;
  these concern change of scalars, ring equivalences, or a completion itself,
  not proper quotients of the given complete ring.
- LeanSearch through `msearch.py`: “The quotient of a Noetherian ring complete
  at its maximal ideal is adically complete” was UNAVAILABLE (HTTP internal
  server error). No verdict is inferred from that unavailable search.
- rg on Mathlib/RingTheory, the whole WeilConjectures source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for quotient/complete in either order and
  `IsAdicComplete` next to quotient or ⧸ found completion lifting maps,
  power-series quotient constructions, and derived-completeness comparisons.
  None is this theorem. The name `quotient_complete_local` has no collision.

There are no new definition nodes or dependency modules to audit, no private
copies of notions, and no hollow definitions. The only theorem proof is `sorry`.
The original signature was correct and was left verbatim unchanged, including
its identical `lean.statement` record (checked by exact string comparison).

Mismatches repaired: the theorem docstring previously summarized the proof in
one sentence and omitted the explicit finite generator, canonical-map
bijectivity, identification of powers and reduction maps, and dependency-node
names required by H8. I expanded it to the node's four proof steps. The standard
copyright/license/authorship header from the example module was missing and was
added. The unused import `LocalRing.RingHom.Basic` was removed: the surjective
local-ring theorem is already imported through `MaximalIdeal.Basic` and its
`Defs` dependency. No mathematical statement, hypothesis, definition, node
field, or proof was changed.
