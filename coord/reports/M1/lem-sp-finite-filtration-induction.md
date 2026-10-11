## Worker report

The module `Sheaf.CategoryTheory.FiniteFiltrationInduction` states finite-filtration
induction for filtered objects in an abelian category. It defines `restriction` as the
chosen factorization of a filtration-preserving morphism through each target subobject,
and defines `gradedMap` by the induced map on cokernels. The theorem
`finite_filtration_induction` assumes two finite filtrations, a filtered morphism, and
that every graded map is an isomorphism; it concludes that the underlying morphism and
every filtration-step restriction are isomorphisms. The finite hypotheses are rendered
by `hA : A.filtration.IsFinite` and `hB : B.filtration.IsFinite`; the graded-piece clause
by `hgraded : ∀ p : ℤ, IsIso (gradedMap f p)`; and the conclusion by
`IsIso f.hom ∧ ∀ p : ℤ, IsIso (restriction f p)`. The auxiliary existence theorem for
`gradedMap` has a sorry proof, as permitted for stage 2; no definition contains sorry
data.

The dependency declaration used is `CategoryTheory.DecreasingFiltration` and its
associated `FilteredObject`, `FilteredObject.Hom`, `DecreasingFiltration.IsFinite`, and
`DecreasingFiltration.gradedPiece` from `Sheaf.CategoryTheory.Filtration`.

Edge cases checked: integer indices include all filtration positions; finite bounds may
be arbitrary integers (including equal bounds); zero and empty objects are permitted;
no strictness hypothesis is added, and the conclusion includes isomorphisms of all step
maps. The graded map is defined through the cokernel universal property, so no extra
choice of representatives is assumed.

Searches made: `msearch.py leanfinder` for finite filtered-object induction (no exact
match); `msearch.py loogle` for `FilteredObject, gradedPiece, IsFinite` (no exact match);
grep of Mathlib CategoryTheory and Algebra/Homology for filtered abelian objects and
associated graded isomorphism criteria (no match); `rg` of `WeilConjectures` and
`lean/Sheaf` for `finite_filtration_induction` (no existing declaration). The recorded
Mathlib search results in the node likewise found only unrelated ring/module
filtrations and graded-object APIs.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, `A` and `B` are filtered objects in one abelian
category, `f` is a filtration-preserving morphism, and `hA`/`hB` state exactly the finite
bounds required by the node. The universal quantifier over all `p : ℤ` in `hgraded`
expresses isomorphism on every graded piece. The conclusion gives the underlying
isomorphism and each induced filtration-step isomorphism, which is the stated strictness
consequence. The auxiliary `restriction` and `gradedMap` definitions use the dependency's
subobjects and cokernels directly. No hypothesis or edge case is omitted or added.

## Second reading by M1

I independently opened the delivered node and module, the dependency node
`def-sp-filtration`, and every dependency declaration used in
`lean/Sheaf/CategoryTheory/Filtration.lean`. I read Stacks `homology.tex` from
`/home/ubuntu/c1-stacks-review/homology.tex`: Definition 0121
(`definition-filtered`, lines 4667 ff.), the graded functor paragraph before
Lemma 05SP (lines 4948 ff.), and Lemma 0127 (`lemma-characterize-strict`, lines
5018 ff.). The repository's `literature/stacks-project/` copy is absent on this
machine. The section assumes only an abelian category; countable direct sums
are required only for the optional direct-sum realization of `gr`, which this
statement does not use. Lemma 0127 applies its induction to an already bijective
map, but its displayed short-exact-sequence argument proves the node's general
criterion without that assumption: the step maps become isomorphisms first,
and the underlying isomorphism follows at the lower bound.

Clause-by-clause list and verdicts:

- Ambient object: an abelian category `C`, rendered by `{C : Type u}`,
  `[Category.{v} C]`, `[Abelian C]`, with independent declared universes `u v`.
  Exact; no linearity, field, finiteness of Hom sets, or smallness assumption.
- Two objects and decreasing integer-indexed subobject filtrations: `A B :
  FilteredObject C`. The dependency structure has `obj : C` and
  `filtration : DecreasingFiltration obj`; the latter has `step : ℤ →
  Subobject obj` and `antitone_step : Antitone step`. Exact, using the recorded
  dependency rather than a private replacement.
- Finiteness and common ordered bounds: `hA : A.filtration.IsFinite` and
  `hB : B.filtration.IsFinite`. The dependency definition is
  `∃ n m : ℤ, F.step n = ⊤ ∧ F.step m = ⊥`. Equivalent to the node's common
  `n ≤ m`: take the minimum of both whole-object bounds and the maximum of
  both zero bounds and that minimum. Antitonicity propagates both equalities.
  Conversely common bounds witness both predicates. No hypothesis changed.
- A filtration-preserving underlying arrow: `f : Hom A B`, whose fields are
  `hom : A.obj ⟶ B.obj` and `preserves : ∀ i, ∃ lift, lift ≫ target.arrow =
  source.arrow ≫ hom`. This is exactly inclusion of the image in the target
  step, not strictness or an isomorphism assumption.
- Step arrows `F^p φ`: `restriction f p` chooses the factorization in
  `f.preserves p`; uniqueness follows from the monic target inclusion. Exact.
- Graded objects: the dependency's `gradedPiece p` is the cokernel of the
  inclusion `Subobject.ofLE (step (p+1)) (step p)`, hence the specified quotient.
  `exists_gradedMap` asserts the induced quotient arrow and its defining
  projection equation; `gradedMap f p` chooses that arrow. The source cokernel
  projection is epic, so its equation determines the map uniquely. Exact.
- Graded-isomorphism hypothesis: `hgraded : ∀ p : ℤ, IsIso (gradedMap f p)`.
  All integer positions, with the same quantifier order as the node. Exact.
- Underlying-isomorphism conclusion: `IsIso f.hom`. Exact.
- Every step-isomorphism conclusion: `∀ p : ℤ, IsIso (restriction f p)`,
  conjoined with the underlying conclusion. For an underlying isomorphism this
  is equivalent to `φ(F^p A) = F^p B` and implies the stated strictness; no
  additional predicate is needed and no conclusion is lost. Exact.

Edge cases: ℤ is the prescribed index set, so an empty index set is not an
object of this statement. An empty induction interval (`n = m`, including
`n = m = 0`) forces the underlying objects to be zero and is allowed. Zero
objects allow arbitrary finite witnesses, even ones initially in reversed
order; the common-bound argument above still applies. Negative bounds and
`n = 0` are included. No scheme, characteristic, or coefficient ring is
introduced; no empty-scheme or characteristic case is excluded by an extra
assumption. The two ambient universes are unrestricted, and the subobject and
cokernel constructions use the abelian-category dependency's existing API.

Independent searches (different wording from the worker):

- `msearch.py leanfinder`: “In an abelian category a map respecting bounded
  decreasing subobject flags is invertible if maps of consecutive quotients
  are invertible”. Eight results about `ObjectProperty.isoModSerre` and Serre
  classes; none concerns the specified filtered maps or criterion.
- `msearch.py loogle`: `"graded", IsIso`; zero hits, unknown unqualified
  identifier `IsIso`. This query did not establish absence by itself.
- `msearch.py leansearch`: “isomorphism criterion using successive quotients
  of finite flags in an abelian category”; service unavailable (Internal
  Server Error), recorded without claiming a successful search.
- `msearch.py grep` across Mathlib:
  `isIso_of_gr|iso_of_graded|gradedMap|finite_filtration_induction|DecreasingFiltration`;
  zero hits. Direct `rg` on the source's `WeilConjectures`, the project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json` for `DecreasingFiltration`,
  `FilteredObject`, `gradedMap`, the theorem name and isomorphism/filtration
  combinations found only the dependency's filtered-object definitions,
  project uses of them, and unrelated source results about filtration closure,
  spectral-object image filtrations, and stupid truncations. No existing
  theorem or induced-map API for these filtered objects was found.

Mismatches repaired: the restriction and graded-map docstrings lacked source
places; the existence theorem lacked its natural-language quotient-map proof;
its proof is now explained using monicity, compatibility of consecutive
restrictions, and the cokernel universal property. The main theorem docstring
summarized rather than carried the node's three proof steps; it now records
common bounds and the exact diagrams, descending induction with the named
short-five-lemma dependency, and the final underlying/strictness conclusion.
The misleading source parenthesis “Lemma 0127 (Tag 0121)” was corrected to
Lemma 0127's label, with Definition 0121 cited separately. The redundant
`Mathlib.CategoryTheory.Abelian.Basic` import was removed. The `lean.statement`
record now copies the multiline signature verbatim, and `lean.declarations`
lists the auxiliary declarations too. The mathematical statement and existing
correct definitions were retained.

No new definition node or dependency module is needed: the dependency gives
all filtration notions and graded objects; the induced maps are explicitly
introduced by this item's own statement and Step 1. Both definitions have
concrete data (choices from existence proofs), never sorry data; both named
theorems retain only `by sorry` proofs, with source and node proof docstrings.
No variable or universe is unbound. No item statement correction is involved.

Validation: `scompile.py M1 lem-sp-finite-filtration-induction` compiled the
repaired module cleanly (1.1 seconds, exit 0, no warnings). The delivery dry
run printed `OK`: server compilation and the stage-2 preflight both passed.
