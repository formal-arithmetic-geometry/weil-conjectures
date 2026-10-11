## Worker report

The module states the two conclusions of Tag 07P4. It uses `K : Type u` with `[Field K]` and `[CharP K p]`, an index type `A`, and subfields `Kα : A → Subfield K`. Hypotheses `h₁`, `h₂`, and `h₃` render respectively containment of p-th powers, the intersection equality, and directedness. `dmap` and `hdmap` encode the canonical K-linear maps from `Ω[K⁄(ZMod p)]` to `Ω[K⁄Kα]` and their defining action on universal differentials. Conclusion (1) states that an element annihilated by every map is zero. Conclusion (2) states the finite-extension equality, with the generated subfield represented by `Subfield.closure` of p-th powers and the image of `Kα`.

The Kähler differential notion is Mathlib `KaehlerDifferential` (`Mathlib.RingTheory.Kaehler.Basic`), matching `def-weil-pbc-kahler-differentials`; field extensions use `[Field L] [Algebra K L] [FiniteDimensional K L]`, matching `def-pc-field-extension`.

Edge cases checked: arbitrary (including empty) index type, degree-one finite extensions, and subfields containing p-th powers. The theorem is written with the source's empty-intersection convention via set intersections.

Searches: node-provided LeanFinder, LeanSearch, Loogle and grep searches found no existing theorem; Mathlib Kähler differential declarations were used directly.

## Earlier second reading (a previous round; superseded)

The declaration was reread against the node. Each field, characteristic, index-family, containment, intersection, and directedness hypothesis is present. The differential map data and compatibility equation express the universal-property map named in the node. The first conclusion is pointwise kernel vanishing; the second uses `Subfield.closure` for the generated field. No mismatch was found.

## Second reading by C1

Read the actual source in `/home/ubuntu/c1-stacks-review/more-algebra.tex`,
lines 11458ff., `lemma-intersection-subfields`, with the section
`section-p-bases` opening (characteristic p > 0), and the tag table entry
`07P4,more-algebra-lemma-intersection-subfields`. The source introduces no
Noetherian, finite-generation, or nonempty-family assumption. Read the full
item node and both statement dependency nodes and their Mathlib declarations.
There is no statement correction, new node, or dependency module in this delivery.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Prime p: `(p : ℕ) [Fact p.Prime]`. All positive prime characteristics are
  covered, including p = 2; p = 0 and p = 1 are excluded by the source.
- Field K of characteristic p: `(K : Type u) [Field K] [CharP K p]`.
  No perfectness, finite degree over the prime field, or other assumption is added.
- Index collection and subfields: `(A : Type v) (Kα : A → Subfield K)`.
  Both universes are arbitrary and independent; neither finiteness nor
  nonemptiness is required. Subfields, rather than intermediate fields over an
  unrelated chosen algebra structure, are exactly the source's objects.
- K^p: `Set.range (fun x : K => x ^ p)`, the set of p-th powers itself.
- Condition (i): `h₁`, containment of this range in every `Kα α`.
- Condition (ii): `h₂`, equality of this range with `⋂ α : A, (Kα α : Set K)`.
- Condition (iii): `h₃`, for every α and β some γ is contained in their
  intersection. The direction of inclusion and order of quantifiers agree.
- Absolute and relative differential modules:
  `Ω[K⁄(ZMod p)]` and `Ω[K⁄(Kα α)]`. Read
  `def-weil-pbc-kahler-differentials` and its recorded `KaehlerDifferential`
  match in `Mathlib/RingTheory/Kaehler/Basic.lean`: definition at 153,
  universal derivation `D` at 198, and `linearMapEquivDerivation` at 327.
  This last declaration identifies K-linear maps with base derivations and
  gives the exact universal property of the dependency, not another notion.
  Read `Mathlib/Algebra/Algebra/ZMod.lean`: `ZMod.algebra` supplies the
  canonical prime-field algebra structure; its local registration is an alias
  of existing data, with no proof or data hole. `Subfield.toAlgebra` and
  `algebraMap_ofSubfield` (Subfield/Basic.lean:558ff.) give inclusion for Kα.
- Canonical differential maps: `dmap` is K-linear, and `hdmap` says
  `dmap α (D (ZMod p) K a) = D (Kα α) K a` for every α and a.
  These are the maps explicitly introduced by the node. Universal derivations
  generate the source module, so this specifies their unique value. Their
  existence is unconditional by the universal property: the relative
  derivation kills the prime field. No arbitrary substitute map is assumed.
- Conclusion (1): the first conjunct quantifies over every ω and says that
  `∀ α, dmap α ω = 0` implies `ω = 0`, precisely zero intersection of kernels.
- Finite extensions in (2): `∀ (L : Type w) [Field L] [Algebra K L]
  [FiniteDimensional K L]`. Read `def-pc-field-extension` and its recorded
  `Algebra` signature (Algebra/Defs.lean:95); the ring map is `algebraMap K L`.
  Read `FiniteDimensional` (FiniteDimensional/Defs.lean:75), the standard
  finite vector-space dimension condition. No separability assumption is added.
- Conclusion (2): the second conjunct states equality of the set of p-th
  powers of L with the intersection of the generated subfields
  `Subfield.closure (Set.range (fun x : L => x ^ p) ∪
  (algebraMap K L '' (Kα α : Set K)))`. Read `Subfield.closure`
  (Subfield/Basic.lean:294) and `mem_closure`: this is exactly the smallest
  subfield containing L^p and the image of Kα. Equality is in L, not K.

Edge cases: empty A is allowed; `h₂` then forces K^p = K. A perfect field
has zero absolute differentials, and every finite extension of a perfect
field is perfect, so both conclusions have the correct empty-intersection
meaning. Singleton families force Kα = K^p. The zero differential satisfies
(1). Degree-one extensions reduce (2) to h₂, and inseparable finite
extensions are included. A zero ring cannot be a field and is outside the
source's scope. Schemes and n do not occur. Universes u, v, w are all bound:
the theorem is polymorphic in w and does not constrain extension fields to
the universe of K. There is no test-algebra quantification whose universe
could make a hypothesis vacuous.

Independent searches actually run through msearch.py:

- LeanSearch: “In positive characteristic a decreasing family of subfields
  detects nonzero Kahler differentials and remains separating after finite
  field extensions”: HTTP Internal Server Error, recorded UNAVAILABLE,
  not a negative result.
- Loogle: `KaehlerDifferential, Subfield`: zero hits.
- LeanFinder: “A filtered intersection of intermediate fields containing the
  Frobenius image detects differential forms in characteristic p”: eight
  hits, concerning characteristic-zero differential field structures or
  perfectClosure; none states either clause of this lemma.
- Mathlib grep: `intersection_subfields|iInf.*[Ff]robenius|[Ff]robenius.*iInf`:
  zero hits. Direct rg over the entire upstream WeilConjectures tree,
  repository lean/Sheaf, and dag/lean_names_upstream.json for
  `intersection_subfields|intersection-subfields-differentials|subfields.*differential|differential.*subfields`
  found only the citation in DetectNonPthPower.lean. A further field-theory
  grep for KaehlerDifferential/Frobenius/Subfield found no existing theorem.
  Existing notions are reused; no duplicate definition is introduced.

Mismatches repaired: H8, the theorem docstring gave no natural-language proof
and no precise source place. Added the full five-step node argument, including
nonemptiness derived from a nonzero differential, the tower induction, both
primitive cases, and the directedness repair of the source's non-direct sum.
Added a source/blueprint docstring to the local instance and the standard
copyright/license header. Moved the module docstring immediately after imports.
Replaced the unused IntermediateField import by Subfield.Basic (the notion
actually used) and removed the unused TensorProduct scope. The theorem's
signature is unchanged and verified byte-for-byte against lean.statement.
No mathematical statement was corrected, no declaration was proved, and the
only sorry is the named theorem, now supplied with its complete proof outline.
All lines are at most 100 characters and all variables/universes are bound.

Validation: prescribed scompile.py server compilation passed in 1.4 seconds,
exit code 0, with no errors or warnings. Dry-run and delivery checks follow.

## Reviewer fix (R-isd1104, stage 2)

Statement restated without changing its content: the assumed maps `dmap`/`hdmap` were replaced by Mathlib's canonical `KaehlerDifferential.map (ZMod p) (Kα α) K K` (the map with `D a ↦ D a`, checked by `simp`); the subfields are `IntermediateField (ZMod p) K` as in the landed sibling lem-weil-pbc-intersection-subfields-subspace (every subfield contains the prime field), with (ii) as `K^p = ↑(⨅ α, Kα α)` and (iii) as `Kα γ ≤ Kα α ⊓ Kα β`; the index type is implicit `{ι : Type v}` with no `Nonempty` (the node has none; empty ι gives `⨅ = ⊤`, i.e. K perfect, where both clauses hold). Conclusion (2) unchanged.
