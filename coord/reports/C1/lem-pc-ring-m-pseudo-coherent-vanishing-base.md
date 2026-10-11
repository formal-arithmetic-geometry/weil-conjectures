## Worker report

`DerivedCategory.IsMPseudoCoherent` defines the notion in the item. The theorem
`DerivedCategory.isMPseudoCoherent_of_homology_vanishes` states its zero-complex base case.

The commutative ring $R$ is `{R : Type v} [CommRing R]`, with the derived category size
convention `[HasDerivedCategory.{v} (ModuleCat.{v} R)]`; $m$ and $C$ are the binders
`(m : ℤ) (C : DerivedCategory (ModuleCat.{v} R))`. The sole hypothesis, vanishing
of $H^i(C)$ for every $i\ge m$, is `hC : ∀ i : ℤ, m ≤ i → IsZero
((homologyFunctor (ModuleCat.{v} R) i).obj C)`. The conclusion is exactly
`IsMPseudoCoherent m C`.

Inside the definition, the bounded complex is `E` with lower and upper bounds
`E.IsStrictlyGE a ∧ E.IsStrictlyLE b`; finite freeness of every term is
`∀ i, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)`. Its morphism in the derived
category is `f : Q.obj E ⟶ C`. The cohomology isomorphisms above $m$ are
`∀ i, m < i → IsIso ((homologyFunctor ... i).map f)` and degree-$m$ surjectivity is
`Epi ((homologyFunctor ... m).map f)`, equivalent to surjectivity in `ModuleCat`.

Dependency: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
`DerivedCategory.Q`; `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`DerivedCategory.homologyFunctor`. The new definition uses Mathlib's cochain complex,
strict support predicates, and `Module.Free`/`Module.Finite` rather than copies.

Edge cases: $m$ ranges over all integers, including zero and negative values; the zero
complex is bounded and finite free even over the zero ring, so a zero derived object and
arbitrary vanishing tails remain included. No nonempty degree range is assumed.

Searches: `msearch.py leanfinder` for the full bounded finite-free approximation returned
T-structure and factorization results, no match; `msearch.py loogle` for
`IsMPseudoCoherent, MPseudoCoherent` returned unknown identifier; `msearch.py grep`
for pseudo-coherence in Mathlib/Algebra/Homology returned no match. `rg` over
`WeilConjectures` found only an unrelated prose occurrence; `rg` over `lean/Sheaf`
found none. `rg` over `dag/nodes` and `blueprint_refs.py search 'm-pseudo-coherent'`
found uses of the phrase but no definition node. `rg` for the item id in
`WeilConjectures` returned none.
`msearch.py leansearch` for the full notion returned Internal Server Error; its
unavailability is recorded on the new node.

Node fault: the item's unchanged `source.place` cites Tag 064W for Lemma 15.66.5.
The Stacks Project identifies that lemma as Tag 064U; Tag 064W is Lemma 15.66.7.
The definition is Definition 15.66.1, Tag 064Q.

## New nodes

`def-pc-ring-m-pseudo-coherent` records the exact notion from Stacks, More on Algebra,
Definition 15.66.1 (Tag 064Q), part (1). Search results above show no Mathlib,
source-repository, Sheaf-library, or DAG definition of it. Its sole dependency is
`def-weil-abstract-derived-category`, the Mathlib derived category leaf.

## Earlier second reading (a previous round; superseded)

Pending independent reading by the second worker assigned to this sandbox. This worker
has not supplied a second-reading verdict.


## Second reading by C1

Read the item and its proof, the new definition node, both delivered modules, and the
Mathlib leaf `def-weil-abstract-derived-category` independently. The Lean states exactly
the node, with the repairs below. There are no dependency replacement modules and no
statement correction: the mathematical node statement is already correct.

Object/hypothesis/conclusion checklist:

- Ring R: `{R : Type u₁} [CommRing R]` in the theorem; corresponding `u` in the
  definition. Stacks Conventions, lines 51–53, explicitly makes rings commutative
  with identity and includes the zero ring. Verdict: exact, no extra ring hypothesis.
- Integer m: `(m : ℤ)`. Verdict: every integer, same quantifier order as the node.
- Abelian category of R-modules: `ModuleCat.{v₁} R`, with its Mathlib abelian instance.
  Verdict: the actual module category, no finiteness or Noetherian assumption.
- D(R), its object C and chosen morphism universe:
  `[HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]` and
  `(C : DerivedCategory (ModuleCat.{v₁} R))`. Opened Basic.lean:74–98:
  `HasDerivedCategory` chooses a localization, `DerivedCategory` is that localization,
  and `Q` is its localization functor. The instance is the dependency's explicit
  size convention, not an additional mathematical condition. Verdict: exact after repair.
- Sole vanishing hypothesis: `hC : ∀ i : ℤ, m ≤ i → IsZero
  ((homologyFunctor (ModuleCat.{v₁} R) i).obj C)`. Opened HomologySequence.lean:29–41:
  this functor factors cohomology of complexes through Q. `IsZero` means the module
  is zero categorically. Verdict: exactly every degree at least m, including m.
- Conclusion: `IsMPseudoCoherent m C`. Opened its full definition, not merely the name.
  Verdict: exactly the notion spelled out inline in the item.
- Definition witness: `∃ (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)`;
  `E.IsStrictlyGE a ∧ E.IsStrictlyLE b` means terms outside a finite interval are zero
  (read Embedding/CochainComplex.lean). Verdict: a bounded complex, not merely
  bounded cohomology.
- Each term finite free: `∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)`.
  Verdict: exactly finite free, allowing rank zero.
- Derived morphism: `∃ f : Q.obj E ⟶ C`. Verdict: an arbitrary derived morphism,
  with the correct source and target, not an extra chain-map requirement.
- Isomorphisms: `∀ i : ℤ, m < i → IsIso ((homologyFunctor ... i).map f)`.
  Verdict: exactly above m; no isomorphism demanded in degree m.
- Surjection: `Epi ((homologyFunctor ... m).map f)`. Opened
  ModuleCat/EpiMono.lean:50 (`epi_iff_surjective`); verdict: exactly surjective at m.

Source check: read /home/ubuntu/c1-stacks-review/more-algebra.tex at
`definition-pseudo-coherent` (Tag 064Q, part 1), `lemma-pseudo-coherent` (064U),
and `lemma-recognize-pseudo-coherent` (064W, part 1), with tags/tags open.
064W states this vanishing lemma verbatim. The new node's statement is exactly
064Q(1); its objects and both cohomology clauses match its module. Its dependency
is the correct derived-category Mathlib leaf. Searched definition nodes for
m-pseudo-coherence/064Q: no existing definition node. The other pseudo-coherence
nodes concern all m or schemes and do not define this cutoff notion. New-node
fields, creation item, source, blueprint ancestry, and search records satisfy §5.

Edge cases: m=0 and negative m are included; zero derived objects, zero modules,
rank-zero free modules, and the zero ring are allowed. No nonempty interval, index
family, characteristic restriction, field hypothesis or scheme is involved.
Ring, module-carrier and localization-morphism universes are now independent;
the prior same-universe restriction is removed. All universe/term binders are explicit.

Independent searches (msearch.py): LeanFinder query “finite free approximation of a
complex inducing isomorphisms in high degrees and epimorphism at the cutoff” returned
complex factorizations and truncation epimorphisms, no matching notion or theorem.
Loogle `"pseudo"` returned compiler pseudo-arrays and bicategorical pseudofunctor
notions, no pseudo-coherence. Mathlib grep `pseudo.?coher|coherent.*complex` returned
zero hits. LeanSearch query “derived category pseudo coherence from zero cohomology
in high degrees” failed with Internal Server Error; no negative conclusion is drawn
from that unavailable service. Independent rg of WeilConjectures and lean/Sheaf
found only the unrelated DirectImage.lean prose occurrence. Upstream name index has
no item-id match. Existing worker searches remain in searches.jsonl.

Mismatches repaired: both modules had tied ring, module and localization universes;
separated them. The theorem docstring wrongly replaced the valid tag 064W by 064U;
restored 064W(1), corrected its lemma number to 15.66.7 and expanded the zero-complex
proof step by step. The repository node's mixed lemma-number/tag metadata remains
unchanged, since its tag and mathematical statement identify the right result.
Updated both lean.statement fields verbatim to the final signatures. The worker
report above describes the original version; this section records these corrections.
No hollow definitions: the definition has an explicit existential body. The sole
theorem remains `by sorry`; nothing is proved. All declaration docstrings have their
own blueprint id and source. Compilation checks both modules together in dependency
order. Distinct universe names between modules accommodate the supplied combining tool.
