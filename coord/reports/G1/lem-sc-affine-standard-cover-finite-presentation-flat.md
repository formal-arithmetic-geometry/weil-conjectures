## Worker report

The module `lean/Sheaf/RingTheory/FinitePresentationAndFlatOfFiniteFreeStandardCover.lean`
states `Module.finitePresentation_and_flat_of_finite_free_standard_cover`, with one
`sorry` proof and no definitions or other theorems. No node correction, new node,
or dependency replacement is needed. Only the item's `lean` field changes.

Clause-by-clause correspondence:

- A commutative ring `R`: `{R : Type u} [CommRing R]`.
- An `R`-module `N`: `{N : Type v} [AddCommGroup N] [Module R N]`.
  The universes `u` and `v` are separately declared, so the module need not have the
  same size as its ring. All variables and universes are explicitly bound.
- Finitely many elements `f_1,...,f_r`: `{r : ℕ} (f : Fin r → R)`.
  An arbitrary natural length includes zero. The zero-based enumeration merely
  reindexes the same list. Stating the implication for every such witness is
  equivalent to an implication whose premise asserts that a witness exists.
- Generating the unit ideal: `hspan : Ideal.span (Set.range f) = ⊤`.
  Taking the range forgets only repetitions; repetitions do not change the ideal.
- Each localization `N_{f_i}`: `LocalizedModule.Away (f i) N`, over
  `Localization.Away (f i)`. These are the standard localizations at powers of
  `f i`, with Mathlib's canonical localized-ring module structure.
- Each localization is finite free: `hfree : ∀ i : Fin r,
  Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) N) ∧
  Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) N)`.
  `Module.Finite` means finitely generated and `Module.Free` means a basis exists;
  together these mean finite free. No common rank or nonzero rank is imposed.
- The first conclusion is `Module.FinitePresentation R N`.
- The second conclusion is `Module.Flat R N`, joined by `∧` to the first.
  The ring-map part of the flatness dependency is irrelevant to this module claim.

Dependency declarations read and used:

- `def-weil-pbc-module-localization-away`: its `mathlib_match` is
  `LocalizedModule.Away`, in `Mathlib.Algebra.Module.LocalizedModule.Basic`.
  Read the complete protected abbreviation and its docstring at lines 1473–1478:
  it is `LocalizedModule (Submonoid.powers x) M`.
- `def-sc-finitely-presented-module`: its `mathlib_match` is
  `Module.FinitePresentation`, in `Mathlib.Algebra.Module.FinitePresentation`.
  Read the class and docstring at lines 63–69: a finite generating set with
  finitely generated relation kernel, equivalent to the stated finite presentation.
- `def-weil-pbc-flat-ring-map`: the usable module clause of its `mathlib_match` is
  `Module.Flat`, in `Mathlib.RingTheory.Flat.Basic`. Read the complete class and
  docstring at lines 106–115 and its preservation-of-injections API. Also read
  `RingHom.Flat` in `Mathlib.RingTheory.RingHom.Flat` at lines 25–29; no ring map
  is asserted here and it is not imported.
- Finite free uses the already available notions `Module.Free` from
  `Mathlib.LinearAlgebra.FreeModule.Basic` (class and docstring at lines 42–44),
  carried by `def-weil-pbc-free-module`, and `Module.Finite` from
  `Mathlib.RingTheory.Finiteness.Defs` (docstring and full class at lines 116–119).
  These declarations are available transitively through the finite-presentation
  import. No private notion of finite freeness is introduced.

Source checked: the local literature checkout is absent on this machine, so
opened [Stacks Tag 00NX](https://stacks.math.columbia.edu/tag/00NX) directly.
Its proof of (7) → (4) → (5) → (1) supplies exactly finite presentation and
flatness from finite local freeness. Read the two descent signatures in Mathlib:
`Module.FinitePresentation.of_localizationSpan` and
`Module.flat_of_localized_span`. The latter uses flatness over the original ring,
so the docstring explicitly explains restriction of scalars along the flat
localization map. The three numbered DAG proof steps and their named dependencies
are all retained in the theorem's natural-language proof docstring.

Edge cases checked before writing:

- `r = 0`: the empty range spans the zero ideal, so `hspan` can hold only in the
  zero ring; modules over the zero ring are zero, hence finitely presented and
  flat. The empty case is included without a nonempty-cover hypothesis.
- `N = 0`: all localized modules are finite free of rank zero, and both conclusions
  hold. Neither the module nor any localization is assumed nontrivial.
- `r = 1`, `f 0 = 1`: localization is the original module, and the statement is
  finite free implies finitely presented and flat.
- Entries equal to zero or nilpotents give zero localizations; they cause no
  problem provided the whole list still generates the unit ideal.
- Repeated entries and different finite ranks are allowed. For example the two
  idempotents of a product ring give components with possibly different ranks.
- No Noetherian, domain, characteristic, or separatedness condition is needed or
  imposed. There is no mathematical dispute.

Searches made for an existing combined statement:

- `msearch.py ... leansearch "finite free localizations on a unit ideal cover imply
  finitely presented flat module"`: service unavailable (Internal Server Error),
  reported without claiming a no-match search result.
- `msearch.py ... leanfinder "finite standard open cover free localizations implies
  module finitely presented and flat"`: eight hits, mostly algebra
  finite-presentation descent, plus `Module.flat_of_localized_span`; none state
  the combined module theorem with finite-free hypotheses.
- `msearch.py ... loogle "Module.Free, Module.FinitePresentation"`: five hits,
  including `Module.finitePresentation_of_free_of_surjective`,
  `Module.FinitePresentation.equiv_quotient`, and results on freeness over local
  rings; none is this cover criterion.
- `msearch.py ... grep "of_localizationSpan|flat_of_localized_span|finitePresentation.*flat"
  RingTheory`: 25 hits, including the separate finite-presentation and flatness
  descent theorems; no combined finite-free-cover theorem.
- `rg -n "finitePresentation.*flat|finite.*free.*local|of_localizationSpan|flat_of_localized_span"
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures
  /home/ubuntu/weil-conjectures-sheaf-G1/lean/Sheaf`: results include descent for
  sections of finite locally free sheaves and ring-equivalence transport with
  rank-at-stalk conclusions, but no declaration with this node's objects and
  hypotheses. The sheaf theorems concern a sheaf and its sections rather than an
  arbitrary module with the given standard-open free cover.
- `rg -n "lem-sc-affine-standard-cover-finite-presentation-flat|finitePresentation_flat_of|finitePresentation_and_flat_of"
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures
  /home/ubuntu/weil-conjectures-sheaf-G1/lean/Sheaf dag/lean_names_upstream.json`:
  no hits. This includes the prescribed node-id search in the source repository.
- The proposed full declaration name was also searched in Mathlib, the source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.

Validation: `scompile.py G1 lem-sc-affine-standard-cover-finite-presentation-flat`
compiled the final module on the server in 1.3 seconds, exit code 0, with no errors
or warnings. The delivery dry run is the final mechanical check; the independent
second reader supplies the second-reading section and delivers.

## Second reading by G1

Independent second reader: I opened the base node, the sandbox node and module,
all three statement dependency nodes, and the actual Mathlib declarations they
record. I also read the two descent theorem signatures and the upstream near
matches below. There are no new definition nodes, dependency replacements, or
statement corrections in this delivery.

The node's complete list, with its Lean rendering and verdict:

1. An arbitrary commutative ring R: `{R : Type u} [CommRing R]`. Exact;
   there is no Noetherian, domain, field, nontriviality, or characteristic assumption.
2. An arbitrary R-module N: `{N : Type v} [AddCommGroup N] [Module R N]`.
   Exact, with independently bound universes u and v.
3. A finite list of ring elements: `{r : ℕ} (f : Fin r → R)`. Exact;
   every finite list has such a length, including zero, and no rank is specified.
   Universal quantification over witnesses gives the same implication as the
   node's existential-cover premise, without choosing a canonical cover.
4. These elements generate the unit ideal: `hspan : Ideal.span (Set.range f) = ⊤`.
   Exact; repetitions and indexing order do not change the generated ideal.
5. For every entry, N localized at f i over R localized at f i is finite free:
   `hfree : ∀ i : Fin r, Module.Finite (Localization.Away (f i))
   (LocalizedModule.Away (f i) N) ∧ Module.Free (Localization.Away (f i))
   (LocalizedModule.Away (f i) N)`. Exact; neither a positive nor a common rank
   is assumed. `LocalizedModule.Away` is the dependency's localization at powers
   of the element, and the scalar action is the canonical localized-ring action.
6. N is finitely presented over R: `Module.FinitePresentation R N`. Exact;
   its finite generators and finitely generated relation kernel are equivalent
   to the dependency's finite free presentation.
7. N is flat over R: `Module.Flat R N`, conjoined with clause 6. Exact;
   I read `Flat` and `lTensor_preserves_injective_linearMap`, so the class gives
   the module clause of def-weil-pbc-flat-ring-map, without imposing a ring map.

Source check: the repository contains the literature index but no algebra.tex.
I fetched the Stacks project's algebra.tex into this item's scratchpad and read
`definition-locally-free`, `lemma-finite-projective` (Tag 00NX), and `lemma-cover`
(Tag 00EO). I also opened https://stacks.math.columbia.edu/tag/00NX. The source
introduces only a ring and module; the finite-free standard-open cover is
precisely finite local freeness, and the cover lemma explicitly equates the cover
condition with the unit ideal. The (7) -> (4) -> (5) -> (1) argument gives both
conclusions without a further standing hypothesis. The Lean statement agrees.

Edge cases: r = 0 forces the zero ring through hspan, and its modules are zero;
the empty spectrum is therefore included. N = 0 and localizations at zero or
nilpotent entries are permitted. The singleton unit cover recovers finite free
implies finitely presented and flat. Different finite ranks on different
components and repeated cover entries are permitted. No restriction on
characteristic or universe is present; finite generation plus freeness means
finite free also over the zero ring. All universes and variables are bound.

Independent searches (different phrasing from the worker):

- Loogle via msearch.py: `Module.Free, Module.Flat, Module.FinitePresentation`:
  successful, zero hits.
- LeanFinder via msearch.py: `A module that becomes finite and free after
  inverting a finite family of elements spanning the unit ideal is flat and
  finitely presented`: successful, eight hits. These include
  `Module.flat_of_localized_span`, algebra finite-presentation descent, and a
  theorem making a finitely presented module free after localization; none
  has the combined finite-free-cover premise and two conclusions here.
- Independent rg in Mathlib, WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json for `finitePresentation.*[Ff]lat`,
  `[Ff]lat.*finitePresentation`, `finite_free_standard_cover`,
  `finite.free.*localizations`, and the proposed full theorem name. I opened
  `Module.finitePresentation_flat_rankAtStalk_of_ringEquiv` (transport along a
  ring equivalence, assuming both desired properties already) and
  `finitePresentation_flat_sections_top_of_isFiniteLocallyFree` (global sections
  of a locally free sheaf). Neither states the arbitrary-module cover criterion.
  Other hits are component results, not this statement. No duplicate name found.

H5/H6/H8/H9: there is no definition or auxiliary result, and the only proof is
`by sorry`. The header, namespace, source and blueprint docstrings, imports,
100-character lines, and explicit binders meet the conventions. The proof
text retains all three DAG steps and their named dependencies. Its additional
restriction-of-scalars explanation is valid (and is not an additional hypothesis).
The node's lean.statement equals the file's signature verbatim. No mathematical
or encoding mismatch was found; no Lean or node changes were needed. The only
second-reader change is this independent review section.

Validation: scompile.py compiled the delivered module, exit code 0 in 1.3 seconds,
with no errors or warnings. Dry run and delivery follow this review.
