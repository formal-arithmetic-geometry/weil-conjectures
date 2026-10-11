## Worker report

Module: `Sheaf.RingTheory.LocalizationFiniteGlobalDimension`.
Declaration: `Ring.localization_preserves_projective_and_global_dimension`.
It states all parts of the node as one conjunction; its only proof is `sorry`.
No statement correction, new node, or dependency module is needed.

Source checked: Stacks Project, Algebra, Lemma 00O8,
https://stacks.math.columbia.edu/tag/00O8 . The local literature checkout has no
`stacks-project/algebra.tex`, so the source was read at the official tag page.
Its two assertions and proof agree with the node. The final inequality is the
node's explicit consequence of assertion (2).

Hypotheses and clauses:

- The commutative ring is `(R : Type u) [CommRing R]`.
- Its multiplicative subset is `(S : Submonoid R)`; the ring of fractions is
  `Localization S`, with its canonical commutative ring structure.
- The nonnegative integer is `(n : ℕ)`.
- An arbitrary R-module is `M : ModuleCat.{max u v} R`. There is no finite-generation
  restriction. Independent universes `u v` are explicitly declared; using `max u v`
  includes the ring's universe and permits arbitrarily large modules as v varies.
- Clause (1)'s hypothesis is `ModuleCat.HasProjectiveResolutionLE M n`, the dependency's
  exact resolution with projective terms and zero terms above n. Its conclusion is
  the same predicate and bound on `ModuleCat.of (Localization S) (LocalizedModule S M)`.
  Thus the object is the actual module of fractions, without a private definition or
  replacement by the Ext-vanishing projective-dimension predicate.
- Clause (2) is the implication from `HasGlobalDimensionLE R n` to
  `HasGlobalDimensionLE (Localization S) n`, both at module universe `max u v`.
  The recorded definition quantifies over every module, not only finite modules.
- The 'in particular' clause quantifies over `h : HasFiniteGlobalDimension R` and
  concludes `∃ hS : HasFiniteGlobalDimension (Localization S),
  globalDimension (Localization S) hS ≤ globalDimension R h`.
  The existential proof hS is needed because the recorded minimum definition takes
  its finiteness witness as an argument. This asserts both finiteness and the inequality.

Dependencies read and used:

- `def-weil-pbc-finite-global-dimension`: module `Sheaf.RingTheory.GlobalDimension`;
  `ModuleCat.HasProjectiveResolutionLE`, `Ring.HasGlobalDimensionLE`,
  `Ring.HasFiniteGlobalDimension`, and `Ring.globalDimension`. Their full definitions
  and docstrings were read. The module is imported directly.
- `def-weil-pbc-module-localization`: module
  `Mathlib.Algebra.Module.LocalizedModule.Basic`; `LocalizedModule`, the quotient of
  pairs, with its localization module structure. Imported directly.
- `def-weil-pbc-projective-module`: Mathlib leaf, no Lean record needed;
  `Module.Projective` in `Mathlib.Algebra.Module.Projective` was read with its docstring.
  Used through `HasProjectiveResolutionLE` and its `ProjectiveResolution` terms, via
  `Mathlib.Algebra.Category.ModuleCat.Projective` imported by the definition module.

Edge cases checked before writing: n = 0 asserts preservation of projectivity and
of global dimension zero. The zero module has a zero resolution. The zero ring and
submonoids containing zero are permitted; their localizations are zero rings, whose
modules are zero. S = {1} gives the original ring and module up to canonical
isomorphism. No domain, nonzero, Noetherian, or finite-generation hypothesis occurs.
No independent test-module universe below u is used. The same module universe in
source and target lets any localized-ring module be restricted to R as in the proof.

Searches for an existing statement:

- `msearch.py leanfinder "localization preserves finite global dimension and projective
  resolution length"`: eight hits on Ext-defined projective dimension, no exact match.
- `msearch.py loogle "LocalizedModule, Module.Projective"`: projectivity of localized
  modules and a maximal-localization criterion only; the former is the n = 0 ingredient.
- `msearch.py grep "globalDimension|HasGlobalDimension|localiz.*ProjectiveDimension"`:
  four hits in `Mathlib/RingTheory/LocalProperties/ProjectiveDimension.lean`; read the
  full file. `ModuleCat.localizedModule_hasProjectiveDimensionLE` uses Mathlib's
  Ext-vanishing predicate, not the recorded resolution predicate, and gives no global
  dimension assertion. `ModuleCat.localizedModule` and its docstring were also read.
- `msearch.py leansearch "localization preserves finite global dimension"`:
  unavailable (Internal Server Error); the other search services worked.
- `rg` in `WeilConjectures` and `lean/Sheaf` for global dimension and localization of
  resolution bounds: the landed definitions and other global-dimension lemmas only;
  no localization statement. Searching the exact node id upstream gave no hit.
  No duplicate declaration name or notion was found.

Validation: server `scompile.py` compiled the 49-line module cleanly (exit 0, 1.3 s),
with no warnings. The module docstring records all four proof steps of the DAG.

## Second reading by C1

Independent reader; opened the sandbox node and module, all three statement
 dependency nodes, and their declaration sources. No mathematical mismatch was
found. The Lean and node record are retained; this second-reading section is
added to the report.

Source: read the actual Stacks `algebra.tex`, `lemma-localize-finite-gl-dim`
(statement and proof, current lines 24549–24571), at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
and https://stacks.math.columbia.edu/tag/00O8. The local literature checkout
contains no algebra.tex. The chapter's `section-conventions` explicitly says
rings are commutative with identity and includes the zero ring. There is no
standing Noetherian, domain, characteristic, or finite-generation assumption.
Definition 00O6 (https://stacks.math.columbia.edu/tag/00O6) uses a uniform bound
on resolutions of all modules and its minimum. The node's additional final
inequality follows by applying 00O8(2) at that minimum.

Objects, hypotheses, and conclusion clauses matched individually:

1. Commutative ring R with identity: `(R : Type u) [CommRing R]`.
   Verdict: exact, including the zero ring under the source conventions.
2. Multiplicative subset S containing 1: `(S : Submonoid R)`.
   Verdict: exact; no exclusion of 0 or other additional condition.
3. Ring of fractions: `Localization S` with its canonical ring and algebra
   structures. Verdict: exact, rather than an arbitrary unrelated ring.
4. Nonnegative integer n: `(n : ℕ)`. Verdict: exact, including n = 0.
5. Arbitrary R-module M: `∀ M : ModuleCat.{max u v} R` in the first conjunct.
   Verdict: exact; modules have no finiteness or nonzero assumption. The module
   universe contains the ring universe and can be arbitrarily large.
6. Hypothesis of (1): `ModuleCat.HasProjectiveResolutionLE M n`.
   Opened GlobalDimension.lean: this is an existential `ProjectiveResolution M`
   whose terms above n are `IsZero`. Opened Mathlib's Preadditive/Projective/
   Resolution.lean: it has projective terms and a quasi-isomorphism to M in
   degree zero, hence the exact augmented sequence of the node. In particular
   the augmentation is epi and exactness at degree n gives its left end.
   Opened ModuleCat/Projective.lean: `IsProjective.iff_projective` identifies
   these terms with `Module.Projective`, since the ring is small in max u v.
   Verdict: exact, including projectivity of every term and both end pieces.
7. Conclusion of (1): the same predicate with the same n on
   `ModuleCat.of (Localization S) (LocalizedModule S M)`.
   Opened LocalizedModule/Basic.lean: `LocalizedModule` is the fraction quotient,
   `mk m s` denotes m/s, and `mk_eq` is the node's equivalence relation.
   Verdict: exact localization module, with the localized-ring action.
8. Hypothesis of (2): `HasGlobalDimensionLE.{u, max u v} R n`.
   Opened its definition: it quantifies over every module in that universe,
   with the resolution predicate of item 6. Verdict: exact uniform bound.
9. Conclusion of (2): `HasGlobalDimensionLE.{u, max u v} (Localization S) n`.
   Verdict: exact uniform bound with unchanged n and module universe. Restriction
   of scalars of any target module is in the same source module universe.
10. Final clause's hypothesis: `∀ h : HasFiniteGlobalDimension.{u, max u v} R`.
    The dependency defines finiteness as existence of a uniform natural bound.
    Verdict: exact; h is a proof witness, not added data or a stronger hypothesis.
11. Final clause's conclusion: `∃ hS : HasFiniteGlobalDimension ... (Localization S),
    globalDimension ... (Localization S) hS ≤ globalDimension ... R h`.
    Opened both minimum definitions: each is `Nat.find` on that finiteness
    witness. Verdict: exactly target finiteness and the dimension inequality;
    proof irrelevance makes the witness arguments harmless. No clause is lost
    by packaging the assertions as a conjunction.

Edge cases: n = 0 permits a resolution concentrated in degree zero, so (1)
is preservation of projectivity. M = 0 admits the zero complex and minimum
length zero. R = 0 and 0 in S are allowed; localization can be the zero ring
and the module of fractions the zero module. S = {1} is allowed. Empty S is
not a multiplicative subset because it lacks 1; an empty free-module index set
is permitted in the dependency notion of projectivity. Empty schemes do not
occur in this ring statement. No characteristic is restricted. `universe u v`
binds both universes, and `max u v` keeps localization in the same module
universe without a vacuous small test-module quantifier. No variable is unbound.

Independent searches (different wording from the first reader):

- msearch leanfinder: "bounded projective resolutions over a ring of fractions
  imply global homological dimension bound". Eight hits, all Ext-defined
  projective dimension facts, no global-dimension/localization statement.
- msearch loogle: `Localization, ProjectiveResolution` returned an unknown
  identifier diagnostic, so it was not treated as a valid absence result.
  Repeated with quoted `"LocalizedModule", "Projective"` (result below).
- msearch grep: `finite global|global_dimension|localizedModule_hasProjectiveDimensionLE`.
  Three hits, all in LocalProperties/ProjectiveDimension.lean. Opened its
  `localizedModule_hasProjectiveDimensionLE` and inequality declarations:
  they concern Mathlib's Ext-based predicate and Shrink localization, and
  supply neither the recorded resolution predicate nor the global bound.
- Direct rg in the project's lean/Sheaf, upstream WeilConjectures, and Mathlib
  Algebra and RingTheory for globalDim, GlobalDimension,
  HasProjectiveResolutionLE, and the full proposed declaration name. Only
  the project's canonical definitions and different global-dimension lemmas
  occurred; no exact existing statement or duplicate declaration.

H4/H5/H6/H8/H9: all dependency notions are used directly. No new node or
 dependency module is delivered, so H12/H13 do not apply. No statement correction
exists or is needed, so citer correction checks do not apply. No definition or
private copy is added; the sole theorem proof remains `sorry`. Both docstrings
name 00O8 and the blueprint id, and the theorem docstring follows all four node
proof steps, including exactness at the ends, projectivity, restriction/localizing
back, and the minimum argument. Both imports are used. Namespace, topic path,
explicit universes, and line lengths follow the conventions. The recorded
`lean.statement` was compared with the file signature verbatim.

The valid quoted Loogle query returned seven hits: projectivity of localized
modules (the n = 0 ingredient), preservation of projective objects, the
Ext-defined localization bounds, and finite Noetherian local criteria. None
states all clauses of this node. Second-reader scompile: exit 0, compiled in
1.2 seconds, no errors or warnings. Automated text comparison confirms the
node signature is verbatim and every Lean line is at most 100 characters.
