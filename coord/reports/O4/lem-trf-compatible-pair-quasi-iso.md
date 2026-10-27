## Worker report

The module `Sheaf.Algebra.Homology.CompatiblePairQuasiIso` states the unbounded
compatible-pair criterion, with theorem proofs postponed by `sorry`. Its helper
`HomologicalComplex.compatiblePair_condition` states the chain-map identity into
cycles already implicit in the node's construction of `e^n`.
`HomologicalComplex.compatiblePairMap` is real data: `pullback.lift` of precisely
`a.f n` and `P.toCycles n (n + 1)`, using that identity. No arbitrary map or
existence choice replaces the canonical map. The helper identity and canonical
map belong to this node's specified construction and are listed in
`lean.declarations`; they are not independent new mathematical notions.

Hypotheses and clauses, in node order:

- An arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  The object and morphism universes remain independent.
- The integer-indexed cochain complexes are `{P X : CochainComplex C ℤ}`;
  their chain map is `(a : P ⟶ X)`.
- `Z^n(K)` is Mathlib's `K.cycles n`, the kernel represented by `K.iCycles n`.
  `z^n` is `HomologicalComplex.cyclesMap a n`.
- The differential into cycles is `K.toCycles n (n + 1)`.
- `T^n` is literally `pullback (X.toCycles n (n + 1)) (cyclesMap a (n + 1))`.
  Its first factor is `X.X n`, its second `P.cycles (n + 1)`, and the common
  target is `X.cycles (n + 1)`.
- `e^n` is `compatiblePairMap a n`. Its compatibility identity is
  `a.f n ≫ X.toCycles n (n + 1) = P.toCycles n (n + 1) ≫ cyclesMap a (n + 1)`.
- Epicity of every `e^n` is the sole additional hypothesis
  `(h : ∀ n : ℤ, Epi (compatiblePairMap a n))`.
- The conclusion quantifies over every `n : ℤ` and states
  `Epi (a.f n)`, `Epi (cyclesMap a n)`, and `IsIso (homologyMap a n)`.
- The final `QuasiIso a` states the node's explicit resulting
  quasi-isomorphism assertion. Together with the termwise epicity above it
  gives exactly a degreewise epimorphic quasi-isomorphism.
- There is no boundedness, projectivity, enough-projectives, projective-cover,
  derived-category-size, or lift-on-Hom assumption.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`, including its full class definition.
- `def-weil-abstract-derived-category`: its recorded module is
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. Its `DerivedCategory` and
  `HasDerivedCategory` docstrings were read. The statement uses that module's
  actual complex/cohomology/quasi-isomorphism interface:
  `CochainComplex`, `HomologicalComplex.cycles`, `toCycles`, `cyclesMap`,
  `homologyMap`, and `QuasiIso`. No derived object occurs, so no localization
  size hypothesis is required. The signatures and docstrings of these
  definitions were read in `ShortComplex.HomologicalComplex` and `QuasiIso`.
- Proof dependency `lem-sp-abelian-refinements`: the declarations
  `CategoryTheory.epi_iff_surjective_up_to_refinements`,
  `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`, and
  `CategoryTheory.Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements`
  were read in `Mathlib.CategoryTheory.Abelian.Refinements`, imported for proofs.
- Proof dependency `lem-weil-pbc-abelian-exact-epi-cokernel`: the used clause is
  `CategoryTheory.ShortComplex.Exact.gIsCokernel` in
  `Mathlib.Algebra.Homology.ShortComplex.Exact`, imported for proofs. Its full
  signature supplies a cokernel cocone from exactness and epicity.

Source checked: `literature/stacks-project/derived.tex`,
`lemma-subcategory-left-resolution` (Tag 05T7), especially the displayed
compatible-pair pullback and the verification of the downward induction step;
`lemma-projective-resolutions-exist` (Tag 0646), clause (3). The source existence
result assumes enough projectives and boundedness. The present node deliberately
extracts just the verification criterion, with its own six-step
refinement argument, which needs neither. The theorem docstring reproduces
all six proof steps, including both inverse laws on cohomology. The source's
bounded resolution-existence statement is not substituted for this criterion.

Edge cases checked mathematically before writing:

- The identity of any complex has an invertible compatible-pair map:
  the second pullback leg is an identity. Thus unbounded complexes are covered.
- For `X = 0`, the hypothesis says the differentials of `P` surject onto the
  next cycles; this is acyclicity, exactly what the conclusion requires.
- For `P = 0`, the hypothesis forces every cycle of `X` to vanish. The next
  cycle vanishes too, so every differential is zero, and then every term
  vanishes. The strong degreewise-epic conclusion remains valid.
- For zero differentials in both complexes, the pullback is a product of a
  target term and the next kernel of `a`. Epicity forces each `a.f n` epic
  and each next kernel zero, hence `a.f n` invertible, as cohomology requires.
- Zero complexes and zero categories cause no extra nonemptiness restriction.
- All degrees, including negative degrees and zero, are quantified uniformly;
  no induction starting from a top degree enters the criterion.

Searches executed on 2026-10-24 (the wrapper log records actual queries):

- LeanFinder via `msearch.py`, query “Epimorphic maps from each source term to
  the pullback of a target term and source cycles imply a degreewise epimorphic
  quasi-isomorphism”: eight hits, including `epi_homologyMap_of_epi_cyclesMap`,
  `instEpiOpcyclesMapOfF`, and `degreewiseEpiWithInjectiveKernel`; no exact match.
- Loogle via `msearch.py`, query `"cyclesMap", CategoryTheory.Epi`: seven hits.
  `ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi` requires an
  isomorphism on cycles, rather than deriving just epicity from this
  compatible-pair hypothesis, so it does not state the node.
- LeanSearch via `msearch.py`, query “A chain map surjecting onto each pullback
  of target terms and source cycles over target cycles is a quasi-isomorphism”:
  eight hits, general quasi-isomorphism definitions and criteria, no exact match.
- Mathlib grep via `msearch.py`, regex
  `pullback.*[Qq]uasi|[Qq]uasi.*pullback|dToCycles|toCycles`, subdirectory
  `Algebra/Homology`: 25 hits, principally cycle/cohomology constructions;
  no compatible-pair criterion.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `compatiblePair|compatible_pair|dToCycles|toCycles.*pullback|pullback.*cyclesMap`:
  no hits. Direct item-id search in `lean/WeilConjectures`: no hits.
- Direct name-clash search in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `compatiblePairMap`,
  `compatiblePair_condition`, and `quasiIso_of_epi_compatiblePairMap`: no hits.

No statement correction, new definition node, dependency repair, or
STATEMENT-DISPUTED flag is needed. The original node is changed only in `lean`.
Server compilation using the prescribed `scompile.py` passed in sandbox mode
(1.1 seconds) and library mode (1.0 seconds), with no errors or warnings.

## Second reading by O4

This is the worker's separate rereading, not a claim of an independent agent
review; the dispatch brief assigns independent review to the maintainer and
forbids starting agents. I reread the original node and the completed module.
The pullback order is target term first, source cycles second; its shared base
is target cycles in degree `n + 1`. The compatibility theorem has exactly the
orientation `pullback.lift` needs in diagrammatic Lean composition. The map
uses the actual component and differential, and its only proof parameter is
the chain-map identity, not the criterion being concluded. The sole extra
hypothesis asserts epicity of this prescribed map for every integer. Each
of the three per-degree conclusions is present and the final quasi-isomorphism
uses Mathlib's existing definition. Universes are explicitly bound and no
boundedness or projectivity sneaks into the interface. The two theorem
proofs remain `sorry`, and the definition itself contains no `sorry`.
The identity, zero-source, zero-target, and zero-differential checks above
agree with the Lean signature. No mismatch was found on this rereading,
and no statement change was made.
