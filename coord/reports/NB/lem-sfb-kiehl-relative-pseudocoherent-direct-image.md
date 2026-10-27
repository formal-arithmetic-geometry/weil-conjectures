## Worker report

Item: `lem-sfb-kiehl-relative-pseudocoherent-direct-image`.
Module: `Sheaf.AlgebraicGeometry.KiehlRelativePseudoCoherentDirectImage`.
Declaration: `AlgebraicGeometry.Scheme.isPseudoCoherent_derivedDirectImage_of_relative`.
The module states the node with `sorry`; it adds no definitions or auxiliary theorems.
The node copy changes only `lean`. No statement correction or disputed statement.

Source read: `literature/stacks-project/perfect.tex`, lines 7545–7567, specifically the
unnumbered paragraph beginning “More generally” after the flat proper lemma 0CSD.
That paragraph assumes only properness and relative pseudo-coherence and asserts
pseudo-coherence of the derived direct image. It explicitly excludes a general
base-change conclusion; this delivery asserts no base-change conclusion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary schemes Z and T | `{Z T : Scheme.{u}}`, with explicit universe `u` |
| Morphism h : Z → T | `(h : Z ⟶ T)` |
| h proper | `[IsProper h]`; Mathlib's properness class supplies locally finite type, as required by the relative predicate |
| E in D(O_Z) | `(E : schemeDerivedCategory Z)` |
| E pseudo-coherent relative to T | `(_hE : IsPseudoCoherentRelativeTo h E)`; this is the dependency's exact predicate, quantifying over every integer m with degree-dependent covers and embeddings |
| Rh_*E | `(schemeDerivedDirectImage h).obj E`, the recorded K-injective-derived pushforward |
| Pseudo-coherent on T | `IsPseudoCoherent T ((schemeDerivedDirectImage h).obj E)`, the recorded local bounded-above finite-free predicate |
| No flatness or local finite presentation assumed | No `Flat` or `LocallyOfFinitePresentation` binder |
| No Noetherian assumption | No Noetherian binder on either scheme |
| No global quasi-compactness or quasi-separatedness of Z,T | No such binder on either scheme; properness of the morphism is retained exactly |
| No global lower cohomological bound on E | E is an arbitrary object of the unbounded derived category, without an `IsGE` or boundedness binder |

The two typeclass binder families select derived-category localizations. The family
`[∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]`
is required by the recorded relative predicate, which uses all scheme charts and affine
spaces. The target-open family supplies the over-site derived categories required by the
recorded absolute predicate. These are choices of localization infrastructure, not
geometric assumptions, and use a common explicit localization universe `w` as in the
dependency. No object, morphism or scheme universe equality was newly imposed.
`set_option autoImplicit false` ensures every variable is explicitly bound.

Dependency declarations read and used (full signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`: `AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`, defined using `IsMPseudoCoherentRelativeTo` for every integer m.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`: `AlgebraicGeometry.schemeDerivedDirectImage`.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`: `AlgebraicGeometry.Scheme.IsPseudoCoherent`.

All recorded proof-dependency modules are included as plain imports unless already
publicly imported for the signature. This includes open restriction, quasi-coherent
pushforward, the affine derived equivalence, Noetherian proper bounded coherent image,
the Noetherian pseudo-coherent criterion, the affine pseudo-coherent criterion,
bounded-flat K-flatness, module K-flatness, ring m-pseudo-coherence, its all-m criterion,
and K-injective global-sections acyclicity. The two proof prerequisites
`lem-sfb-relative-pseudocoherence-all-affine-charts` and
`lem-sfb-relative-complex-noetherian-cohomology-approximation` currently have no recorded
Lean module and are therefore not imported; they are named in the proof docstring.
`def-pc-morphism-conventions` is supplied by the Mathlib morphism classes already imported.
No proof prerequisite is needed to elaborate this theorem's signature.

The theorem docstring carries all six DAG proof steps. It records the affine reduction,
Noetherian degree-m approximation, Noetherian finiteness, base change on a bounded-above
finite free K-flat representative, stupid truncation with the degree-m surjection, and
locality/all-m conclusion. It also records the global-sections acyclicity citation in
both places where the DAG uses it. This is a statement delivery, not a claim that the
agent-written mathematical proof has been formalized.

Edge cases checked before drafting:

- Empty Z: the zero pushforward is covered; there is no nonempty-source hypothesis.
- Empty T: proper maps into the empty scheme and vacuous local conditions are included.
- E = 0 and h = identity: no nonzero or nonidentity restriction occurs.
- Arbitrarily negative nonzero cohomology: no lower bound, boundedness or finite
  Tor-amplitude hypothesis is present. Local finite-free models may extend indefinitely
  toward negative degrees.
- Non-Noetherian bases, nonflat proper maps, proper maps not locally finitely presented,
  and schemes without global quasi-compactness/quasi-separatedness remain included.
- The relative predicate is the all-integer predicate, not a fixed-degree replacement;
  its covers and embeddings need not be uniform in m.

Searches (all through the prescribed msearch.py, or direct read-only rg):

1. LeanFinder query: `Proper derived direct image of a relatively pseudo coherent complex is pseudo coherent`.
   Eight hits, including module pushforward pseudofunctor formulas, derived-category
   t-structure facts, exact-functor derived maps and condensed Grothendieck categories;
   no relative pseudo-coherent finiteness theorem.
2. Loogle query: `IsProper, IsPseudoCoherentRelativeTo, schemeDerivedDirectImage`.
   Zero hits; service reports unknown identifier `IsProper`. Thus this query is
   inconclusive by itself, not evidence of absence.
3. Mathlib grep query: `Kiehl|IsPseudoCoherentRelativeTo|isPseudoCoherent.*[dD]irectImage`.
   Zero hits.
4. The same rg over project `lean/WeilConjectures` and `lean/Sheaf` finds the recorded
   relative definition, the stronger-flatness algebraic-space theorem in
   `SpaceFlatProperPseudoCoherentDirectImage`, a Kiehl mention in the specialized
   finite-free higher-direct-image theorem, and unrelated citations. None states
   proper pushforward finiteness for arbitrary relatively pseudo-coherent complexes.
5. rg for the item id in `lean/WeilConjectures` finds no declaration.
6. rg for the chosen theorem/module names in both library roots and
   `dag/lean_names_upstream.json` finds no existing declaration.
7. LeanSearch query: `The derived direct image of a relatively pseudo-coherent complex under a proper morphism of schemes is pseudo-coherent`.
   Eight hits, all module pushforward instances/formulas or properness class facts;
   no match to the statement. The wrapper logs preserve the returned results.

Validation: scompile.py compiled the file in sandbox mode (23.9 s) and under its library
module name (8.7 s), with no errors or unexpected warnings. Only the expected theorem
`sorry` is left. The required deliver2.py preflight is run before pushing.

## Second reading by NB

A separate self-check pass compared the written signature with the node and the actual
dependency definitions: `IsProper h` supplies locally finite type without an extra
hypothesis; E remains in the full unbounded category; `IsPseudoCoherentRelativeTo h E`
retains the all-m relative condition; the conclusion uses the actual derived direct
image and the local finite-free absolute predicate. The target-open localization binder
is the one required by `IsPseudoCoherent`, not a geometric condition. No conclusion or
hypothesis mismatch was found and no correction was made.

This is explicitly a self-check, not an independent worker review: the dispatch brief
forbids starting other agents. The maintainer's independent review remains the
independent reading of this delivery.
