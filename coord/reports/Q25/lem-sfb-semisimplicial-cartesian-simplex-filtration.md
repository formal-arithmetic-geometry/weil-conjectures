## Worker report

The module `Sheaf.CategoryTheory.SemisimplicialCartesianSimplexFiltration` states
`CategoryTheory.SemisimplicialRingedTotal.semisimplicial_cartesian_simplex_filtration`.
Its only postponed proof is the theorem of this item. The two helpers belong to
this item's construction: `cartesianSimplexTerm` is literally ℓ_n e_n B, and
`cartesianSimplexFace` is the inverse adjunct of the inverse cartesian transition
followed by the specified labelled inclusion. Neither helper chooses an object
or a morphism from an existence theorem. There are no new nodes, dependency
repairs, statement corrections, or disputed statements.

Hypothesis and conclusion correspondence:

- The small coherent ringed semisimplicial total site is the dependency's
  `F`, `D`, `R`, `h` and `P : Presentation R h`. All their universe parameters
  are explicitly bound, using the dependency's `u` and standard derived size
  `u + 1`. `P` retains the canonical evaluations and transitions and their
  normalization, including the module-systems equivalence.
- Exact transition pullback is `exact`: preservation of finite limits and
  finite colimits of each actual `(P.pullback a).ordinary`.
- The exact free-extension adjunctions of the second dependency are supplied
  as `L n : EvaluationFreeExtension P (op (SemiSimplexCategory.mk n))`.
  These are the dependency's fully normalized labelled constructions, not
  arbitrary additive functors or arbitrary adjunctions. They exist under the
  given `exact` hypothesis by `semisimplicial_evaluation_free_adjoint`.
- The object is `B : (R.total h).D`, the ordinary unbounded derived category.
  `hB : P.IsCartesian B` asserts invertibility of all actual derived transitions.
  `cartesianSimplexTerm P L B n` renders X_n with B_n = e_n B.
- `K : ℕ → (R.total h).D`, `u` and `j` are the requested F_N, u_N and j_N.
  `u N ≫ j (N + 1) = j N` renders compatibility, respecting Lean's
  left-to-right composition convention.
- `hK : K 0 = cartesianSimplexTerm P L B 0` is F_0 = X_0.
  `j 0 = eqToHom hK ≫ (L 0).derivedAdjunction.counit.app B` renders the
  counit with the necessary transport along that equality.
- For each natural N, existential maps `v` and `w` and membership of
  `Triangle.mk (u N) v w` in `distTriang` give the distinguished triangle
  with third vertex X_(N+1)[N+1]. Shifts use integers, as in D(M).
- The two first faces are `SemiSimplexCategory.homOfMono
  (SimplexCategory.δ (i : Fin 2))`, then opposite: they are exactly the
  injective maps omitting i. `cartesianSimplexFace` uses the inverse of
  `(P.derivedTransition a).app B`, with its `IsIso` proof obtained from hB,
  followed by `(L 0).derivedInclusion a`, and applies the inverse derived
  adjunction for L_1. Thus the difference in the first-stage triangle is
  precisely q_0 - q_1. `eqToHom hK.symm` only changes its target X_0 to K_0.
  The second arrow is exactly `u 0`; the third is the existential `w`.
- `S`, `ι`, and `Nonempty (IsColimit (Cofan.mk S ι))` assert the actual
  coproduct and its specified coprojections. No global countable-coproduct
  instance is added as an assumption.
- `s`, `p`, and `boundary` have the requested types. The two equations on
  `ι N` render s ι_N = ι_(N+1) u_N and p ι_N = j_N.
  `Triangle.mk (𝟙 S - s) p boundary ∈ distTriang ...` is the telescope triangle.
- The final `IsColimit` is for the cofan with point S[1] and legs
  `(shiftFunctor ... (1 : ℤ)).map (ι N)`, exactly the shifted coprojections.
- There is no boundedness, cohomological truncation, negative Hom hypothesis,
  or restriction on N beyond N being natural.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`:
  `Site.D`, `RingDiagram`, `Presentation`, `Presentation.IsCartesian`,
  `Presentation.evaluation`, `Presentation.pullback`, `Presentation.derivedTransition`.
- `Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint`:
  `EvaluationFreeExtension`, its `ordinary`, `derivedAdjunction`, and
  `derivedInclusion`, and its existence theorem as justification for L.
- The proof imports are `Mathlib.Algebra.Homology.DerivedCategory.Basic`
  for `DerivedCategory` and `Q`,
  `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit` for
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`
  (together with the triangulated localization Qh), and
  `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit` for
  `CategoryTheory.moduleSheaf_complex_colimit_homotopyColimit`.
  The degreewise-split dependency has a mathlib_match and no Lean record;
  its indicated Mathlib interface is used directly, as required.
- Mathlib's `SemiSimplexCategory`, `homOfMono`, `SimplexCategory.δ`,
  `Triangle.mk`, `distTriang`, `Cofan.mk`, `IsColimit`, `shiftFunctor`,
  and `eqToHom` supply the existing categorical notions and transports.

Sources opened: the full two dependency interfaces and their docstrings;
Stacks `spaces-simplicial.tex`, the resolution at Tag 0D9B, the cartesian
comparison at Tag 0D9E, and the Postnikov/hocolimit construction at Tag 0D9Q.
The module docstring includes the full eight-step coefficient-complex,
injection-only adaptation recorded in the node. The example Sheaf compact-object
module is now withdrawn, so its recorded upstream replacement
`WeilConjectures.CategoryTheory.CompactObject` was also read for conventions.

Edge cases checked before writing: N = 0 gives X_1[1] in the quotient triangle
and the separate cone triangle with signed map q_0 - q_1; the latter uses actual
distinct omitted-vertex labels, not a zero or unconstrained map. For a component
m and p > m, the dependency's coproduct is empty and equals zero; the proof's
finite stabilization is therefore valid without any bound on the vertical
complex. B = 0 is allowed; all terms and filtration may then be zero. Degenerate
sites and zero rings are not excluded. The infinite telescope has its universal
property stated explicitly, as does its shift.

Searches (2026-10-24; msearch results also recorded in searches.jsonl):

- leanfinder: `cartesian semisimplicial derived object simplex filtration free
  extension distinguished telescope triangle` returned eight Dold-Kan Γ
  construction declarations. These concern a fixed coefficient category and
  do not give the varying ringed total category or this filtration.
- leansearch: `An unbounded cartesian semisimplicial derived module is the
  homotopy colimit of its simplex filtration` returned general filtered
  colimits of complexes, cosimplicial colimits and ModuleCat colimits;
  none states the desired result.
- loogle: `SemiSimplexCategory, Triangle, IsColimit` returned no hits and the
  diagnostic `unknown identifier 'Triangle'`; no matching result was found.
- msearch grep: `simplex.*[Ff]iltration|semisimplicial.*[Cc]artesian` in
  Mathlib/CategoryTheory returned zero hits.
- rg in live `lean/WeilConjectures` for the item id, semisimplicial names and
  proposed declarations returned no existing declaration. rg in `lean/Sheaf`
  found the two dependency modules, but no simplex-filtration theorem.
  Proposed full declaration names were also checked in Mathlib and
  `dag/lean_names_upstream.json`, with no match.

Validation: scompile.py compiled the sandbox and library forms cleanly on the
server (2.1 s and 2.6 s); no non-sorry warnings or errors were printed.

## Second reading by Q25

This is a self-review by the sole dispatched worker, not a claim of independent
agent review: the dispatch explicitly forbids starting other agents, and the
maintainer provides the independent reading. With the node and module reopened,
I checked the exact source and target of the inverse cartesian transition and
its inclusion, both omitted-vertex labels and their order, the two transports
at stage zero, the quotient shift's positive sign, the three telescope maps,
both leg restriction equations, and the shifted cofan's legs. Every clause is
accounted for above. The helper definitions contain real expressions and no
postponed data. The sole theorem proof is `sorry`. No mismatch or correction
was found in this reading.
