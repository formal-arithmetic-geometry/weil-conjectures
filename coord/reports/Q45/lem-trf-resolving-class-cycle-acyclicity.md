## Worker report

The module `Sheaf.Algebra.Homology.ResolvingClassCycleAcyclicity` states
`HomologicalComplex.resolving_class_cycle_acyclicity`, with one `sorry` and no new
notions. The node changes only in `lean`. No statement correction or dependency
repair is needed. The class is an arbitrary predicate, not a separately defined
resolving-class structure.

Hypothesis-by-hypothesis correspondence:

- The abelian categories are `{A : Type u₁} {B : Type u₂}` with their independently
  sized `Category.{v₁}` and `Category.{v₂}` structures and `[Abelian A] [Abelian B]`.
- The additive functor is `(V : A ⥤ B) [V.Additive]`. Mathlib's additive-functor
  class states preservation of addition and implies preservation of zero.
- The object class is `(𝓔 : A → Prop)`. `hzero` puts every zero object in it;
  `hiso` transports membership along every isomorphism.
- `hclosed` quantifies over every `S : ShortComplex A`. Its `S.ShortExact`
  premise expresses the given short exact sequence; `𝓔 S.X₂` and `𝓔 S.X₃`
  are exactly the middle and quotient membership assumptions. Its conclusions
  `𝓔 S.X₁ ∧ (S.map V).ShortExact` express kernel membership and the short
  exact image sequence, using the images of the specified arrows.
- `(E : CochainComplex A ℤ) (b : ℤ)` gives the complex and bound.
  `hbounded : ∀ n, b < n → IsZero (E.X n)` expresses termwise vanishing
  strictly above b. `hacyclic` expresses `IsZero (E.homology n)` in every
  degree. `hterms` gives membership of every term.

Clause-by-clause correspondence:

- `∀ n, 𝓔 (E.cycles n)` gives membership of all cycles.
- `((E.cyclesShortComplex n (n + 1)).map V).ShortExact` is exactly
  `0 → V(Zⁿ) → V(Eⁿ) → V(Zⁿ⁺¹) → 0`. The upstream construction has
  objects `E.cycles n`, `E.X n`, `E.cycles (n+1)` and arrows `E.iCycles n`
  and `E.toCycles n (n+1)`. Its image uses `V.map` on those same arrows.
- The first subobject equality identifies the image of `V.map (E.iCycles n)`
  with the kernel subobject of the outgoing differential in the actual complex
  `(V.mapHomologicalComplex (ComplexShape.up ℤ)).obj E`.
- The second equality identifies that same subobject with the image subobject
  of the incoming differential in degree `(n-1,n)` of that same complex.
  The preceding short exactness conclusion includes monicity of the image
  inclusion, so its image subobject represents its domain faithfully. These
  are equalities of subobjects of `V.obj (E.X n)`, not arbitrary object isomorphisms.
- The final `.Acyclic` is exactness in every degree of the termwise image complex.
- There is no assumption of global right exactness, homology preservation,
  enough projectives, or existence of a derived functor.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Read the full class and docstring.
- `def-weil-abstract-derived-category`: its recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` is publicly imported.
  This node also covers complexes and cohomology: the statement uses
  `CochainComplex`, `HomologicalComplex.homology`, `cycles`, `iCycles`,
  `toCycles`, and `Acyclic`. No derived-category localization parameter is
  needed for a statement entirely about complexes.
- `HomologicalComplex.cyclesShortComplex` in
  `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`
  supplies the existing canonical cycle sequence without a second definition.
- `CategoryTheory.ShortComplex.ShortExact` in
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact` and
  `imageSubobject` / `kernelSubobject` exposed by
  `Mathlib.CategoryTheory.Abelian.Exact` give exact sequences and subobjects.
- Proof dependency `lem-sp-abelian-refinements` is a Mathlib leaf, without a
  `lean` record. Its recorded source `Mathlib.CategoryTheory.Abelian.Refinements`
  is imported privately. Read `epi_iff_surjective_up_to_refinements`,
  `ShortComplex.exact_iff_exact_up_to_refinements`, and
  `Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements`,
  including their full signatures. They cover the three recorded clauses.

The theorem docstring reproduces all four proof steps: cycle short exactness
from refinement lifting, descending membership and image exactness, identification
of kernels, and identification of images and acyclicity. Source checked:
`literature/stacks-project/derived.tex`, `lemma-F-acyclic-ses` and
`lemma-leray-acyclicity` (Tags 015D/015E). The class-level statement is the node's
explicit abstraction of the dual argument, not asserted to be verbatim Stacks.

Edge cases checked before writing: the zero complex and the class of zero
objects satisfy the conclusion; for n>b both relevant cycle objects are zero;
at n=b induction starts from Z^(b+1), not Z^b. Negative bounds and arbitrarily
negative degrees are included by ℤ throughout. The identically true class
specializes to preservation of all short exact sequences. The zero functor is
allowed. No smallness relation between the two categories or their morphism
universes is imposed. No empty class is allowed by the zero-object premise,
as required by the node. Exactness is stated using IsZero, not equality with a
chosen zero object.

Searches (2026-10-24):

- `msearch.py ... leanfinder "An additive functor exact on short exact sequences
  in a kernel closed class preserves acyclicity of bounded above complexes in
  that class"`: eight results, including `Functor.exact_tfae`,
  `Functor.preservesHomology_of_map_exact`, and `ShortComplex.ShortExact.map`.
  None includes the class-relative descending induction or both subobject clauses.
- `msearch.py ... loogle '"ShortExact", CategoryTheory.Functor.Additive'`:
  eleven results, principally preservation of all epimorphisms/monomorphisms
  under global preservation hypotheses. None states this node.
- `msearch.py ... grep 'acyclic.*map|map.*acyclic|cycles.*exact' Algebra/Homology`:
  25 hits; exactness and cycle infrastructure, not this class-relative result.
- `msearch.py ... leansearch "An additive functor exact on a kernel closed class
  sends bounded above acyclic complexes in the class to acyclic complexes"`:
  eight results, including `Acyclic`, `Functor.exact_tfae`, and additive functor
  infrastructure. No exact match.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for resolving-class/cycle-acyclic
  names, kernel-closed wording, and the exact item id found no matching theorem.
  The related upstream `Acyclic.map_of_rightAcyclic` has a bounded-below complex,
  right-acyclic terms and a globally left-exact functor, so is not this statement.
- A focused source search for `iCycles.*toCycles` found the existing
  `cyclesShortComplex`, which is used. Source reads of `Functor.exact_tfae`
  and `preservesHomology_of_map_exact` confirmed their global assumptions.
- Exact proposed declaration-name search over Mathlib, WeilConjectures and Sheaf
  found no collision. Search tool outputs are also retained in `searches.jsonl`
  by the prescribed wrapper.

Validation: prescribed `scompile.py Q45 lem-trf-resolving-class-cycle-acyclicity`
compiled this module in both sandbox and library modes cleanly (9.5 s and 1.3 s).
All variables and universes are explicitly bound. No node faults or disputed
statement were found.

## Second reading by Q45

This is the worker's final consistency rereading of the node and completed file;
the dispatch brief assigns the independent delivery review to the maintainer and
forbids starting another agent. It is not represented as an independent review.

Rechecked every binder against the node: arbitrary abelian A and B; additive V;
zero-containing, isomorphism-closed predicate; closure and exact image only when
the middle and quotient lie in that predicate; integer cochain E, integer b,
strict upper vanishing, zero cohomology, and term membership. Rechecked each
conclusion: all cycle memberships, all exact image sequences on the canonical
maps, the two subobject identities in V(E^n), and acyclicity of that same image
complex. In particular short exactness supplies monicity, making the use of
`imageSubobject (V.map (E.iCycles n))` precisely the subobject represented by
V(i_n). No mismatches or changes were found on this rereading.
