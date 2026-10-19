## Worker report

Record the exact existing theorem `CategoryTheory.Sheaf.epi_nsmul_id_of_injective`
in `WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion`, branch
`slopmaster2`, lines 97–128. No new Lean module, duplicate statement, new node,
dependency repair, or statement correction is needed. Only the item's `lean`
field changes. Its existing status and proof fields are preserved.

Read the full node and all three statement dependencies, their records, and
recorded source declarations. Read the theorem's complete source and docstring
both locally and via `scompile.py --source` (identical). Read Stacks Project,
`sites-cohomology.tex`, Tag 0DD7, `lemma-torsion`, first proof paragraph. That
paragraph extends a local section along multiplication by n on the free abelian
sheaf on an object, establishing divisibility. The upstream theorem concludes
exactly categorical epimorphy, as requested by this node.

Hypothesis and clause correspondence:

- A small site: inherited `{C : Type u} [Category.{v} C]` and
  `{J : GrothendieckTopology C}` give the category and its topology. The
  dependency's covering-site model uses `Precoverage.toGrothendieck`; this theorem
  applies to that topology as well as to arbitrary Grothendieck topologies.
- The universe convention: independent explicit `u`, `v`, and `w`, with
  coefficient groups `AddCommGrpCat.{max w v}`, accommodate the chosen bound.
  For a site with objects and morphisms within the coefficient bound, choose
  `w` at least the object universe. The inherited
  `[HasSheafify J AddCommGrpCat.{max w v}]` is the ordinary left exact
  sheafification available for small sites in that bound, not a restriction on
  the site topology. Mathlib `Sites/LeftExact.lean:308–311` supplies it from
  ordinary group limits, filtered colimits and small covering posets; the
  essentially-small-site transport is in `Sites/Equivalence.lean:216`.
  No object/morphism universe equality is imposed by the theorem.
- An abelian sheaf I: `(I : Sheaf J AddCommGrpCat.{max w v})` uses precisely the
  full category of abelian sheaves, with natural transformations as morphisms.
- I is injective: `[Injective I]` is the Mathlib extension property along every
  monomorphism. It is the injective-object clause of
  `def-sp-injective-resolutions`, not an injective presheaf or stalkwise property.
- Every positive integer n: `{n : ℕ} (hn : n ≠ 0)`, equivalent to `0 < n` on ℕ.
- Multiplication by n on I: `n • 𝟙 I` is addition of the identity morphism n times
  in the preadditive category, so acts sectionwise as multiplication by n.
- The conclusion is `Epi (n • 𝟙 I)`, in the abelian sheaf category itself. The
  recorded statement does not replace epimorphy by pointwise surjectivity.

Dependency declarations used/read:

- `def-weil-size-convention`: its `lean.convention` record explicitly has no
  declaration; it is implemented through the explicit universe parameters.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, lines 28–33, whose field
  `factors` is the required extension property. Also read the full signature and
  docstring of `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, lines 39–55; the
  resolution clause is not needed to state this theorem.
- `def-weil-pbc-sites-and-cohomology`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` in
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, together with the Mathlib
  `Precoverage.toGrothendieck` and `CategoryTheory.Sheaf` encodings retained by
  that dependency's record and docstring. Read its complete definition and
  docstring, and `CategoryTheory.Sheaf` in `Mathlib.CategoryTheory.Sites.Sheaf`.
  Cohomology and morphisms of sites are not used by the item.

Edge cases checked: n = 0 is excluded as required; n = 1 gives the identity and
is included. The zero injective object, empty category, and degenerate topology
are included. No nonempty-site, enough-points, terminal-object, global-pullback,
or scheme hypothesis is introduced. No `HasExt` assumption is inherited: that
binder is introduced after this theorem in the source.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “Multiplication by a positive integer on an injective
  sheaf of abelian groups is an epimorphism”: eight hits, concerning generating
  sections, a Mayer–Vietoris epimorphism, presentability, and group cohomology;
  no exact Mathlib match.
- `msearch.py`, Loogle: `"Injective", "nsmul"`: twelve hits, all scalar
  cancellation and torsion-free results; no exact Mathlib match.
- `msearch.py`, Mathlib grep:
  `epi_nsmul|injective.*divisible|divisible.*injective`: seven hits, including
  `AddCommGrpCat.injective_of_divisible`, which is a different implication for
  abelian groups, and unrelated injectivity results. No sheaf theorem.
- `rg` in upstream `WeilConjectures` for `epi_nsmul_id_of_injective` finds the
  exact theorem in `CategoryTheory/Sites/SheafCohomologyTorsion.lean` and its
  module-scalar analogue. The item id itself has no upstream tag hit. The node's
  `lean_audit.slopmaster2` already identifies this closed attachment candidate.
- `rg` in `lean/Sheaf` for `injective.*divisible|epi_nsmul|divisible.*injective`
  finds only explanatory text in `TorsionSheafComplexRepresentative.lean`.
- `rg` in `dag/lean_names_upstream.json` for the theorem name/item id has no hit;
  the direct source and `scompile.py --source` establish the declaration.

No disputed statement or node fault was found. The delivery wrapper checks the
existing declaration through `scompile.py` using its generated `#check` probe;
there are no delivered modules to compile.

## Repair of return b8124f89072d

The sole returned point is a reviewer `--apply-fixes` pathname rejection:
`coord/reports/N9/lem-trf-injective-abelian-sheaf-divisible.md` was placed inside
the fix directory, whereas the stage-2 fix parser accepts the report directly
as `lem-trf-injective-abelian-sheaf-divisible.report.md` at that directory's root.
Read the parser in `tools/merge_delivery.py`, including its report-path branch.
This return specifies no mathematical change to the statement or Lean binding.

The repaired sandbox now supplies that accepted root-level report filename,
with exactly the same content as `report.md`. Normal delivery still reads
`report.md` and installs it at the prescribed committed report path. A reviewer
using the additional fix artifact must select that root-level file alone;
the delivery report's committed path is not a fix-directory pathname.
The recheck and repair explanation are included directly in the delivery, so
this repair requires no reviewer report override to land.

Compared the retained node with the current shared node: the only difference
was the intended `lean` record. Refreshed the sandbox node from that current
node and retained this record, preserving every other field. The delivery
wrapper refreshes `origin/newtargets-dag` and rebuilds the one-commit packet
on that current base; no direct Git operation was run on the shared checkout.
Re-read the existing theorem from the live source through `scompile.py
--source`, all dependency declarations, and Stacks 0DD7 lines 4225–4232.
Repeated the LeanFinder, Loogle and Mathlib grep searches reported above;
the results remain eight, twelve and seven hits respectively, with no exact
Mathlib theorem and the same exact upstream theorem.

## Second reading by N9

Worker recheck during repair; the maintainer supplies the independent review,
as required by the dispatcher brief. No separate agent was started and no
independent worker reading is claimed.

Read the node and the full upstream declaration again. The explicit category
and topology encode the small site; `Sheaf J AddCommGrpCat.{max w v}` is its
abelian-sheaf category; `[Injective I]` is the extension property along monos;
`{n : ℕ} (hn : n ≠ 0)` includes precisely positive integers; and
`Epi (n • 𝟙 I)` is precisely the requested conclusion for multiplication by n.
The preceding `HasSheafify` binder belongs to this declaration, while the
following `HasExt` binder does not. The scratch probe checks the full type,
its axioms and synthesis of `HasSheafify J AddCommGrpCat.{max u v}` for
independent site object universe u and morphism universe v. Thus choosing the
coefficient bound to contain the small site supplies sheafification without
forcing those universes equal. The zero object, empty site and n = 1 remain
included; n = 0 remains excluded. No statement or binding mismatch was found;
the repair changes report packaging and validation documentation only.

Repair validation: `scompile.py` compiled the scratch probe cleanly, including
its published-library confirmation. The theorem's axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`. Synthesis returned
`instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover`.
This instance check needs imports `Mathlib.CategoryTheory.Sites.LeftExact`
and `Mathlib.Algebra.Category.Grp.FilteredColimits`; the first probe omitted
those instance imports and failed synthesis, then the corrected probe passed.
These are standard Mathlib instances, with no extra theorem or assumption.
The scratch probe is outside `lean/` and is not a delivered library module.
