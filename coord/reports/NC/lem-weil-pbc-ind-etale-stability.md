## Worker report

The module `Sheaf.RingTheory.IndEtaleStability` states
`RingHom.indEtale_principalZariski_stability`, with proof `sorry`. It states the entire
node as a conjunction, with no new definitions, dependency replacements, or statement
correction. Its docstring includes all nine proof steps and their dependency IDs.
The blueprint source was read at
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-ind-etale-stability.md`.

Clause-by-clause correspondence, numbering the ten conjuncts:

1. Ind-etale base change: `RingHom.IsStableUnderBaseChange (@RingHom.IndEtale.{u})`.
   The Mathlib predicate quantifies over arbitrary commutative ring pushout squares,
   with their algebra structures and compatible scalar towers; it concludes the
   property for the base-changed structural map.
2. Ind-Zariski base change: the same predicate applied to
   `@Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra`.
3. Ind-etale composition: `RingHom.StableUnderComposition (@RingHom.IndEtale.{u})`.
   This quantifies over three arbitrary commutative rings and composable ring maps;
   it assumes the property for both maps and concludes it for their composite.
4. Ind-Zariski composition: the same predicate with the principal ind-Zariski condition.
5. Ind-etale filtered colimits: arbitrary `I : Type u`, `[SmallCategory I]`,
   `[IsFiltered I]`, `D : I ⥤ Arrow CommRingCat.{u}`, and colimit cocone `c`;
   `IsColimit c` and `∀ i, (D.obj i).hom.hom.IndEtale` imply the same for `c.pt.hom.hom`.
6. Ind-Zariski filtered colimits: the same arrow diagrams and colimit hypothesis,
   evaluated with `Algebra.IsIndPrincipalZariski` and each arrow's `toAlgebra`.
   Arrow colimits compute source and target colimits, so this includes varying bases,
   as well as the fixed-base diagrams explained in proof step 5.
7. Ind-etale implies weakly etale: arbitrary commutative `A B` and `f : A →+* B`,
   `f.IndEtale → f.WeaklyEtale`.
8. Relative assertion: arbitrary commutative `A B C`, `[Algebra A B]`, `[Algebra A C]`,
   hypotheses `Algebra.IndEtale A B` and `Algebra.IndEtale A C`, and every
   `f : B →ₐ[A] C`; conclusion `f.toRingHom.IndEtale`. The algebra homomorphism
   supplies exactly the required compatibility with the base; no flatness,
   injectivity, nonzero-ring or finite-presentation hypothesis is added.
9. Weakly etale composition: `RingHom.StableUnderComposition (@RingHom.WeaklyEtale.{u, u})`.
10. Weakly etale base change: `RingHom.IsStableUnderBaseChange (@RingHom.WeaklyEtale.{u, u})`.

All universes and variables are explicitly bound. All rings share universe `u`,
as in the recorded ind-etale and principal ind-Zariski definitions. Index types
are in that same universe. Ring structures are typeclasses, not extra mathematical
hypotheses. No diagonal conclusion is added: the diagonal computation belongs to
the proof, although the node's title mentions it.

Dependency declarations used:

- `Sheaf.RingTheory.IndPrincipalZariski`: `Algebra.IsIndPrincipalZariski`, the exact
  filtered presentation by finite products of principal localizations required here.
  The full definition and its docstring were read.
- Its public imports expose `Algebra.IndEtale` and `Algebra.WeaklyEtale`, and the
  spectrum equivalences recorded on the dependency. The definition/signatures and
  docstrings were read in `WeilConjectures.RingTheory.ProEtale.IndEtale`,
  `Mathlib.RingTheory.Etale.Weakly`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
- `RingHom.IndEtale` is the existing ring-map spelling of `Algebra.IndEtale`
  with the algebra structure induced by the map.
- `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`: `RingHom.WeaklyEtale`
  supplies the identical ring-map spelling for weak etaleness.
- `Mathlib.RingTheory.RingHomProperties`: `RingHom.IsStableUnderBaseChange` and
  `RingHom.StableUnderComposition`; both definitions were read in full.
- `Mathlib.CategoryTheory.Limits.Comma`: arrow category colimit infrastructure.
  All recorded proof dependency modules, including Mathlib matches, are imported
  non-publicly for the stage-3 proof plan.

Edge cases checked: the zero ring and maps to it are included (`CommRing`, no
`Nontrivial`). The principal ind-Zariski definition allows `n = 0` and hence the
empty product, and localization at zero. Singleton filtered diagrams and identity
maps are included. Empty filtered diagrams are excluded precisely by `IsFiltered`,
which is nonempty, consistently with the recorded definitions. Arbitrary
characteristics are included. No finiteness or injectivity is imposed on the
relative algebra homomorphism. Fixed-base and varying-base filtered colimits are
both covered. No node faults or disputed statements were found.

Searches for reuse:

- `msearch.py ... leanfinder`: query "Ind-etale and principal ind-Zariski ring maps
  stable under base change composition filtered colimits and relative algebra maps".
  Eight hits, all ordinary etale stability, etale loci, or etale algebra maps;
  none states the combined node with principal ind-Zariski presentations.
- `msearch.py ... loogle`: `RingHom.IndEtale, Algebra.IsIndPrincipalZariski,
  RingHom.WeaklyEtale`; zero hits, unknown identifier `RingHom.IndEtale` in that index.
- `msearch.py ... grep`: `IndEtale|IndPrincipalZariski|WeaklyEtale` in `RingTheory`;
  five Mathlib hits, the existing weakly etale class and ULift equivalence only.
- `rg` in upstream `WeilConjectures` for ind-etale and weakly etale names found
  individual upstream results: `RingHom.IndEtale.comp`,
  `RingHom.IndEtale.isStableUnderBaseChange`, `RingHom.IndEtale.of_isColimit`,
  `Algebra.IndEtale.weaklyEtale`, `RingHom.IndEtale.of_comp`, and
  `RingHom.WeaklyEtale.comp`. Their signatures were inspected; server `#check`
  probes confirmed availability. They do not supply the principal ind-Zariski
  clauses, so no declaration states the full node.
- The upstream item-ID search returned no match. `rg` in `lean/Sheaf` found only
  the recorded `Algebra.IsIndPrincipalZariski` definition for the principal notion.
  The upstream `Algebra.IndZariski` permits arbitrary local isomorphisms as stages,
  so its stability lemmas cannot be recorded as this entire node's statement.
- The new full declaration name was searched in the project and upstream name
  inventory; no existing declaration matches it.

Validation: the final module compiled cleanly through `scompile.py` on the server,
with nice 19, two threads, and the standard 60-second per-file limit. All temporary
`#check` probes were removed. No local compiler or global build was run.

## Second reading by NC

I read the node statement, its blueprint source, the dependency node
`def-weil-pbc-ind-etale-algebra`, and the rendered declaration
`RingHom.indEtale_principalZariski_stability` in
`Sheaf.RingTheory.IndEtaleStability`.

The ten clauses correspond item by item. Clauses 1 and 2 use
`RingHom.IsStableUnderBaseChange` for `RingHom.IndEtale` and
`Algebra.IsIndPrincipalZariski` respectively; clauses 3 and 4 use
`RingHom.StableUnderComposition` for the same two properties. Clauses 5 and 6
quantify over `I : Type u`, `[SmallCategory I]`, `[IsFiltered I]`, an arrow
functor `D : I ⥤ Arrow CommRingCat`, a cocone and `IsColimit`, and conclude the
ind-etale or principal ind-Zariski property of the colimit arrow. Clause 7 is
`f.IndEtale → f.WeaklyEtale`. Clause 8 quantifies commutative rings `A B C`,
`[Algebra A B]`, `[Algebra A C]`, both relative ind-etale hypotheses, and every
`f : B →ₐ[A] C`, concluding `f.toRingHom.IndEtale`. Clauses 9 and 10 are weakly
etale composition and base-change stability. The quantifier order and all
universe and typeclass binders match the node; `RingHom`'s stability
predicates supply exactly the arbitrary ring maps and pushout hypotheses of
the source lemmas.

The dependency's `Algebra.IsIndPrincipalZariski` is the recorded finite-product
of principal-localizations filtered-colimit notion, while its public module
also supplies the recorded `Algebra.IndEtale` and `Algebra.WeaklyEtale`
declarations. No private duplicate or extra hypothesis occurs. The source
place in `literature/stacks-project/proetale.tex`, section `Ind-etale algebra`,
defines filtered colimits of etale algebras and states base change,
composition, filtered colimits, permanence for algebra maps, weak etaleness,
and the later ind-Zariski results; the Lean conjunction renders the blueprint
node's combined statement.

Edge cases are included: `CommRing` permits the zero ring and zero maps;
`Fin n` in the principal-localization dependency permits `n = 0` (the empty
product); `IsFiltered` supplies the required nonempty filtered diagrams;
identity and singleton diagrams are allowed; arbitrary characteristics and
empty spectra are not excluded; and all indices and rings share the node's
universe `u`. Varying bases are covered by the arrow-category formulation.

I searched Mathlib and the upstream `WeilConjectures` sources with LeanFinder,
Loogle, grep, and the project name inventory for the full combined statement
and for the principal ind-Zariski notion. Existing upstream lemmas cover only
individual etale or weakly-etale operations; no declaration states this
combined theorem. The project search likewise found only the dependency's
`Algebra.IsIndPrincipalZariski` definition and individual upstream stability
lemmas.

No mismatch was found, so no source or Lean changes were required. The module
compiled cleanly with the required server command and standard limits.
