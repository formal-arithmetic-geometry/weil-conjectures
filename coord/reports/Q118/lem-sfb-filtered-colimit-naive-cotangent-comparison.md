## Worker report

Delivered statement: `Algebra.CanonicalNaiveCotangent.filteredColimit_comparison` in
`Sheaf.RingTheory.FilteredColimitNaiveCotangentComparison`, with the concrete helper
`comparison`. A second module supplies the missing fixed-base functor, using Mathlib's
existing conormal quotient, canonical presentation, differential and cone construction.
No change to the item's mathematical statement was needed. The only added statement
dependency is the new definition node below. All five theorem bodies are exactly `sorry`.

Clause-by-clause correspondence:

- A commutative base ring is `{R : Type u} [CommRing R]`.
- The small filtered category is `{J : Type (max u v)} [SmallCategory J] [IsFiltered J]`.
  `IsFiltered` includes nonemptiness, common targets and equalization of parallel arrows.
- The algebra diagram is `F : J ⥤ CommAlgCat.{max u v} R`. The specified algebra colimit
  cocone is `c : Cocone F` with `hc : IsColimit c`; its algebra is `c.pt` and its legs
  are `c.ι.app j`. We quantify over any colimit cocone rather than force a chosen carrier.
- For every algebra `T`, `ideal T` is an abbreviation for
  `(Generators.self R T).toExtension.ker`: the kernel of evaluation on `MvPolynomial T R`.
  The degree-minus-one term is the existing `(ideal T).Cotangent`, literally I/I².
  `differential T` composes Mathlib's `cotangentEquivCotangentKer.symm`, its
  `cotangentComplex`, and `cotangentSpaceBasis.repr`, restricted to R. Thus its target
  is the actual finite-support module `T →₀ T`, with differential the partial-derivative
  formula. `Generators.cotangentSpaceBasis_repr_one_tmul` verifies that formula.
- `conormalMap f` is `Ideal.mapCotangent` for `MvPolynomial.rename f.hom`.
  `rename_mem` is the named kernel-preservation assertion needed for this construction.
  `freeMap f` is `Finsupp.lsum` of `lsingle (f t)` composed with `f.hom.toLinearMap`:
  it sends a d[t] to f(a) d[f(t)], including collisions. No arbitrary chain map is assumed.
- `differential_naturality` states exactly the chain-square identity. `differentialMap`
  packages that square. `complex` takes its differential between degree-zero single
  complexes and the existing `CochainComplex.mappingCone`, whose terms are canonically
  I/I² in degree -1 and the free module in degree 0, with zero elsewhere and the positive
  original differential. This is the same cone encoding already used by the landed
  `Algebra.indEtale_naiveCotangent_acyclic` statement. It adds only canonical zero
  biproduct factors; it is not the full cotangent complex or an arbitrary presentation.
- `map` uses `single.mapArrow` and `homotopyCofiber.mapArrowHom` on that concrete square.
  The named `map_id` and `map_comp` assertions supply the functor laws. These four
  postponed structural assertions are clauses of the new definition node, and each
  has its natural-language proof in its docstring. Every definition has actual data.
- The diagram of complexes is `F ⋙ functor R`; all terms are R-modules. Its specified
  degreewise colimit is `k : Cocone (F ⋙ functor R)` with `hk : ∀ n, IsColimit
  ((HomologicalComplex.eval ... n).mapCocone k)`. Thus K is `k.pt`, eta is `k.ι`, and
  `HomologicalComplex.isColimitOfEval` gives its colimit universal property as a complex.
- `comparison F c k hk` is that universal property's `desc` of
  `(functor R).mapCocone c`. Consequently its composites with eta are exactly N(iota),
  by the existing `IsColimit.fac` law. The characterization is built into the definition.
- The first conclusion is `QuasiIso (comparison F c k hk)`. The second is
  `IsIso (DerivedCategory.Q.map (comparison F c k hk))`, the requested isomorphism of
  the *canonical arrow* in D(Mod(R)). `[HasDerivedCategory.{w} (ModuleCat... R)]`
  keeps the localization morphism universe arbitrary, as the recorded definition does.
- There are no injective, flat, finite, Noetherian, or finitely presented assumptions.

Dependency declarations read and used:

- def-weil-pbc-category-colimit: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `Cocone`, `IsColimit`, the universal-property `desc`, and
  `Mathlib.CategoryTheory.Filtered.Basic`, `CategoryTheory.IsFiltered`.
- def-weil-pbc-smooth-ring-map: its recorded `Mathlib.RingTheory.Smooth.Basic`,
  `Algebra.Smooth`, gives the smoothness predicate rather than an explicit complex.
  Read its full signature and docstring, `FormallySmooth`, and its recorded
  `mathlib_match` pointing to the exact Mathlib canonical cotangent construction.
  We reuse that construction directly: `Generators.self`, `toExtension`,
  `Extension.Cotangent`, `cotangentComplex`, `cotangentEquivCotangentKer`, and
  `Generators.cotangentSpaceBasis`, from `Mathlib.RingTheory.Extension.Cotangent.Basic`.
  No smoothness hypothesis is imposed, and no dependency repair or duplicate smoothness
  definition is needed. The new node assembles the missing functor, not these existing notions.
- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`, and `QuasiIso`.
- The new definition also cites def-weil-pbc-mv-polynomial-ring:
  `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`, `aeval`, `algHom_ext`;
  `MvPolynomial.rename` is the existing coefficient-fixing renaming algebra map.
- Proof imports implement the recorded Mathlib matches of
  lem-weil-pbc-filtered-colimit-algebras-elementwise,
  lem-pc-filtered-colimit-commrings-elementwise, and
  lem-weil-pbc-filtered-colimit-modules-criterion: Concrete representative/equality
  lemmas; connected Under colimits; CommRingCat and ModuleCat filtered colimits;
  `Types.FilteredColimit.isColimitOf'` and reflection of colimits.
  lem-sfb-filtered-colimit-conormal-modules currently has no recorded Lean module,
  so no nonexistent import is introduced; the stage-3 proof docstring names it.

Edge cases checked before writing: the zero ring and zero algebra are allowed; no
nontriviality instance is required. A filtered category is nonempty by definition, so
there is no silent exclusion of a permitted empty diagram. A one-object identity
system gives the identity comparison up to unique colimit identification. Noninjective
maps can collide variable labels, and `lsum` adds those coefficients. Eventual-zero
relations are permitted; no cancellation or flatness is assumed. Infinite underlying
algebras give finite-support free modules and arbitrary-variable polynomials. All sizes
fit one ambient universe `max u v`; this includes all rings and small diagrams after
choosing their ambient universe, without equating independent base and algebra sizes.
Arbitrary colimit carriers and arbitrary localization morphism universe remain allowed.

Searches (also recorded verbatim as tool responses in the new node's mathlib_searches):
LeanFinder, "canonical naive cotangent complex commutes with filtered colimits of
commutative algebras", returned eight general functoriality/finite-presentation hits,
including `CotangentSpace.map_comp_cotangentComplex`, with no comparison theorem.
Loogle, `"cotangentComplex", "colimit"`, and `"cotangentComplex", CommAlgCat`,
returned zero hits. msearch grep for cotangent/colimit or directLimit in either order
returned zero hits; grep for cotangent functor or CommAlgCat/CochainComplex returned
zero hits. LeanSearch for the canonical fixed-base functor returned eight general
hits, including `Ideal.mapCotangent` and `HomologicalComplex.asFunctor`, with no such
functor. Project/DAG searches and `blueprint_refs.py search 'naive cotangent'` found no
fixed-base canonical functor; the latter returned zero blueprint-node matches. Direct
rg over Mathlib, WeilConjectures and Sheaf found no `CanonicalNaiveCotangent` name.
The prescribed grep of the item's id in WeilConjectures had no hit. Read the existing
NaiveCotangentComparison and IndEtaleNaiveCotangentAcyclic modules to avoid duplicate
quotient or cone definitions. No exact theorem match exists.

Validation: both modules compiled individually and together through the prescribed
scompile.py wrapper, clean of errors and warnings. The first probes found and repaired
an ambient-universe mismatch, a missing module-category Abelian import, and a field
notation ambiguity when converting the conormal equivalence to a linear map. The final
construction uses `LinearEquiv.toLinearMap` explicitly. No source/library file was edited.
No STATEMENT-DISPUTED flag or statement correction is necessary.

## New nodes

`def-sfb-canonical-naive-cotangent-functor`: defines the fixed-base canonical naive
cotangent functor, including the specified polynomial renaming, conormal and free
maps, kernel preservation, differential compatibility and identity/composition laws.
Source: Stacks algebra.tex, Tag 00S0, definition-naive-cotangent-complex and
equation-functoriality-NL; Tag 07BQ. The searches above found the individual Mathlib
constructions, but no assembled fixed-base functor or corresponding DAG node. Its
module reuses those constructions and supplies only the missing assembly. All data
are explicit; the structural proof obligations are named theorem clauses matching
this node and have complete proof docstrings. The item's only non-lean change is
adding this node to stmt_deps.

## Second reading by Q118

Self-review only: the dispatcher explicitly prohibited starting another agent, and the
maintainer performs the independent review. Reopened both delivered Lean files and the
original node for this pass. Matched each binder and clause as above. Checked especially
that `hc` is the algebra-colimit universal property, `hk` expresses every degree's
module colimit, and the conclusion mentions the canonical comparison rather than an
unrelated derived isomorphism. Checked the cone sign: the degree -1 to 0 entry is the
original differential, since both single-complex differentials are zero. Checked that
`Ideal.mapCotangent` and the Mathlib conormal type-synonym equivalence use the same
R-action via constants; hence differential and conormal maps are in the same module
category. Checked that `freeMap` adds rather than discards variable collisions. Read
all structural sorry signatures against the new node, which explicitly asserts each
law. Checked the original node's statement, proof, proof_deps and other metadata are
unchanged. No additional mismatch was found; this is not claimed to be an independent
second worker's reading.
