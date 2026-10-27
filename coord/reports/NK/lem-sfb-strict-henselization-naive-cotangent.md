## Worker report

The module `Sheaf.RingTheory.StrictHenselizationNaiveCotangent` states
`Algebra.strictHenselization_naiveCotangent_iso`, with one `sorry` and no new definitions.
The node is unchanged outside `lean`. There are no new nodes, dependency repairs,
statement corrections, or disputed statements.

Clause-by-clause correspondence:

- Commutative local rings A and B: `{A : Type u} {B : Type v}` with
  `[CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]`.
- Local homomorphism A → B: `[Algebra A B] [IsLocalHom (algebraMap A B)]`.
  The latter is the standard local-ring-map predicate, equivalent to inverse image
  of the maximal ideal being the source maximal ideal.
- Chosen residue separable closures: `[Field KA] [Field KB]`, the two
  `Algebra (IsLocalRing.ResidueField ...) ...` instances, and the two `IsSepClosure`
  instances. The A- and B-algebra structures and their scalar towers specify
  precisely the maps through the residue quotients.
- Compatible embedding: `(i : KA →+* KB)` and `hi`. A unital ring homomorphism
  of fields is injective; `hi` is exactly extension of the induced residue-field map.
- Strict henselizations relative to these choices: `PA` and `PB` use the recorded
  `StrictHenselizationPresentationIn`, retaining the universal pointed-etale colimit
  and specified algebra identification. Their residue maps are the recorded
  `StrictHenselizationPresentationIn.residueMap`.
- Induced local map As → Bs: `[Algebra As Bs]` and its `IsLocalHom` instance;
  `[Algebra A Bs]` and the towers `A B Bs`, `A As Bs` assert the commutative square.
  `hres` is precisely compatibility with `i` on the specified residue maps.
  Local-ring instances on As and Bs express the node's local strict henselizations.
- Canonical polynomial presentation: `Generators.self A B` has variables indexed
  by every element of B, value map the identity and section `MvPolynomial.X`.
  Its `toExtension.Cotangent` is I/I² and its `toExtension.CotangentSpace` is
  `B ⊗[A[B]] Ω[A[B]/A]`. `cotangentComplex_mk` reads `[h] ↦ 1 ⊗ dh`.
  This is the node's `Ω[A[B]/A] ⊗[A[B]] B` under the canonical symmetry.
- Two terms in degrees -1 and 0: `CochainComplex.mappingCone` of the
  degree-zero `HomologicalComplex.single` map. The cone's terms are the
  canonical biproducts `N1 ⊞ 0`, `0 ⊞ N0`; all other terms are zero objects.
  Under the biproduct-with-zero identifications its differential is the specified
  positive conormal differential, not its negative.
- Ordinary termwise tensor: the source uses
  `(Generators.self A B).toExtension.cotangentComplex.baseChange Bs`.
  Its terms are `Bs ⊗[B] N1`, `Bs ⊗[B] N0`, and its formula is
  `c ⊗ x ↦ c ⊗ δ(x)`. These are the node's right tensor products under symmetry;
  no derived tensor functor or flatness assumption occurs.
- Target: the identical cone construction for `Generators.self As Bs`.
- Derived isomorphism: the existential `e` is an actual isomorphism between
  the images of these complexes under `DerivedCategory.Q`, with the chosen
  morphism-size parameter `[HasDerivedCategory.{w} (ModuleCat.{max u v t} Bs)]`.
- The canonical map, rather than unspecified isomorphic objects: the existential
  chain map `f` satisfies `DerivedCategory.Q.map f = e.hom`. Its degree -1
  and degree 0 components are pinned by the two equations with `mappingCone.inl`
  and `mappingCone.inr`. These inclusions are isomorphisms in their respective
  degrees because the complementary summands are zero. Hence the equations
  uniquely determine every nonzero component; all other components are maps
  between zero objects. They are exactly `Extension.Cotangent.map` and
  `Extension.CotangentSpace.map` for `Generators.defaultHom` on the canonical
  presentations, extended by `LinearMap.liftBaseChange Bs`. The default
  polynomial map sends C(a) to C(image a), X(b) to X(image b), as required.
  `Cotangent.map_mk` and `CotangentSpace.map_tmul` show these are the class
  and differential formulas in the node, for every generator and scalar.
- No Noetherian, finite-type, or flatness condition is imposed. All rings A and B
  have independent universes; KA, KB, As, Bs and the modules use the arbitrary
  common larger universe `max u v t`, as required by the pointed-etale interface.

Dependency declarations read and used:

- `def-pd-separable-closure`: `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`,
  `IsSepClosure.exists_intermediateField_mem`; its docstring identifies
  Mathlib's `IsSepClosure`, which is the predicate used here.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`.
  Their definitions explicitly use `IsLocalRing.ResidueField` and
  `IsLocalRing.ResidueField.map`, respectively. Our rings need the latter exact
  local-ring objects, rather than introducing schemes or new residue definitions.
- `def-sc-ring-strict-henselization`: `Sheaf.RingTheory.StrictHenselizationPresentationIn`,
  `Algebra.StrictHenselizationPresentationIn` and its `residueMap`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic` / `Eval`,
  `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`, through
  `Algebra.Generators.self` in the extension/cotangent import.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`, through the cotangent module.
- `def-weil-pbc-module-tensor-product`: `Mathlib.LinearAlgebra.TensorProduct`,
  `TensorProduct`, `LinearMap.baseChange`, `LinearMap.liftBaseChange`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.

Proof dependencies are imported privately when recorded: pointed-etale filteredness,
etale finite presentation, ind-etale universe transport, ind-etale cotangent acyclicity,
Jacobi–Zariski and tensor right exactness. The cokernel-Kahler dependency is in
`Mathlib.RingTheory.Extension.Cotangent.Basic`, already public for the statement.
`lem-sfb-ind-etale-jacobi-zariski-left-injective` has no recorded Lean declaration
at delivery preparation, so there is no module to import. It is a proof-only input;
its full statement is retained in the stage-3 docstring proof plan, and the maintainer
can add its import when it is stated, per stages/2-statements.md rule 7.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-henselization-NL`, lines 8523–8555 (Stacks 0D08).
It explicitly gives the strict-henselization comparison and proves it by the
same two Jacobi–Zariski arguments. The four-step node proof is recorded in the
theorem docstring, including ind-etale left injectivity and without a false
interchange of H1 and tensor.

Edge cases checked mathematically:

- The identity local map and identical compatible choices give the identity comparison.
- For fields and compatible separable closures this is the usual base-extension
  comparison; the construction permits arbitrary characteristic and inseparability
  of the original residue-field extension.
- Nonreduced and non-Noetherian local rings are allowed. No module freeness,
  finite generation or flatness of A → B is assumed.
- Zero rings are excluded precisely by `IsLocalRing`, in accordance with the
  source convention for local rings; no additional exclusion is introduced.
- A and B may have different universes. The common universe contains both bases,
  so the pointed-etale tests cannot become vacuous through a universe choice.
- All elements of B index the polynomial variables; no finite variable-set
  restriction or finite-presentation assumption has entered the statement.

Searches for reuse:

1. `msearch.py ... leanfinder "strict henselization naive cotangent complex canonical
   comparison quasi isomorphism"`: eight hits, including `Algebra.H1Cotangent.map`,
   `Algebra.Extension.tensorH1Cotangent`, localization comparison equivalences,
   formal-smoothness tests and presentation maps. None states this comparison.
2. `msearch.py ... loogle "Algebra.Extension.Cotangent.map, Algebra.Generators.defaultHom"`:
   one hit, `Algebra.Generators.H1Cotangent.equiv_apply`, concerning a change of
   presentation for first homology, not strict henselization or derived complexes.
3. `msearch.py ... grep "hensel.*cotangent|cotangent.*hensel"`: zero Mathlib hits.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for naive-cotangent and
   strict-henselization names: no existing theorem. Read
   `Sheaf.RingTheory.NaiveCotangentComparison` (arbitrary presentations and
   characterization interfaces) and `Sheaf.RingTheory.IndEtaleNaiveCotangentAcyclic`
   (the canonical single-map cone representation), together with Mathlib's
   polynomial-presentation and cotangent functoriality declarations. The present
   statement directly reuses the latter cone and Mathlib maps, defines no second
   naive cotangent object, and does not choose an arbitrary comparison.
5. Name search in `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and
   `Sheaf` found no collision for `strictHenselization_naiveCotangent_iso`.

Validation: the prescribed `scompile.py NK lem-sfb-strict-henselization-naive-cotangent`
compiled the sandbox and library module cleanly (6.3 s and 2.8 s), without warnings.
The first compile exposed that the Abelian instance was only privately imported
by a proof dependency; adding the direct public `ModuleCat.Abelian` import fixed it.
Line-length warnings in the initial draft were repaired before the clean compile.
No library build or direct git operation was run.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
