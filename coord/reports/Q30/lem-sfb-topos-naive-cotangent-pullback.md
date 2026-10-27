## Worker report

The module `Sheaf.CategoryTheory.Sites.InverseImageNaiveCotangent` states
`CategoryTheory.SheafPolynomialCotangent.inverseImage_naiveCotangent`, with its
sole theorem proof `sorry`. Its auxiliary definition `liftedVariables` constructs
the actual variable map into the existing polynomial sheafification; its auxiliary
structure `InverseComparison` spells out the canonical comparisons and their
derived isomorphism. No mathematical theorem is proved here, and no definition
has postponed data.

Source read: `literature/stacks-project/sites-modules.tex`,
`lemma-pullback-NL` (Tag 08TZ), entire statement and omitted-proof hint to the
differential comparison; also `lemma-NL-up-to-qis` (08TY), which supplies the
standard two-term presentation. The five-step proof docstring reproduces the
accepted node's polynomial, kernel-square, quotient, differential/tensor and
chain-localization argument. The item is not a blueprint unit statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Sites small in a common sheaf universe: `universe u`, `{C D : Type u}`,
  `[SmallCategory C] [SmallCategory D]`, and Grothendieck topologies `J`, `L`.
  These are the small site representatives in the node's common size bound,
  exactly the convention of the recorded polynomial-cotangent dependency. The
  derived category is that dependency's standard enlarged localization; no
  equality between a derived Hom universe and the coefficient universe is imposed.
- A geometric morphism from sheaves on the target site to sheaves on the source
  site: `g : GeometricMorphism (Sheaf L (Type u)) (Sheaf J (Type u))`.
  The direction matches the node: its inverse sends `J`-sheaves to `L`-sheaves.
  Its adjunction and finite-limit preservation are the fields of the existing
  `GeometricMorphism`, with no extra exactness or flatness hypothesis.
- A map of commutative ring sheaves: `f : A ⟶ B`, with
  `A B : Sheaf J CommRingCat.{u}`.
- The pulled-back rings and ring map are `AI`, `BI`, `fi`, with the existing
  algebraic inverse-image presentations `IA`, `IB`. The hypothesis `_hf` is
  exactly `SheafDifferentials.RingMapCompatibility g f fi IA IB`, expressing
  that `fi` is the inverse image of `f`, rather than an arbitrary second ring
  map. These parameters describe the transported objects and their operations;
  they do not assume the cotangent comparison. Algebraic inverse images exist
  by `geometric_inverse_image_exact`. The already-landed definition node
  `def-weil-pbc-algebraic-inverse-image` is added to `stmt_deps` to name this
  interface explicitly.
- The standard polynomial `P=A[B]`, its evaluation kernel, locally generated
  kernel square, and differential term are the dependency's `polynomialSheaf`,
  `evaluation`, `kernelIdeal`, `LocallyInKernelSquare`, and `differentialTerm`.
  Nothing is redefined. `canonical f` is its identity-generator presentation.
- `K : Model (canonical f)` is exactly the standard complex in degrees -1,0.
  `Model.quotient_surjective` and `Model.quotient_kernel` characterize its
  conormal quotient; `Model.degreeZero` identifies its degree zero term with
  the actual differential tensor; `Model.differential_formula` is
  `[j] ↦ dj ⊗ 1`; `Model.supported` gives its other zero terms.
  `KI : Model (canonical fi)` is the same construction on the target site.
  These model parameters allow every uniquely characterized representative
  of the construction supplied by the dependency, rather than assuming a new
  quasi-isomorphism or an unrelated complex.
- The comparison's polynomial lift is `InverseComparison.polynomial`.
  `coefficients`, `generatorCompatibility`, and `evaluation` normalize its
  underlying ring identification on coefficients, variables and evaluation.
  `liftedVariables` uses `MvPolynomial.X` followed by `toSheafify`, not a
  freely chosen variable map.
- The two component isomorphisms are `components (-1)` and `components 0`.
  `conormal` says that the transported class of every generalized kernel
  section maps to the class of its image under the specified polynomial
  identification. Thus the evaluation-kernel and conormal-quotient
  identifications are the canonical ones. `tensors` sends every generalized
  `b ⊗ dp` to the corresponding tensor of the transported coefficient and
  polynomial, retaining both the differential and tensor normalization.
  These formulas quantify over every test sheaf `T`; they do not assume
  surjectivity of a sheaf quotient on sections of an individual site object.
- `differential` is precisely the chain differential square. `pulled`,
  `pulledDegree` and `pulledDifferential` describe the actual termwise inverse
  image complex and its termwise identifications. This avoids adding a
  `PreservesZeroMorphisms` assumption merely to use the complex-map API.
  `chainIso_components` identifies the actual chain isomorphism with those
  same component maps.
- The displayed isomorphism in `D(Mod(BI))` is `derivedIso`. Its type uses the
  existing `localization BI` on the termwise inverse-image complex and on
  `KI.complex`; `derivedIso_eq` fixes it as the localization of `chainIso`.
  Thus the result is a derived isomorphism with its specified chain origin,
  rather than only an assertion about homology groups or a bare arbitrary
  nonempty isomorphism type. `Nonempty (InverseComparison ...)` packages all
  these normalized data simultaneously without choosing an uncharacterized
  object from an existence assertion.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`:
  `CategoryTheory.SheafPolynomialCotangent.{sets,polynomials,polynomialSheaf,
  base,evaluation,canonical,kernelIdeal,tensorD,Model,localization}` and its
  existence statement `sheaf_polynomial_cotangent_comparison`.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism`, with `inverse`, `direct`, `adj`, `leftExact`.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`:
  `SheafOfModules.AlgebraicInverseImageOfUniverses`, including all transported
  ring/module graph conditions and the natural underlying-module comparison.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`:
  `CategoryTheory.SheafDifferentials.{sets,setsMap,moduleSets,RingMapCompatibility}`;
  `omega`, `derivation` and `inverseDifferentials_existsUnique` provide the
  differential construction and the proof dependency.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the abbreviation for Mathlib's actual
  `SheafOfModules`. `CategoryTheory.siteModuleRings` is the existing ring
  forgetting in `Sheaf.Paper.RingedSiteIdeal`, imported by the presentation module.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`,
  used through the dependency's `derived` and `localization`.
- The site dependency is `CategoryTheory.Precoverage.IsSiteForCoverings`
  in `Sheaf.CategoryTheory.SiteCoveringAxioms`; here the associated topology
  and sheaf categories are the existing Mathlib ones. The size-convention
  node is explicitly a metatheoretic convention with no declaration.

Plain proof imports include the recorded exactness, tensor comparison,
bilinear universal property and local sheafification modules. The proof-only
node `lem-trf-geometric-standard-differential-comparison` has no Lean record
or Mathlib match on the read base, so there is no module of it to import.
It is not a statement dependency: the polynomial construction itself is
already defined in the recorded presentation dependency. The main proof
can establish the required polynomial normalization using its universal
property as described in the node; no dependency wait or cycle is introduced.

Edge cases checked against the definitions: zero rings and zero module sheaves
are allowed; no `Nontrivial`, nonempty-site or characteristic hypothesis appears.
Empty sites and the topology with empty covering sieves are not excluded.
The identity morphism permits the identity component maps, with canonical
polynomial identification. The statements quantify over all degrees, including
both -1 and 0, and all generalized sections, including tests with no global
sections. Quotients remain sheaf quotients, allowing locally represented
sections that are not globally represented. No finite generation,
quasi-coherence, geometric points, enough-points assumption, or flatness is added.

Searches actually run:

- `msearch.py ... leanfinder "geometric inverse image of the sheaf naive cotangent complex canonical comparison"`:
  eight ring-theoretic cotangent hits, including
  `Algebra.Extension.CotangentSpace.map_cotangentComplex` and
  `Algebra.Extension.H1Cotangent.map`; no sheaf/topos theorem.
- `msearch.py ... loogle "SheafPolynomialCotangent, AlgebraicInverseImageOfUniverses"`:
  zero hits; unknown identifier `SheafPolynomialCotangent` in the Mathlib service.
- `msearch.py ... grep "naiveCotangent|naive_cotangent|pullback.*[Cc]otangent"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Inverse image of naive cotangent complex of sheaves of rings"`:
  eight hits, including `SheafOfModules.pullback` for a continuous site functor
  and scheme/open-immersion constructions; none is this topos theorem.
- `rg` with that same cotangent regex in `lean/WeilConjectures` and `lean/Sheaf`:
  ring localization, algebraic-space naive cotangent definitions and related
  tangent-space uses, but no geometric inverse-image comparison for the
  standard sheaf complex. A direct grep for the item id in
  `lean/WeilConjectures` found nothing.
- `rg` for `inverseImage_naiveCotangent|InverseComparison|liftedVariables` in
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` found
  no declaration with any of the three proposed fully qualified names.

No statement correction, new definition node, dependency repair or
STATEMENT-DISPUTED flag is needed. The independent delivery review is performed
by the maintainer as specified in the dispatcher brief; no independent reader
was invented in this report.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
