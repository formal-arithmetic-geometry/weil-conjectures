## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero` states
`AlgebraicGeometry.ProEtale.proEtale_extension_by_zero`, with `sorry` as its whole
proof. The node's natural statement and all existing dependency records are unchanged.
The helper declarations package the existing geometric stalk as a functor, apply the
existing extension functor termwise, and construct the canonical scalar mate. Their
data is explicit. No new notion or independent theorem is introduced.

Hypotheses and clauses, in the order of the node:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  These are the coefficient universes of the recorded extension functor; `ModuleCat.{u + 1} A`
  gives all modules in the larger site universe. No nonzero-ring assumption is present.
- Schemes and the open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j]`. The site is exactly `Scheme.ProEt.topology`, with object universe
  `u+1` and morphism universe `u`, as in the recorded geometric-stalk definition.
- The extension functor is the dependency's `openImmersionLowerShriek
  (ModuleCat.{u + 1} A) j`. No alternate extension presheaf or sheafification is defined.
  For constant coefficients, module-valued sheaves are the fixed-module presentation
  of sheaves of modules over the constant ring sheaf (Stacks 09AE(3)).
- Exactness is the conjunction of `PreservesFiniteLimits` and `PreservesFiniteColimits`
  for that existing functor. Its additivity is already provided by the upstream module.
- The left-adjoint clause is `Nonempty (openImmersionLowerShriek ... j ⊣
  openImmersionRestriction ... j)`. This is the actual restriction functor, whose
  sections are evaluation on the composite into X. The recorded
  `upperStarIsoOpenImmersionRestriction` canonically identifies it with inverse image.
  The statement also gives the adjunction between the termwise functors on complexes.
- Degreewise action is the real abbreviation `openExtensionCochain A j :=
  (openImmersionLowerShriek ... j).mapHomologicalComplex (.up ℤ)`. Mathlib's construction
  takes degree n to `j_!(K.X n)`, differential to `j_!(K.d n m)`, and chain morphism to
  `j_!(f.f n)`. Its source consists of all cochain complexes indexed by ℤ.
- A geometric point in U is quantified as `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ U)`, and its point in X is `y ≫ j`. The first stalk case is a
  natural isomorphism between whole complex functors
  `openExtensionCochain A j ⋙ (geometricModuleStalkFunctor A (y ≫ j)).mapHomologicalComplex`
  and `(geometricModuleStalkFunctor A y).mapHomologicalComplex`. This includes all
  degrees, differentials, and chain morphisms, rather than merely abstract degreewise
  module isomorphisms. Nonempty here asserts existence of this natural isomorphism;
  no definition chooses data from this statement.
- A geometric point outside U is `y : Spec (.of Ω) ⟶ X` with
  `¬ ∃ z : Spec (.of Ω) ⟶ U, z ≫ j = y`. For an open immersion, factoring the point is
  equivalent to its underlying point lying in the open image: if it lies there, the
  full morphism Spec Ω factors uniquely through the open subscheme. The conclusion
  `IsZero` is on the entire stalk cochain complex of `j_!K`, for every complex K.
- The coefficient clause quantifies every `(B : Type (u + 1)) [CommRing B] [Finite B]`
  and every `φ : A →+* B`, with no injectivity, surjectivity or algebra hypothesis.
  Restriction is `sheafCompose _ (ModuleCat.restrictScalars φ)`: it keeps each section
  group and restriction map and changes the action to a • m = φ(a) • m. This is the
  fixed-module presentation of `SheafOfModules.restrictScalars` in the dependency.
  `openExtensionScalarMap φ j` is constructed, not postulated: `mateEquiv` transposes
  the identity between restriction-then-scalars and scalars-then-restriction along
  the two recorded `openImmersionLowerShriekAdjunction`s. The map has direction
  `Res_U ⋙ j_!^A ⟶ j_!^B ⋙ Res_X`. The two `IsIso` assertions apply to this specified
  map and to its termwise extension. The inverse of its `asIso` is exactly the
  node's canonical `Res_X j_!^B K ≅ j_!^A Res_U K`. This normalization rules out an
  arbitrary chosen map or arbitrary natural isomorphism.

Dependency declarations inspected and used:

- `def-weil-extension-by-zero`: the complete module
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs` in the
  side framework was read, including its coefficient universes, `localizationLowerShriek_eq`,
  `openImmersionLowerShriek`, `openImmersionRestriction`,
  `openImmersionLowerShriekAdjunction`, `upperStarIsoOpenImmersionRestriction` and
  the exactness instance. This relocated module avoids the obsolete duplicate imports.
- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, and its full constant-coefficient
  construction were read. Its site is the same `Scheme.ProEt.topology` used here;
  this module is also imported transitively through the stalk dependency.
- `def-weil-pbc-scheme-conventions` is a convention-only record. Its relevant notions
  are `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-proetale-geometric-stalk`: `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`,
  `AlgebraicGeometry.Scheme.proEtaleGeometricNeighbourhoodForget`,
  `proEtaleGeometricStalkDiagram`, `proEtaleGeometricStalk`, and
  `proEtaleGeometricFixedModuleStalk`. The helper stalk functor is the composite of
  `sheafToPresheaf`, whiskering by this exact neighbourhood-forget functor, and `colim`.
  Its value is definitionally the recorded fixed-module stalk. No new neighbourhood
  category or stalk object is substituted.
- `def-pc-sheaf-restrict-scalars` is a Mathlib leaf with no `lean` record, as allowed:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`. Its full signature and implementation were read.
  The fixed-module version is Mathlib's `ModuleCat.restrictScalars` under `sheafCompose`.
  Both constructions retain section groups and maps, with precisely the same action.

The stated proof dependencies are retained as proof-only imports:
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk`,
`Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`, and the Mathlib module
sheafification/change-of-rings interfaces. The abstract derived-category dependency
is already reached through `ProEtaleDerivedCategory`. The docstring contains the
node's localization, representative-class stalk argument, scalar identity followed
by sheafification, and termwise argument, so a stage-3 worker can start from it.

Edge cases checked:

- Empty U: the inside case has no points; the outside case says every stalk complex
  vanishes. The extension is zero, as required by the construction.
- Empty X: its open subscheme is empty and both point clauses are vacuous.
- Identity open immersion: every geometric point has its own unique lift, and the
  stalk comparison identifies the original complex with itself.
- The zero coefficient ring is permitted; its module category is trivial. Coefficient
  maps into the zero ring and arbitrary noninjective/nonsurjective coefficient maps
  are included. A unital map out of the zero ring already forces a zero target.
- Unbounded complexes and negative degrees are included; there is no boundedness,
  constructibility, nonzero-complex or nonzero-stalk assumption.
- Geometric points remain in the chosen bound. No equality of site object and
  morphism universes was imposed. No conservativity of ordinary geometric stalks
  is asserted or used.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`: “extension by zero proetale exact adjunction geometric
  stalk restriction of scalars”. Eight hits, about ordinary module stalks and smooth
  sheaves (including `Scheme.Modules.restrictStalkNatIso`); no complete match.
- `msearch.py ... loogle`: `SheafOfModules.restrictScalars, CategoryTheory.Adjunction`.
  Zero hits.
- `msearch.py ... grep`: `extension[Bb]yZero|lowerShriek|LowerShriek|openImmersionLowerShriek`.
  Zero Mathlib hits for the requested pro-etale statement.
- `msearch.py ... leansearch`: “extension by zero exact left adjoint geometric stalk
  proetale”. Service unavailable (Internal Server Error), as recorded by the tool.
- `rg` in the source project's `WeilConjectures/SixFunctors/ProEtale` found the
  already-recorded extension functor and its exactness/adjunction, plus projection,
  complement and comparison results. None states the two geometric-stalk cases
  and canonical coefficient comparison together. `grep -rn` for the exact node id
  returned no source occurrence.
- `rg` in `lean/Sheaf` found the separate `ProEtaleExtensionZeroComparison` module
  (etale/pro-etale comparison and composition coherence) and unrelated topological
  or etale extension results; none states this node.
- Exact-name `rg` across Mathlib, the source project, and `lean/Sheaf` found no
  declaration named by this delivery.

Sources opened: the blueprint node in the launcher's local literature mirror;
Stacks `proetale.tex`, Definition `definition-extension-zero` (09AE), and
`sites-modules.tex`, Lemmas `lemma-extension-by-zero` (03DI),
`lemma-extension-by-zero-exact` (03DJ), and `lemma-sheafification-presheaf-modules` (03CY).
The framework note `coord/pefw-upstream-framework.md` was also read.

No statement correction, disputed statement, new DAG node, or dependency-module repair
was needed. The helpers belong to this node and are all listed in `lean.declarations`.

Validation: the final module passed `scompile.py` locally with its side overlay,
including both sandbox and library-name passes (5.4 and 5.5 seconds), without errors
or warnings. `stage2_delivery.check_lean_text` found no mechanical text faults.
The required `deliver2.py --no-push` result is recorded below after execution.

Dry run completed successfully: `deliver2.py NR lem-cbc-proetale-extension-zero --no-push`
printed `OK (dry run)` for commit `1b11ca2b9d`: compilation and preflight passed except
for the independent second reading, which the second reader supplies. Nothing was pushed.

## Second reading by NR

I independently opened the node and the complete module. The node introduces a finite
commutative ring (A), schemes (U,X), and an open immersion (j:U\hookrightarrow X).
The module renders these as `A : Type (u + 1) [CommRing A] [Finite A]`,
`{U X : Scheme.{u}}`, and `(j : U ⟶ X) [IsOpenImmersion j]`; the chosen site is
`Scheme.ProEt.topology` and the coefficient category is `ModuleCat.{u + 1} A`.
This has the node's fixed small-site universes and does not add a Noetherian,
separated, characteristic, nonzero-ring, or boundedness hypothesis.

The exactness clause is rendered by the conjunction of
`PreservesFiniteLimits (openImmersionLowerShriek ...)` and
`PreservesFiniteColimits (...)`. The left-adjoint clause is the recorded
`openImmersionLowerShriek ... ⊣ openImmersionRestriction ...`, and the degreewise
clause uses the canonical `mapHomologicalComplex (.up ℤ)` abbreviation
`openExtensionCochain`; these are the dependency functors, with no private
replacement. The stalk-inside-(U) clause is rendered as a natural isomorphism of
whole complex functors, hence gives the stated pointwise stalk prescription for every
complex and is compatible with differentials and maps as required by the source proof.
The outside-(U) clause quantifies the same algebraically closed geometric point and
factorization negation, then gives `IsZero` for every source complex. The coefficient
clause quantifies every finite commutative (B) and every ring homomorphism
`φ : A →+* B`; `openExtensionScalarMap` is the explicitly defined mate of the
identity scalar square, and the two `IsIso` conclusions (sheaves and complexes) give
exactly the inverse canonical comparison
`Res j_!^B K ≅ j_!^A Res K` in the node. No mismatch was found, and the Lean file and node
statement were preserved.

I checked the empty open, empty ambient scheme, identity immersion, zero coefficient
ring, arbitrary (including noninjective and nonsurjective) coefficient maps, negative
and unbounded complex degrees, and the vacuous point cases. All are covered by the
same binders; no accidental nonemptiness, characteristic, conservativity, or universe
restriction was added.

I repeated the existing-declaration searches with `rg` over Mathlib, the source
`WeilConjectures` tree, and `lean/Sheaf`, and independently through `msearch.py`: LeanFinder query
“An open immersion of schemes induces an exact extension by zero on module sheaves
and its geometric fibres vanish on the complement” returned eight ordinary scheme
module-restriction hits, none on the small pro-etale site; Loogle query
`CategoryTheory.Functor.mapHomologicalComplex, CategoryTheory.Adjunction` returned
zero hits; grep query `extensionByZero|extension_by_zero|openImmersionLowerShriek|stalk.*[Ll]ower[Ss]hriek`
returned zero Mathlib hits. LeanSearch query “The geometric stalk of extension by zero
vanishes outside an open subscheme and equals the original stalk inside” was unavailable
(Internal Server Error), rather than evidence of absence. Only the recorded lower-shriek, pro-etale site, geometric-stalk,
and Mathlib scalar-restriction declarations were found; no complete statement or
competing definition exists. I read each dependency signature and source docstring,
including the relocated lower-shriek framework and the fixed-module geometric stalk.
The module compiles cleanly with `scompile.py`, and `deliver2.py --no-push` passes its
mechanical checks. The worker's declarations, imports, proof docstring, and verbatim
node `lean.statement` agree with the file.

The literature files are absent in the local mirror, so I read the exact server copies
by a read-only SSH command: the blueprint lemma and its unit, `proetale.tex` Definition
`definition-extension-zero` (09AE), the pointed-neighbourhood definition and Lemmas
`lemma-cofinal-etale` (0F6B) and `lemma-geometric-lift-to-cover` (0F6C), and
`sites-modules.tex` Lemmas `lemma-extension-by-zero` (03DI),
`lemma-extension-by-zero-exact` (03DJ), and
`lemma-sheafification-presheaf-modules` (03CY). These assume an arbitrary scheme/site;
there is no hidden finiteness hypothesis on the scheme or the modules. Constant-ring
module sheaves have the fixed-module-valued presentation used by the recorded upstream
functor, and the coefficient mate uses its actual adjunction. I also read that module
through `scompile.py --source` to verify the current server interface. The stanza of
`ProEtaleGeometricStalk` used here forms colimits in `ModuleCat.{u + 1} A` over precisely
the pointed weakly etale neighbourhoods; the helper adds only its functorial action.
There are no new or repaired dependency modules in this delivery. The only change of
the second reading is this report. The final independent compile passed both wrapper
passes (8.9 and 5.0 seconds), without errors or warnings.
