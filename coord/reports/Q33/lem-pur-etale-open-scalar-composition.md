## Worker report

Existing declaration delivery: no Lean module is added. The published module
`Sheaf.Paper.OpenScalarSiteCoherence` already contains both clauses, as
`AlgebraicGeometry.ProEtale.OpenScalarSite.etale_scalar_comp` and
`AlgebraicGeometry.ProEtale.OpenScalarSite.etale_scalar_id` (lines 198 and 221).
Their full signatures and proof docstrings were read locally and checked against
the live source with `scompile.py --source Sheaf.Paper.OpenScalarSiteCoherence`.
Only the item's `lean` field changes. Its `statement` is the composition signature
verbatim; `declarations` also records the separate identity clause.

Hypothesis and clause correspondence:

- Finite commutative unital rings: `{A B : Type (u + 1)}` with `[CommRing A]`,
  `[CommRing B]`, `[Finite A]`, `[Finite B]`; the unital map is `(φ : A →+* B)`.
- Arbitrary schemes: `{V U X : Scheme.{u}}`, with no geometric finiteness,
  separatedness, or Noetherian hypothesis. Rename the source's V,U,X to the
  node's U,V,T, and its k,j to the node's a,b.
- Ordinary unbounded constant-coefficient derived categories: the argument
  `(L : Etale.DerivedCategoryModule A V)` is an arbitrary object of
  `DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  The namespace `ProEtale.OpenScalarSite` does not change the explicitly
  ordinary-etale types in these two declarations.
- Derived scalar extension Q is `Etale.scalarExtension φ X` (and similarly
  on U and V). This is the published constant-coefficient scalar extension,
  with its K-flat representative normalization, not an arbitrary functor.
- Exact inverse image is `(Etale.upperStar (ModuleCat R) j).mapDerivedCategory`.
  `properOpenCoefficientPullbackIso φ j` is the exactness transport of
  `scalarPullbackIso φ j`. In functor order it has type
  `Q_X ⋙ j_B^* ≅ j_A^* ⋙ Q_U`, the node's lambda. Its inverse therefore
  has the direction used in the prescribed transpose.
- Open immersions are `(k : V ⟶ U) (j : U ⟶ X)` with
  `[IsOpenImmersion k] [IsOpenImmersion j]`; their composite is `k ≫ j`.
- Exact extension by zero is
  `(Etale.openImmersionLowerShriek (ModuleCat R) j).mapDerivedCategory`.
  No derived right image or compactification-dependent extension is substituted.
- The node's beta is `(Etale.openScalarExtension φ j).hom.app L`, the
  canonical natural isomorphism used by `etaleOpenTensorComparisons`.
  Its `q_normalized` field fixes the ordinary summand/tensor comparison on
  K-flat representatives; `q_unique` makes that normalization unique.
  The `q_restricts` field identifies its restriction using the open units.
  Equivalently, the definition of `openScalarExtension` is uniqueness of
  the composite scalar/open left adjoints, so its inverse is the open mate
  of the inverse scalar/restriction mate. Transporting the latter along
  `leftDerivedUpperStarIsoMapDerivedCategory` gives the inverse of
  `properOpenCoefficientPullbackIso`. The open Hom equivalence thus sends
  beta inverse to Q(unit) followed by lambda inverse, exactly the definition
  of `properOpenCoefficientOpenInverse`. This is also the normalization
  argument read in `compactScalarOpen_normalization`; that theorem uses the
  same composite-adjunction construction expressed with left-derived pullback.
  No arbitrary isomorphism or extra normalization hypothesis is introduced.
- Set C_R to `Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
  (ModuleCat R) k j`. Its type is composite extension isomorphic to iterated
  extension. Therefore `c_R = C_R.inv`, not `C_R.hom`. Its definition is
  `Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComp ...)`
  followed by `Functor.mapDerivedCategoryCompIso`, so it derives precisely
  the canonical comparison of `lem-cbc-extension-zero-composition`.
- In left-to-right Lean composition order, the existing theorem states
  `Q(C_A.hom) ≫ beta_b ≫ b_!(beta_a) ≫ C_B.inv = beta_ba`.
  Precomposing both sides with `Q(C_A.inv)`, cancelling the inverse pair,
  and reversing the equality gives
  `Q(c_A) ≫ beta_ba = beta_b ≫ b_!(beta_a) ≫ c_B`.
  This is exactly the displayed node equation, whose TeX composition is
  written in right-to-left order. It is an equivalent equation, with no
  strengthening or weakening and no additional conclusion.
- Identity clause: `etale_scalar_id` states
  `beta_id ≫ extensionId_B.hom = Q(extensionId_A.hom)` on every L.
  Thus beta is the identity under those canonical identity-open identifications.
- Both signatures quantify over arbitrary unbounded L. They contain no bounded
  flat representative, constructibility, torsion-object, or scalar-flatness
  hypothesis. The bounded flat representative in the separate
  `scalar_site_square` theorem is not used by either declaration recorded here.

Dependency declarations inspected and used to identify the objects:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-derived-categories`: `AlgebraicGeometry.Etale.DerivedCategoryModule`,
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, publicly available
  from its recorded module `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `lem-pur-derived-change-of-rings`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`,
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`,
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
  Its representative characterization fixes the canonical tensor comparison;
  the exact etale scalar specialization above is already published.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-pbc-extension-by-zero` and its adjunction:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
  `openImmersionLowerShriekUpperStarAdjunction`, and
  `openImmersionLowerShriekAdjunction`,
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `lem-coef-etale-open-tensor`:
  `AlgebraicGeometry.Etale.EtaleOpenTensorComparisons` and
  `etaleOpenTensorComparisons`, `Sheaf.SixFunctors.EtaleOpenTensor`;
  its fixed `openScalarExtension` is defined in the public dependency
  `Sheaf.SixFunctors.EtaleOpenTensorDefs`.
- `def-pur-open-coefficient-normalizations`:
  `AlgebraicGeometry.Etale.properOpenCoefficientPullbackIso` and
  `properOpenCoefficientOpenInverse`, `Sheaf.Paper.ProperOpenCoefficientRefinement`.
- `lem-cbc-extension-zero-composition`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekComp` and
  `openImmersionLowerShriekComp_coherence`,
  `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`;
  the derived comparison is in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.
- Proof dependency `lem-sp-open-scalar-site-coherence`: the two existing
  declarations recorded by this delivery, `Sheaf.Paper.OpenScalarSiteCoherence`.

Source reading: `literature/stacks-project/sites-cohomology.tex`,
`remark-compose-base-change` (0E46) and `lemma-j-shriek-and-tensor` (0GL1).
The former composes adjunction base-change mates; dually its unit calculation
gives the open law. The latter is the unbounded open tensor identity.

Edge cases checked: empty source/open, identity a or b, zero derived object,
zero coefficient ring where a unital ring map exists, nonflat coefficient
quotients, and inputs unbounded in both directions. Neither existing signature
excludes them. The identity theorem explicitly covers the identity open rather
than silently treating identity extension as definitionally equal to identity.
The coefficient universe is the published u+1 convention; there is no imposed
equality between the site's object and morphism universes.

Searches (2026-10-21):

- `msearch.py ... leanfinder "Scalar extension and extension by zero on unbounded
  etale derived categories respect composition and identity open immersions"`:
  eight hits, mainly `Scheme.Modules.restrictFunctorComp` and scheme open
  immersion formulas; none states the coefficient law.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.NatIso"`:
  zero hits; NatIso was not recognized by the service.
- `msearch.py ... grep
  "openScalarExtension|etale_scalar_comp|scalar.*[Cc]omp.*[Ss]hriek"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Canonical scalar comparison for extension by zero
  respects composition of open immersions"`: eight hits, including ordinary
  scheme module restriction composition and unrelated scalar composition;
  none is this derived coefficient comparison.
- `rg -n 'openScalarExtension|etale_scalar_comp|properOpenCoefficientOpenInverse'
  lean/WeilConjectures lean/Sheaf`: found the two exact ordinary-etale clauses
  in `Sheaf.Paper.OpenScalarSiteCoherence`, the canonical balancing data,
  and the open coefficient normalizations described above.
- `rg -n 'lem-pur-etale-open-scalar-composition' lean/WeilConjectures`: no hits.
  `dag/lean_names_upstream.json` has no `etale_scalar_comp` match.

No statement correction, new node, dependency repair, or disputed statement.
No new proof is written; both published comparison theorems currently have
the stage-2 `sorry` bodies owned by their existing DAG node. Under brief-stage2
section 1, an existing-declaration-only attachment introduces no file to compile.
The required `deliver2.py --no-push` validation nevertheless generated and
compiled its existing-declaration check on the server and returned
`OK (dry run): commit e77cced2347 passes the preflight and compiles`.

## Second reading by Q33

I reread the item and the two published signatures after preparing the record;
no other agent was started, as required by the dispatcher brief. The finite-ring
and unital-map binders match; the schemes and open immersions are arbitrary;
the typed categories are ordinary etale unbounded derived categories; the
balancing map is precisely the fixed `openScalarExtension` of the tensor
dependency, with its canonical unit normalization as described above.

The point requiring care was the direction of the compositor: the existing
theorem uses composite-to-iterated `C_A.hom` first, while the node uses
iterated-to-composite `c_A`. Writing `c_R = C_R.inv` and cancelling the
isomorphisms yields the node's equation exactly. The record and this report
explicitly state that conversion. The second declaration supplies the entire
identity clause; the first declaration alone would have omitted it, so both
are listed in `lean.declarations`. The bounded hypothesis belongs exclusively
to the site's separate scalar/site square and is absent from both chosen
signatures. No mathematical mismatch or source correction was found.
