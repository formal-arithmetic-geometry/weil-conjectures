## Worker report

The module `Sheaf.CategoryTheory.Sites.InverseImageDifferentials` states the node with four
sorry theorems: `CategoryTheory.SheafDifferentials.inverseDifferentials_existsUnique`,
`inverseDifferentials_naturality`, `inverseDifferentials_identity`, and
`inverseDifferentials_composition`. All helper definitions have real data. The JSON statement,
proof, and proof dependencies are unchanged. Its statement dependencies gain the already
landed `def-weil-pbc-algebraic-inverse-image`, whose recorded general-universe interface is
used verbatim.

Source read: `literature/stacks-project/sites-modules.tex`, labels
`lemma-differentials-sheafify` (08TP), lines 6035–6059, and
`lemma-pullback-differentials` (08TQ), lines 6061–6088, including both proofs.
08TP identifies the sheafification with the free-module relation cokernel. 08TQ identifies
inverse image with target differentials and explicitly requires compatibility with the
universal derivation. The node's last sentence records the naturality and coherence of
these same generator-preserving comparisons; those are retained as three equations.

Hypothesis and clause matching:

- Sites small in a common universe of values: `C : Type uC`, `Category.{vC} C`,
  `EssentiallySmall.{w} C`, `J : GrothendieckTopology C`, and the analogous binders for
  `D,K` and (for composition) `E,L`. All value categories use `w`. The site object and
  morphism universes remain independent; no equality between them is imposed. Small-model
  sheafification and its locally-bijective characterization are supplied by Mathlib's
  existing transport lemmas inside definitions, rather than imposed as hypotheses.
- Geometric morphism with left exact left adjoint: the recorded `GeometricMorphism`
  has `inverse`, `direct`, `adj` and `leftExact`. The theorem takes exactly that structure.
- A morphism of sheaves of commutative rings: `A B : Sheaf J CommRingCat.{w}` and
  `φ : A ⟶ B`. `AI,BI,ψ` are its transported presentation on the target site.
- The sheafification of sectionwise ring differentials: `omega φ` is
  `PresheafOfModules.sheafification (𝟙 (ring B).obj)` applied to Mathlib's
  `relativeDifferentials' φ.hom`. That presheaf's object at U is
  `CommRingCat.KaehlerDifferential (φ.hom.app U)`, i.e. the recorded ring differential
  construction. `ring` only forgets commutativity. `omega φ` lives in the recorded
  `ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
- Its derivation: `derivation φ` is Mathlib's `derivation' φ.hom` postcomposed with the
  module sheafification adjunction unit. `d φ` is the same map on underlying set sheaves.
  The `ULift` on these sets is exactly the one required by the recorded algebraic
  inverse-image interface; it neither changes the differential module nor its sections.
- Equip inverse-image rings/modules by finite-product transport: `FA` and `F` are the
  recorded `SheafOfModules.AlgebraicInverseImageOfUniverses` for A and B. Its graph
  equations on every test sheaf express the inverse finite-product formulas, and its
  natural `moduleUnderlying` comparison fixes module morphisms. These are presentations
  of the objects the node explicitly says to equip, not extra exactness, linearity or
  site-functor hypotheses. `RingMapCompatibility` says that `ψ` is the image of `φ`
  under those very underlying-ring comparisons. In particular the source-ring comparison
  is not an arbitrary isomorphism of sets.
- Canonical isomorphism of inverse-B-module sheaves: the primary conclusion is
  `∃! e : F.modules.obj (omega φ) ≅ omega ψ, IsComparison f φ ψ F e`.
  The isomorphism lives in the module-sheaf category, including linearity in its type.
  Unique normalization gives the meaning of canonical, without choosing an unspecified
  object from an existence theorem.
- Carries inverse image of the universal derivation to the universal derivation:
  `IsComparison` is the equality
  `f.inverse.map (d φ) ≫ comparison f φ ψ F e = F.ringUnderlying.hom ≫ d ψ`.
  `comparison` uses the inverse of `F.moduleUnderlying` and the underlying map of `e`;
  it retains all coefficient and module identifications explicitly.
- Naturality in commutative ring squares: `squareDerivation` pulls back the target
  derivation along b and restricts scalars. `squareMap` is the actual canonical map,
  constructed by Mathlib's sectionwise universal property and sheafification adjunction.
  `squareSetsMap` forgets this map to underlying sets. The naturality theorem takes
  `a ≫ φ' = φ ≫ b`, its transported square, and the equation identifying bi with the
  transported b; its conclusion is the commuting square for these canonical differential
  maps and any normalized comparisons e,e'. It never substitutes an arbitrary map for
  the differential square map. Equality on underlying set sheaves is faithful and is
  therefore equality of the corresponding semilinear module-sheaf maps.
- Identity: the identity theorem uses the identity set-sheaf functor, its algebraic
  transport F, the identity ring comparison, and the universal-derivation normalization.
  Its equation identifies the resulting differential comparison, after the specified
  module identification, with the identity. It does not demand equality between two
  separately presented module structures.
- Composition: `g.comp f` is the recorded geometric composition. F,G,H present the
  successive and composite algebraic inverse images; `hB` is their canonical ring
  comparison equation. The three normalized comparisons satisfy exactly
  `comparison (g.comp f) = g.inverse.map (comparison f) ≫ comparison g`.
  This equation includes the module comparisons through the definition of `comparison`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `CategoryTheory.GeometricMorphism`
  and `CategoryTheory.GeometricMorphism.comp`, including full fields and composite
  adjunction. `inverseMate` and `inverseIso` were read and are not needed here.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`, full signatures and docstrings. The module version of this
  same sheafification is `PresheafOfModules.sheafification` and its adjunction in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`, including their signatures and
  universal-property docstrings. The bundled form is `CommRingCat.KaehlerDifferential`;
  `relativeDifferentials'` and `isUniversal'` are its existing presheaf form in
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, including
  its general-site docstring. Mathlib's `SheafOfModules`, `Hom`, `toSheaf`, and
  `SheafOfModules.restrictScalars` supply all module categories and maps.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`:
  `SheafOfModules.AlgebraicInverseImageOfUniverses`, with every ring/module graph equation
  and the naturality of `moduleUnderlying`; its full declaration was read.

The three proof lemmas about exactness, free modules, and the differential cokernel have
no recorded Lean declarations on the base and therefore no modules to import. Their DAG
statements and source proofs were read; the theorem docstrings preserve that proof route.
No independent notion is missing: the helper definitions in this module construct exactly
the objects and arrows named in this node, under the authorized owning-module helper rule.
There are no new nodes and no dependency record repairs.

Edge cases checked mathematically: empty sites and their terminal sheaf categories;
zero ring sheaves (no Nontrivial hypotheses); identity ring maps (zero differential module);
identity geometric morphisms; successive inverse images with independently presented but
canonically identified rings/modules; arbitrary ring squares, without injectivity,
surjectivity, flatness, or existence of a site functor. None is excluded by the binders.
The common value universe is explicit, and using an essentially small site also permits
larger presentations of the same small site. No statement fault or dispute was found.

Searches actually run:

- `msearch.py leanfinder`: “inverse image of sheaves along geometric morphism commutes
  with Kahler differentials”; eight hits, led by the presheaf differential map and
  sectionwise ring maps. No sheaf/geometric-morphism comparison.
- `msearch.py loogle`: `"KaehlerDifferential", "map"`; twelve ring-level hits, including
  `KaehlerDifferential.map`, `map_D` and `mapBaseChange`; no geometric-morphism statement.
- `msearch.py grep`: `relativeDifferentials|sheafDifferentials|inverseImageDifferentials`;
  five hits in Mathlib's presheaf differential construction, no sheaf comparison.
- `msearch.py leansearch`: “sheaf of relative Kahler differentials sheafification universal
  derivation”; eight hits on ring and presheaf differentials, including
  `relativeDifferentials'` and `isUniversal'`. These definitions are reused.
- `rg` on upstream WeilConjectures and project `lean/Sheaf` for the node id,
  `relativeDifferentials`, `sheafDifferentials`, and `geometricInverseImage`: upstream
  scheme-specific differential modules exist, but require a morphism of schemes, and
  do not cover arbitrary sites or geometric morphisms. Read the complete definitions
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`, and
  `relativeDifferentialsHomEquiv` in the upstream Modules/Differentials module.
- `grep -rn` of the exact item id in upstream WeilConjectures: no hits. `rg` on upstream,
  side sources and `dag/lean_names_upstream.json` for the proposed namespace and main
  theorem names: no duplicates.
- `blueprint_refs.py search 'sheaf differentials'`: zero blueprint nodes. `ancestor`
  identifies `lem-trf-local-term-locality`. DAG keyword search finds the existing 08TP
  cokernel theorem, not a separately recorded definition of sheaf differentials.

Validation uses the prescribed `scompile.py` wrapper. Initial elaboration repairs made
all coefficient and site universes explicit, supplied Mathlib's existing small-model
sheafification instances inside definitions, and corrected the orientation of the
ring-square naturality equation. No mathematical hypothesis or conclusion changed.

## Second reading by Q75

No second worker reading was performed: the 2026-10-17 direct-delivery policy leaves the
independent reading to the maintainer. The worker checked each clause again against the
node and both Stacks proofs. During this check the base-ring inverse-image isomorphism
was replaced by the recorded algebraic transport FA so its canonical ring operations are
explicit as well. The naturality equation uses a constructed canonical square map;
identity and composition retain the underlying module comparisons.

Final file-only validation: `scompile.py Q75 lem-trf-topos-inverse-image-differentials
lean/Sheaf/CategoryTheory/Sites/InverseImageDifferentials.lean` returned exit code 0 for
both the sandbox compilation and the final library-path compilation, with no errors or
warnings. The file has 303 lines, every line at most 100 characters, `autoImplicit false`,
and exactly four postponed proofs, each a named theorem corresponding to a node clause.
