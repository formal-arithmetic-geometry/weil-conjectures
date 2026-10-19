## Worker report

The module `Sheaf.CategoryTheory.Sites.FpStalkRealization` states
`CategoryTheory.SiteFpStalkRealization.exists_fp_stalk_realization` with `sorry`.
All other declarations are actual constructions using existing Mathlib and project
interfaces. There is no additional postponed assertion, arbitrary map, or choice
of unspecified algebraic data. The natural-language statement is unchanged.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-check-K-flat-stalks`, proof of (1), especially the paragraph realizing a
finitely presented stalk module; and `sites.tex`, `lemma-point-localize` (04H2).
Also read the recorded localized-sheaf equivalence and site-point reconstruction
modules, including their complete signatures and proof docstrings.

Hypotheses and clauses, individually:

- A site small in the coefficient universe: `C : Type u`, `[SmallCategory C]`,
  `J : Precoverage C`, `hJ : J.IsSiteForCoverings`; sheaves use
  `J.toGrothendieck`. Objects, arrows, coefficients, sets and modules all lie in
  `u`. This is the small-site encoding, not the larger pro-etale encoding.
- Finite limits: `[HasFiniteLimits C]` in the section variables, inherited by
  the theorem and every point construction that needs it.
- A commutative ring sheaf: `R : Sheaf J.toGrothendieck CommRingCat.{u}`.
  Its ring sheaf for `SheafOfModules` is its image under
  `sheafCompose _ (forget₂ CommRingCat RingCat)`; only commutativity is forgotten.
- A point: `p : GeometricMorphism (Type u) (Sheaf J.toGrothendieck (Type u))`.
  Its inverse image, adjunction and left exactness are the recorded datum.
- `R_p = p⁻¹R`: `stalkRing J p R` is the actual colimit of section rings over
  `sitePointNeighbourhood J p`. This category has objects `(U,x)` with
  `x : p.inverse.obj (h_U^#)`. The recorded reconstruction theorem identifies
  its set colimit with `p.inverse`, by the specified section-to-germ map.
  Ring operations in the RingCat colimit are the transported operations, so
  this is the algebraic inverse image ring, represented by a concrete model.
- A finitely presented module: `M : ModuleCat.{u} (stalkRing J p R)` and
  `[Module.FinitePresentation (stalkRing J p R) M]`.
- The object `U` and element `x`: the existential `n : sitePointNeighbourhood J p`
  is exactly this pair; `n.1` is `U`, `n.2` is `x`.
  `sitePointFunctor` uses `yoneda ⋙ presheafToSheaf ⋙ p.inverse`, exactly the
  sheafified representable in the statement. No subcanonical assumption appears.
- A sheaf on the localized ringed site: the existential `F` has type
  `ringedSiteModules` over the restriction of `R` to `n.1`, with topology
  `J.toGrothendieck.over n.1` on `Over n.1`.
- The point specified by `x`: existential geometric morphism `q`, with
  `q.inverse = sets (localizedNeighborhoods J p n) (...)`.
  Here `localizedNeighborhoods` is `Over.post (neighborhoods J p)` on `Over n`.
  A neighborhood is therefore `(V,y,f)` with `p⁻¹(h_f)(y)=x`, precisely the
  fiber point of 04H2. Its inverse image is the actual colimit of sections over
  these neighborhoods. This fixes the point using `x`, not an unrelated point.
- `j_U⁻¹` is restriction and `j_U q ≅ p`: the natural isomorphism `e` has
  source `J.toGrothendieck.overPullback (Type u) n.1 ⋙ sets ...` and target
  `p.inverse`. Its first normalization clause sends every representative
  section on a neighborhood `z` to `p.inverse.map (sitePointSectionHom ... s)`
  evaluated at `z.left.2`. Thus this is the canonical inverse-image comparison.
  An isomorphism of these left adjoints gives the corresponding geometric
  morphism isomorphism under their adjunctions.
- Canonical `q⁻¹R_U ≅ R_p`: `localizedRingCocone` is the original ring colimit
  cocone restricted along `(Over.forget n).op`. `localizedRingIsColimit` is
  obtained from Mathlib's initiality of `Over.forget n`; `localizedRingIso`
  is `colimit.isoColimitCocone` for this specified cocone. This explicitly
  constructs the canonical ring isomorphism on germs. `localizedModules`
  takes this cocone as coefficient datum, so its outputs already have scalars
  in `R_p` by this canonical identification.
- Canonical `q⁻¹(G|_U) ≅ p⁻¹G`, natural in every module sheaf `G`:
  `comparison` is a natural isomorphism
  `SheafOfModules.overFunctor ... n.1 ⋙ localizedModules ... ≅ stalkModules ...`.
  Its normalization clause identifies the two section germs for every `G`,
  every pointed slice neighborhood `z`, and every section `s`. Since both
  sides are section colimits, this uniquely fixes the comparison and is the
  module version of the displayed set comparison. ModuleCat morphisms and
  isomorphisms express `R_p`-linearity.
- `q⁻¹F ≅ M`: `Nonempty ((localizedModules ...).obj F ≅ M)`.
  The module stalk is Mathlib's actual varying-ring `colimitFunctor`, not a
  supplied lift or an extra exactness assumption. Its underlying set is the
  section colimit defining `q.inverse`, and its action is the colimit action.
- Finite numbers of relations and generators: the existential `a b : ℕ`.
- Matrix with entries in `R(U)`: `A : Fin b → Fin a → R.obj.obj (op n.1)`.
- `F` is the sheaf cokernel of that matrix: `α` has source and target
  `SheafOfModules.free (ULift.{u} (Fin a))` and
  `SheafOfModules.free (ULift.{u} (Fin b))`; `Nonempty (F ≅ cokernel α)`.
  The final clause evaluates the image of each basis generator at every
  `V : Over n.1`: it is the sum of the target basis sections multiplied by
  `R.obj.map V.hom.op (A j i)`. This specifies the actual matrix morphism,
  including restriction of its coefficients, rather than an arbitrary map
  between free sheaves. `ULift` places the finite index sets in the coefficient
  universe without changing the ranks.

Dependency declarations used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (public transitively).
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` (public transitively).
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `SheafOfModules.over`; `Sheaf.over` and
  `GrothendieckTopology.over` from its Sites.Over import.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf` and
  `toSheafify`, used through the recorded point/section constructions.
- `Sheaf.Paper.SitePointReconstructionSets`: `sitePointNeighbourhood`,
  `sitePointFunctor`, `sitePointSectionHom`, `site_point_reconstruction_sets`.
  This existing, recorded proof dependency is also added to `stmt_deps`, since
  the concrete stalk construction uses its cofilteredness conclusion.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor`:
  `PresheafOfModules.colimitFunctor`, `ModuleColimit.ιM`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward`:
  `PresheafOfModules.pushforward₀`.
- `Mathlib.CategoryTheory.Filtered.Final`: `Over.initial_forget`,
  `IsCofiltered.over`; `Functor.Final.isColimitWhiskerEquiv`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: `free`, `freeHomEquiv`,
  `freeSection`; cokernels use the inherited abelian module-sheaf category.

Proof-only imports retain the recorded localized-sheaf equivalence and the two
Mathlib slice-adjoint/finite-limit preservation modules. Sectionwise sheaf limits
are already available through the public sheaf-module imports. The proof node
`lem-trf-geometric-inverse-image-exact` has no declaration, mathlib_match or closed
upstream audit, so there is no module for that proof-only import; its exactness
argument is retained in the theorem's complete natural-language proof.

Edge cases checked: `a=0` and `b=0` are allowed, with empty lifted index types and
empty sums; neither is excluded by a positivity hypothesis. A zero ring and zero
module are allowed. Point-neighborhood nonemptiness is supplied by cofilteredness,
not an extra chosen neighborhood. A site with no point makes the quantification
inapplicable; the theorem does not assume a point exists. No subcanonicity,
constant-coefficient, enough-points, or flatness hypothesis is added. No assertion
about K-flatness is included. All universe parameters are explicit and
`autoImplicit` is false.

Searches performed using the prescribed `msearch.py` wrapper:

- LeanFinder: "Every finitely presented module over the stalk ring of a site point
  is realized as a finite matrix cokernel on a pointed slice site". Eight results
  concern `SheafOfModules.IsFinitePresentation`, quasicoherent presentations and
  generators. They assume a sheaf exists, and give no realization of a given
  stalk module or normalized slice-point comparisons.
- Loogle: `Module.FinitePresentation, CategoryTheory.GrothendieckTopology.Point`.
  Zero hits.
- Mathlib grep: `FinitePresentation.*stalk|stalk.*FinitePresentation`.
  Two hits in `RingTheory/Spectrum/Prime/FreeLocus.lean`, concerning ranks on a
  scheme spectrum, not this arbitrary ringed-site assertion.
- LeanSearch: "A finite presentation over the ring at a point of a site extends
  to a finite matrix of sections on a pointed localization". Eight hits concern
  finite-presentation localization and existing sheaf presentation predicates;
  none states this realization theorem.
- `rg` over the upstream `WeilConjectures` and project `lean/Sheaf` with the item
  id and the same finite-presentation/stalk regex: no upstream match; project
  hits concern already-given sheaves at scheme stalks. Reading
  `SitePointFibre` confirmed its constant-coefficient module interface is not
  applicable to this variable-ring assertion. Mathlib's varying-ring module
  colimit was found and reused instead of copying its construction.
- Full declaration-name checks in upstream, project and
  `dag/lean_names_upstream.json` found no collision with the namespace or main
  declaration. Generic `ringDiagram` hits lie in other namespaces and describe
  unrelated diagrams.

No statement correction, new node, dependency replacement, or
STATEMENT-DISPUTED flag is needed. The helpers implement the canonical stalk,
restriction and comparison notions of this single assertion and are all listed
in `lean.declarations`, with source and blueprint docstrings.

## Second reading by N3

Self-check against the node and the written module: matched every hypothesis and
clause in the list above. Initially finite free indices were unlifted; the compiler
exposed their universe mismatch and they were changed to `ULift.{u} (Fin _)`,
retaining every finite rank. The slice point is specified by its actual colimit
functor, the ring identification by its restricted universal cocone, and the
natural comparisons by their germs, so none is an arbitrary existential lift.
The matrix condition is sectionwise for every slice object, not just on global
sections. The independent mathematical reading remains the maintainer's review;
no second agent was started, in accordance with the dispatcher brief.

Validation: `scompile.py N3 lem-sfb-site-fp-stalk-realization` completed with
exit code 0 for the sandbox probe (14.0 seconds) and final module name (11.9
seconds), with no errors or warnings. The matrix-section scalar multiplication
uses an explicit `@id` to retain its module type after forgetting to sets.
