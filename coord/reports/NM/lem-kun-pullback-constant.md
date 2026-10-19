## Worker report

The module `Sheaf.AlgebraicGeometry.PullbackConstantModule` states
`AlgebraicGeometry.Scheme.pullback_constantModule_isIso`, with its proof postponed.
It combines the module-sheaf and complex clauses of the node without introducing
any new definition. The natural comparison is the hom of the already constructed
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`. That construction uses
uniqueness of left adjoints to global sections of the pushforward, with the
terminal base-change identification. Its hom is the canonical map adjoint to
constant sections after base change, rather than a chosen abstract isomorphism.

Hypothesis and clause correspondence:

- “morphism of schemes f:X → Y”: `{X Y : Scheme.{u}} (f : X ⟶ Y)`;
  no etaleness, smoothness, finiteness, or nonemptiness condition on f.
- “Λ-module”: `(Λ : Type (u + 1)) [CommRing Λ]` and
  `∀ M : ModuleCat.{u + 1} Λ`. These are the fixed coefficient conventions
  of def-kun-constant-sheaf and the upstream etale inverse-image API.
  No finite generation, torsion or invertibility requirement is added.
- “canonical morphism f⁻¹ underline M → underline M”: the first conjunct
  uses `(upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app M`.
  Its source is `(Etale.upperStar (ModuleCat Λ) f).obj
  ((constantSheaf Y.smallEtaleTopology (ModuleCat Λ)).obj M)`;
  its target is the constant sheaf on X with value M.
- “is an isomorphism on X_Et”: `IsIso` of that morphism, in the category
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- “or complex of Λ-modules”: the second conjunct quantifies over every
  `CochainComplex (ModuleCat.{u + 1} Λ) ℤ`. Applying
  `NatTrans.mapHomologicalComplex` to the same natural comparison produces
  the degreewise canonical comparison. It maps the termwise constant complex
  followed by inverse image to the constant complex on X. Its differentials
  are mapped by the same functors, so this is an actual chain map.
- “is an isomorphism” for the complex: `IsIso` of the component of this
  transformation at M, in the category of cochain complexes of etale sheaves.
  There is no boundedness or passage merely to a derived category.

The conjunction expresses both alternatives simultaneously. The full signature
is recorded verbatim in the node. Universes and variables are explicit.

Statement dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (transitively imported). The full structures
  specify locally affine locally ringed spaces and their morphisms.
- def-kun-constant-sheaf: `CategoryTheory.Functor.mapHomologicalComplex`,
  `Mathlib.Algebra.Homology.Additive`, directly publicly imported. Its full
  definition applies a zero-preserving functor to each object, differential,
  and chain-map component. Constants use `CategoryTheory.constantSheaf`,
  sheafification of the constant presheaf.
- def-weil-pbc-inverse-image: `AlgebraicGeometry.Etale.upperStar` and
  `Etale.upperStarLowerStarAdjunction`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (publicly imported
  through `WeilConjectures.ConstructibleSheaf.Defs`). They use left Kan
  extension and sheafification, for arbitrary scheme morphisms.
- The canonical comparison is the existing
  `AlgebraicGeometry.Scheme.upperStarConstantSheafIso` from
  `WeilConjectures.ConstructibleSheaf.Defs`. Its full definition and docstring
  were read. No copy of the comparison is made.

All recorded proof-dependency modules are also imported. Direct image and
inverse image are in UpperLowerStar.Defs. Sheafification is
`Mathlib.CategoryTheory.Sites.Sheafification`. Stalk pullback is
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`, constant germs are in
`Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`, and conservativity is
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`. The theorem's
source docstring gives all four DAG proof steps, including canonical-germ
compatibility, scalar compatibility, and the inverse chain map.

Edge cases checked: empty X or Y (for every existing f); zero module and zero
ring; identity and arbitrary non-etale f; zero and unbounded complexes;
nonzero differentials (naturality supplies the chain-map condition);
arbitrary characteristic. No point, nonzero coefficient, boundedness or
finite generation assumption occurs. On an empty scheme both sheaves are
zero; for zero coefficients both are zero. The statement agrees with the
blueprint source. There is no statement dispute or correction.

Searches:

- msearch.py leanfinder, “The inverse image of a constant sheaf of modules is
  canonically constant, also termwise for complexes”: eight hits, mostly
  `Sheaf.isConstant_of_forget`, `isConstant_congr`, `isConstant_of_iso`,
  `isConstant_iff_of_equivalence`, and condensed-module constructions;
  none states the two clauses of this node.
- msearch.py loogle, `"constantSheaf", "pullback"`: zero hits.
- msearch.py grep, `sheafPullback.*[Cc]onstant|[Cc]onstant.*sheafPullback`
  in Mathlib CategoryTheory: zero hits.
- rg on upstream and Sheaf for constant/pullback/iso combinations found
  `Scheme.upperStarConstantSheafIso` in ConstructibleSheaf.Defs, which gives
  the sheaf clause; this is reused. Mathlib Additive.lean supplies the generic
  termwise transformation and isomorphism constructors, which are also reused.
  No declaration states the combined module and complex proposition. The
  conjunction is new, not a second constant-sheaf or pullback construction.
- grep for the blueprint id in upstream: no matches. rg for the new full
  declaration's short name in upstream, Sheaf and Mathlib: no matches.

Validation: scompile.py compiled the delivered file cleanly, both its sandbox
probe and its library path, with no errors or warnings. The final prescribed
preflight is run via deliver2.py --no-push. This delivery is for the independent
second reader; no second-reading section has been supplied by the author.

## Second reading by NM

I independently read the sandbox node, its source blueprint lemma and constant-sheaf
 definition, the enclosing Kunneth section, and Stacks etale-cohomology.tex at
 definition-inverse-image (03Q0), equation-pullback and lemma-stalk-pullback (03Q1),
 lemma-stalk-exact (03PT), theorem-exactness-stalks (03PU), and the constant-module
 definition. The Kunneth section's field, finite-type and invertibility assumptions
 belong to its main proposition; this auxiliary lemma and the Stacks inverse-image
 construction are explicitly for arbitrary schemes and arbitrary scheme morphisms.
 The coefficient ring is commutative by def-kun-constant-sheaf, not necessarily a field.

Object, hypothesis and conclusion inventory, with the actual Lean correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`, the Mathlib scheme category recorded by
  def-pc-scheme. Verdict: same objects; no separation, Noetherian, finite-type or
  nonemptiness assumption.
- An arbitrary morphism f from X to Y: `(f : X ⟶ Y)`. Verdict: correct direction
  and no etaleness or other property assumed on f.
- The commutative coefficient ring Lambda: `(Λ : Type (u + 1)) [CommRing Λ]`.
  Verdict: exactly the coefficient convention of the recorded def-kun-constant-sheaf
  specialization, with neither characteristic nor torsion nor invertibility assumptions.
- A Lambda-module M: `∀ M : ModuleCat.{u + 1} Λ` in the first conjunct.
  Verdict: arbitrary module, with no finiteness condition; quantification follows f
  and Lambda as in the node.
- The constant sheaf on Y and its inverse image on X: the source functor of
  `upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f` is
  `constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
  Etale.upperStar (ModuleCat.{u + 1} Λ) f`. Verdict: the same small-etale
  constant sheaf and inverse-image functor as the dependency nodes, not O-module
  tensor pullback or a big-site inverse image.
- The constant sheaf on X: the target functor of that iso is
  `constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  Verdict: correct target, with the same coefficient module.
- The canonical comparison: `(upperStarConstantSheafIso ... f).hom.app M`.
  Verdict: correct map, not just any morphism between isomorphic objects. I read
  its definition in upstream ConstructibleSheaf/Defs.lean: it is
  `Adjunction.leftAdjointUniq` for constantSheafAdj composed with
  upperStarLowerStarAdjunction, transported by lowerStarCompSheafSectionsTerminalIso.
  I also read the terminal-section comparison in UpperLowerStar/Defs.lean and
  Mathlib's homEquiv_leftAdjointUniq_hom_app and unit_leftAdjointUniq_hom_app.
  These identify its adjoint with the constant-section unit after terminal base
  change. Naturality along the unique map to the terminal object gives the same
  constant-section map at every etale object. This is precisely proof step 1's
  sheafification-and-adjunction comparison. ConstantModuleTransitionCoefficients.lean
  independently confirms that normalization on all sheafification generators.
- Isomorphism of module sheaves on X_Et: first conjunct `IsIso (...)`.
  Verdict: an isomorphism in the actual ModuleCat-valued sheaf category, so its
  inverse is linear, rather than an assertion only about underlying sets or stalks.
- Alternatively an arbitrary complex of modules: second conjunct
  `∀ M : CochainComplex (ModuleCat.{u + 1} Λ) ℤ`.
  Verdict: all integer cochain degrees, without boundedness or cohomology conditions.
- Its canonical comparison is an isomorphism: second conjunct `IsIso` of the
  component of `.hom.mapHomologicalComplex (ComplexShape.up ℤ)`.
  Verdict: the actual termwise chain map, with degree-r component the same
  canonical module comparison. I read Functor.mapHomologicalComplex and
  NatTrans.mapHomologicalComplex in Mathlib/Algebra/Homology/Additive.lean:
  they map differentials by the functors and use the natural-transformation
  components as the chain-map components. The conclusion is an actual complex
  isomorphism, not merely a quasi-isomorphism. The two conjuncts render both
  alternatives in the node; no extra naturality or coherence conclusion is added.

Dependency audit: I opened every statement-dependency node and its recorded
 declaration. Mathlib Scheme supplies the scheme category; constantSheaf is
 sheafification of Functor.const and constantSheafAdj is its terminal-section
 adjunction; def-kun-constant-sheaf records mapHomologicalComplex specialized to
 this constantSheaf. Etale.upperStar is the recorded Kan-extension/sheafification
 inverse image, and Etale.lowerStar is evaluation on etale base changes. I also
 read the recorded stalk comparison, constantSheaf_geometricStalk_isIso, and
 isIso_of_isIso_sheafFiber_map signatures and their source comments. All stated
 proof dependencies are imported, directly or via the public upstream import.
 There are no new nodes or dependency modules to audit, and no statement_change
 or citer audit is needed.

Edge cases: empty schemes (whenever a morphism exists), identity and arbitrary
 non-etale morphisms, the zero module and zero ring, all characteristics, zero
 complexes, degree zero and arbitrary nonzero differentials, and unbounded
 complexes are included by the binders. There is no index family to restrict.
 The single universe parameter is polymorphic, and ModuleCat.{u + 1} Lambda is
 the recorded small-site coefficient convention; a smaller coefficient object
 can be regarded in this universe by cumulativity. There is no extra instance
 or equality identifying the object's and morphism's site universes. No variable
 or universe is unbound.

Independent searches (2026-10-15), using different queries from the author:

- msearch.py leanfinder: `inverse image functor commutes with constant coefficients
  and complexes` returned eight generic homological-complex hits, including
  NatIso.mapHomologicalComplex_inv_app_f and Equivalence.mapHomologicalComplex_inverse.
  They do not state this combined etale module-and-complex assertion.
- msearch.py loogle: `"mapHomologicalComplex", "IsIso"` returned zero hits.
- msearch.py grep: `mapHomologicalComplex.*[Cc]onstant|[Cc]onstant.*mapHomologicalComplex|
  pullback_constantModule_isIso` returned zero hits. Direct rg in Mathlib Sites,
  Additive.lean, upstream WeilConjectures and repository lean/Sheaf found the
  existing upperStarConstantSheafIso, the generic termwise natural-iso construction,
  and many uses of the constant-sheaf comparison, but no full assertion combining
  this node's module and complex clauses. These constructions are reused as-is;
  there is no new constant-sheaf, inverse-image or complex construction to duplicate.

Mismatch and repair verdict: none found. I preserved the correct module and node
 signature unchanged and appended only this independent audit. The module has one
 named theorem with proof `sorry`, no new definitions, no hidden data, no private
 declaration, no local notation or local instance. Its module and theorem docstrings
 name the blueprint source, and the theorem docstring carries all four node proof
 steps, including the canonical-germ identification, scalar compatibility and inverse
 chain map. The node's lean.statement is verbatim the file's signature.

Validation: the prescribed scompile.py compiled both the sandbox probe and the
 library-path module successfully (1.7 s and 1.8 s), with no errors or warnings.
