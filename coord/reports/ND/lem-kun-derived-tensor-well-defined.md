## Worker report

This is an existing-declarations delivery: no new module is written. The main declaration is
`CategoryTheory.MorphismProperty.whiskerLeft_of_kFlat` in
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`. Its full signature and surrounding
variables were read. The same module supplies `whiskerRight_of_kFlat` and
`CategoryTheory.DerivedMonoidal.isIso_counit_app_app_of_kFlat_left` / `_right`, recorded in
`lean.declarations`, for the opposite tensor order and the canonical-independence clause.
These are existing general results specialized to the precise sheaf category of the node.

Source checked: the blueprint unit's file
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-derived-tensor-well-defined.md`, and
`literature/stacks-project/sites-cohomology.tex`, labels
`lemma-derived-tor-quasi-isomorphism-other-side` and `definition-derived-tor` (06YT/06YU),
including the independence paragraph immediately preceding the definition. The upstream
preservation proof is exactly Stacks' K-flat-resolution square and cancellation proof.
The node's alternative cone proof is not re-proved or replaced in the DAG.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The commutative ring is `Λ : Type (u + 1)` with `[CommRing Λ]`, and the scheme is
  `T : Scheme.{u}`. Set `A = Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  These are the exact coefficients and size convention recorded by both statement dependencies;
  the generic theorem does not restrict the ring, characteristic, scheme, or complex degrees.
* For the first clause specialize the theorem's `C` to `CochainComplex A ℤ` and its `W` to
  `HomologicalComplex.quasiIso A (.up ℤ)`. Its `g : Y₁ ⟶ Y₂` is the given map `P ⟶ Q`,
  and `hg : W g` is precisely `QuasiIso g`, meaning an isomorphism on every cohomology sheaf.
* `hY₁ : W.kFlat Y₁` and `hY₂ : W.kFlat Y₂` are exactly the two K-flat hypotheses.
  Upstream `HomotopyCategory.kFlat_quotient_obj_iff` transfers this condition between
  complexes and their homotopy classes. `HomotopyCategory.kFlat_iff_preserves_acyclic`
  identifies it with acyclicity of tensors with every acyclic complex. Signed symmetry
  identifies the two tensor orders. Thus this is the acyclic-test K-flatness specified by
  `def-kun-derived-tensor`, without any assumption that the terms are flat or bounded.
* The theorem's arbitrary `X : C` is the arbitrary complex `F`. Its conclusion `W (X ◁ g)`
  says exactly that `id_F tensor g` is a quasi-isomorphism. The monoidal tensor on complexes
  is `HomologicalComplex.tensorObj`, i.e. `mapBifunctor` for `curriedTensor A`.
  It is the direct-sum total tensor on `.up ℤ`, with differential sign `(-1)^p`.
* The generic hypotheses `W.HasTwoOutOfThreeProperty` and
  `W.localizerMorphismKFlat.HasLeftResolutions` require no extra hypothesis on `Λ`, `T`,
  or the complexes: they are available instances for this `A`. The latter comes from
  the unbounded functorial flat resolution of the sheaf category, through
  `CategoryTheory.Abelian`'s cochain K-flat left-derivability instance. The specialization
  probe checks their availability; they are not assumptions added to the node.
* For canonical independence, instead take `C = HomotopyCategory A (.up ℤ)`,
  `W = HomotopyCategory.quasiIso A (.up ℤ)`, and `L = DerivedCategory.Qh`.
  The recorded `_left` counit theorem makes the specified natural comparison
  `δ(P,F) : L(P) tensor-derived L(F) ⟶ L(P tensor F)` invertible for every K-flat `P`
  and arbitrary `F`. This is the counit of the existing derived bifunctor, not an
  arbitrary isomorphism or a choice from a mere existence theorem.
  Given two models with the specified identification `u : L(P) ≅ L(P')`, their canonical
  comparison is `δ(P,F)⁻¹ ≫ (u tensor id) ≫ δ(P',F)`.
  For resolutions `q : P ⟶ C₁`, `q' : P' ⟶ C₁`, use
  `u = asIso(L(q)) ≪≫ (asIso(L(q'))).symm` (with the quotient understood).
  Naturality of the existing counit makes this the localized tensor map for an actual
  model morphism, and functoriality makes it depend only on `u`, with identity and cocycle
  laws by cancellation. This gives the node's canonical independence, including models
  linked by roofs rather than by a direct chain map. The `_right` theorem gives the
  equivalent order with the K-flat model in the second factor.

Statement dependencies used:

* `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`. Its full definition and docstring were read:
  it is `curriedTensor` on the K-flat-derived monoidal category, not degreewise Tor.
* `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  especially the recorded `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The delivered dependency's
  full module was read: `D(T_et,Λ)` is `DerivedCategory A`, with the same `A` above.

Additional inspected interfaces: upstream `FromJoel.CategoryTheory.Abelian.Flat.KFlat`
(acyclic-test equivalence, quotient equivalence, unbounded resolution instances),
`CategoryTheory.DerivedCategory.Monoidal.Shift` (the natural comparison and its invertibility),
and `CategoryTheory.DerivedCategory.FlatModel` (module) and its declaration
`DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` (the explicit cochain version of the comparison). No dependency record needs repair.
The already-stated proof dependencies were inspected through their DAG records; their
SheafOfModules cone tools are not imported into a new module, because this delivery reuses
existing upstream results rather than writing another theorem with postponed proof.

Edge cases checked: zero complexes, identity maps, arbitrary unbounded complexes, zero ring,
empty scheme, all characteristics, and models with no direct comparison chain map.
No nonzero, inhabited-site, boundedness, termwise-flatness, or direct-map assumption occurs.
Identity and three-model cocycle comparisons follow from the specified formula, including
when two models are the same. No statement fault or STATEMENT-DISPUTED issue was found.

Searches (2026-10-15):

* `msearch.py ... leanfinder`, query "Tensoring a quasi-isomorphism between K-flat complexes
  with an arbitrary complex preserves quasi-isomorphisms": eight ordinary module-flatness
  hits (`Module.Flat.iff_lTensor_preserves_shortComplex_exact` and related lemmas), no match.
* `msearch.py ... loogle`, query `IsKFlat, tensorLeftCounit`: no hits, unknown identifier
  `IsKFlat` in the Mathlib search index.
* `msearch.py ... grep`, query `IsKFlat|tensorLeftCounit|quasiIso.*tensor`, subdirectory
  `Algebra/Homology`: no Mathlib hits.
* Direct `rg` of upstream `WeilConjectures/CategoryTheory` and `FromJoel` for
  `tensorLeftCounit`, `IsKFlat`, `quasiIso.*tensor`, then full source reads, found the
  exact generic preservation lemmas and canonical counit theorems recorded here.
  Direct `rg` of upstream for the item's blueprint ID and of `dag/lean_names_upstream.json`
  for that ID returned no explicit blueprint attachment; the mathematical declarations
  were found by their actual names and signatures.
* Direct `rg` of `lean/Sheaf` found `CochainComplex.kFlat_tensor_quasiIso` in
  `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`; the full file was read. It is restricted
  to the one-point site and is not substituted for the small-etale assertion.
  Other hits concerned change of rings, finite Tor amplitude, or first localization.

Validation: a scratch-only specialization probe is compiled with the prescribed `scompile.py`;
`deliver2.py --no-push` also compiles real `#check @...` probes for every recorded declaration
and runs server preflight. No scratch file is included as a delivered module.

The specialization probe checks both recorded clauses on the actual small-etale module-sheaf
category. To avoid expensive open-ended instance search, it explicitly installs the existing
small-etale Grothendieck instance, its colimits, their canonical size-zero shrinking, and
`LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions`. These are applications
of existing constructions, not new mathematical assumptions. With these supplied explicitly,
both preservation and canonical-counit specializations typecheck in about 3.4 seconds under
the standard 60-second limit, with no increased heartbeat option. The initial exploratory
probes timed out in instance search; the explicit construction resolves that issue.


## Second reading by ND

I independently read the item JSON and the blueprint source paragraph, Stacks
`sites-cohomology.tex` at `lemma-derived-tor-quasi-isomorphism-other-side` and
`definition-derived-tor`, and the intervening independence paragraph. The source works on
an arbitrary ringed site: it assumes neither boundedness nor termwise flatness of P and Q.
Specializing to the constant coefficient ring on the small etale site gives exactly this
node. The sandbox statement and proof are unchanged from the repository node; there is no
statement_change, new node, dependency module, or correction to audit.

Here is my object/hypothesis/conclusion inventory and its correspondence, in source order.
All verdicts are pass.

1. A commutative ring Λ: `Λ : Type (u + 1)` and `[CommRing Λ]` in the specialization,
   with no domain, field, characteristic, or nontriviality condition. This is the coefficient
   convention of the recorded dependencies, not an extra ring hypothesis.
2. A scheme T and Λ_T-module sheaves on T_et: `T : Scheme.{u}` and
   `A = Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. I opened both dependency
   records, `Etale.derivedTensor` in `SixFunctors.Etale.Derived.Tensor`,
   `Etale.DerivedCategoryModule` in `SixFunctors.Etale.Derived.Coefficients`, and the entire
   landed `Sheaf.AlgebraicGeometry.DerivedCategories`. All use this same A; there is no
   substitution of Zariski sheaves, modules on a point, or an unrelated ringed site.
3. Complexes P and Q: specialize the existing theorem's C to `CochainComplex A ℤ`.
   The objects `Y₁, Y₂` are P, Q. The entire integer-graded complex is quantified;
   no concentration or flatness of terms is required.
4. A quasi-isomorphism P → Q: `g : Y₁ ⟶ Y₂` and `hg : W g`, with
   `W = HomologicalComplex.quasiIso A (.up ℤ)`. This is exactly `QuasiIso g`,
   hence isomorphisms on every cohomology sheaf, rather than a degreewise isomorphism.
5. K-flatness of both endpoints: `hY₁ : W.kFlat Y₁` and `hY₂ : W.kFlat Y₂`.
   I read the definition of `MorphismProperty.kFlat` and both equivalences
   `HomotopyCategory.kFlat_quotient_obj_iff` and `kFlat_iff_preserves_acyclic` in
   `FromJoel.CategoryTheory.Abelian.Flat.KFlat`. They identify this with the node's
   acyclic-test notion. The two tensor orders in the generic definition are equivalent
   by the signed symmetry in the dependency's construction.
6. Every complex F: the unrestricted `X : C` in `whiskerLeft_of_kFlat`, instantiated
   as F. F is quantified after the endpoint hypotheses and need not itself be K-flat.
7. The prescribed tensor map is a quasi-isomorphism: the conclusion `W (X ◁ g)`
   is the map `id_F tensor g`. I read `HomologicalComplex.tensorObj` and `tensorHom`
   in Mathlib `Algebra.Homology.Monoidal`: these use `mapBifunctor` and its induced map,
   namely the direct-sum total complex with the cochain sign convention. It is not
   the product total complex, tensor of cohomology, or degreewise Tor. The recorded
   `whiskerRight_of_kFlat` also supplies the order used in the model formula.
8. Canonical independence of the K-flat model of K₁ in D(T_et,Λ): the recorded
   `DerivedMonoidal.isIso_counit_app_app_of_kFlat_left` asserts invertibility of the
   specified natural counit at (P,F) for K-flat P and arbitrary F. I opened
   `FromJoel.CategoryTheory.Monoidal.Derived`: its `bifunctor` is the left-derived
   bifunctor, and `counit` is the left-derived counit, with its two naturality equations
   used in the lax monoidal structure. I also opened
   `FromJoel.Algebra.Homology.DerivedCategory.Monoidal` and the shortcut instances:
   the derived monoidal structure and its comparison are precisely the ones defining
   `Etale.derivedTensor`, not a different monoidal structure on the same objects.
   The concrete cochain version `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`
   in module `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` explicitly
   composes this counit with `quotientCompQhIso` and the quotient's monoidal comparison.
   Write it as e(P,F). For a specified derived identification u : Q(P) ≅ Q(P'),
   the canonical comparison is
   `e(P,F).symm ≪≫ whiskerRightIso u (Q.obj F) ≪≫ e(P',F)`.
   For two resolutions of C₁ take u to be `asIso (Q.map q)` followed by the inverse
   of `asIso (Q.map q')`. This requires no direct map between the resolutions.
   Naturality identifies the formula with tensoring a model morphism; cancellation
   of e(P',F) and functoriality give the identity and three-model cocycle equations.
   Thus the existing declarations cover the canonical clause, not merely bare
   existence of some isomorphism. The right counit covers the equivalent order.

The apparent extra generic hypotheses are not extra hypotheses on the source objects.
`W.HasTwoOutOfThreeProperty` is the quasi-isomorphism instance.
`W.localizerMorphismKFlat.HasLeftResolutions` and its homotopy-category left-derivability
structure follow from the unbounded functorial flat resolution instance. I read its
construction in `FromJoel.CategoryTheory.Abelian.Flat.KFlat` and the sheaf and module
instances in `CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.
The explicit Grothendieck and colimit instances in the scratch probe are existing
constructions applied to A, with no new assumed instance or mathematical hypothesis.

Edge cases: the empty scheme, zero ring, zero complexes and identity maps are included;
none of the declarations assumes inhabitedness or nontriviality. Arbitrarily unbounded
complexes and all characteristics are included. Degree zero is an ordinary integer degree;
there is no positive-degree exclusion. No independent index set occurs; empty summands
are handled by the total tensor's coproducts. The scheme's u and the coefficients' u+1
are exactly the dependency encoding and are not equated. The generic preservation and
counit declarations are universe-polymorphic; the probe binds u explicitly and checks
both claims in the actual sheaf category. Different models related by a roof are covered
because u is an arbitrary isomorphism in the derived category.

Independent searches, with different wording from the worker, on 2026-10-15:

- `msearch.py ... leanfinder`: "A quasi-isomorphism of homologically flat complexes
  stays a quasi-isomorphism under total tensor with an unbounded complex" returned
  eight flat-module, complex-factorization and total-tensor-interface hits; no exact
  Mathlib statement.
- `msearch.py ... loogle`: `"counit", "IsIso"` returned twelve adjunction counit
  declarations, none about derived tensor or K-flat complexes.
- `msearch.py ... grep`: `kFlat|tensorLeftCounit|whiskerLeft_of_kFlat` returned no
  Mathlib matches. Direct rg for `homologically flat`, tensor/resolution combinations,
  `counit.*kFlat`, `kFlat.*counit` and `whisker.*kFlat` in Mathlib, upstream and
  `lean/Sheaf` located the existing generic preservation and counit declarations.
  Project module and change-of-rings hits have different sites or coefficient objects.
  Full source inspection confirms reuse of the upstream declarations is appropriate.

No mathematical or signature mismatch was found. I repaired one documentation mismatch:
the worker report had presented a declaration as though it were a submodule; it now gives
module `CategoryTheory.DerivedCategory.FlatModel` and declaration
`DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` separately. I extended the scratch-only
specialization check with the actual canonical comparison formula between two arbitrary
K-flat cochain models and a derived identification. Its inferred conclusion is exactly
`Q.obj (P tensor F) ≅ Q.obj (P' tensor F)`. No module or definition was added to the delivery,
and the node's existing-declaration record and verbatim upstream signature remain correct.
The existing declarations need no replacement proof/docstring module; no hollow data,
postponed helper theorem, hidden file-local convention, or unbound universe was introduced.

Validation: prescribed `scompile.py` accepted the extended specialization probe locally
and on the server in 3.8 seconds each, without errors or warnings and with the standard
limits. The delivery wrapper separately checks every recorded existing declaration.
