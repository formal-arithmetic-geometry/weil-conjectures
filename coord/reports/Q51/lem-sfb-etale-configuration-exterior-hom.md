## Worker report

Module: `Sheaf.AlgebraicGeometry.EtaleConfigurationExteriorHom`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.etale_configuration_exterior_hom`.
The only postponed proof is this named theorem. All helper definitions have real data.
The module preserves the node statement and every accepted stage-1 field; only `lean` changes.
The inherited BLOCKED ending concerned an unchanged stage-1 delivery. The present node has no
Lean record, is listed in the stage-2 queue, and is formalized here as required by the current
stage handoff paragraph of coord/brief-stage2.md. No reopening or stage-1 split is attempted.

Hypotheses and conclusions, clause by clause:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space is `X : AlgebraicSpace S`.
  The given covering scheme with its representable etale map is `U : X.EtaleSite`:
  `U.obj.left : Over S` supplies the scheme and `U.obj.hom` the map to X;
  `U.property` is precisely `IsEtale U.obj.hom`. Surjectivity is the explicit
  `hsurj : IsSurjective U.obj.hom`; separatedness is
  `hsep : IsSeparatedPresheafMap U.obj.hom`, namely closed-immersion scheme tests of
  its diagonal. These are the dependency interfaces, not newly defined properties.
- The size convention is `universe u`, schemes of size u, small-site morphisms of size u,
  and coefficient groups in `AddCommGrpCat.{u + 1}`. This coefficient universe contains
  the site objects. There is no equality imposed between site object and Hom universes,
  and no additional smallness or sheafification assumption. ULift only enlarges the
  represented Hom sets and the constant integers to this common coefficient size.
- `configurationFreeSheaf X U` is exactly the sheafification of
  `uliftYoneda.obj U ⋙ AddCommGrpCat.free`: at V its basis is Hom_X(V,U), and restriction
  composes such a map with the restricting arrow. Mathlib's free abelian group is the
  usual finitely supported integral linear combinations.
- `configurationAugmentation X U` applies sheafification to the natural map whose component
  is `FreeAbelianGroup.lift (fun _ ↦ 1)`. Its target is the sheafification of the constant
  presheaf of integers. Thus it is the epsilon of the statement, sending each generator to 1.
- `configurationExteriorSheaf X U n` sheafifies the sectionwise exterior power of E over Z,
  using `exteriorPower` and its functorial maps. This is the canonical exterior power in
  abelian sheaves, equivalently over the constant integer sheaf. Indeed a locally constant
  integer section acts locally by an ordinary integer; the Z-balanced exterior relations
  therefore impose exactly the constant-sheaf module relations after sheafification.
  No structure sheaf of regular functions is substituted for the constant integers.
- `p : ℕ` is precisely p >= 0. `T`, `pr`, and `Nonempty (IsLimit (Fan.mk T pr))`
  express the (p+1)-fold product U over X. The product is in X.EtaleSite, so it represents
  the fibre product on all etale scheme tests, and its underlying scheme represents the
  sheaf fibre product. Testing on arbitrary schemes is equivalent after an etale cover
  trivializing the tuple's lifts. No finite fibre or affine hypothesis is added.
- `configurationDistinctSet` removes the images of the SCHEME equalizers of the coordinate
  maps, for all unequal index pairs. The equality subscheme is the base change of the
  relative diagonal; equalizers in Scheme encode scheme-theoretic equality, including
  residue-field maps, not merely equality of underlying topological images.
- `W : X.EtaleSite` and `j : W ⟶ T` give the claimed etale scheme, and the separate
  `IsOpenImmersion` and `IsClosedImmersion` conjuncts together with the range equality
  identify it as exactly that open and closed complement. Either ordering of unequal
  pairs gives the same removed finite union as the node's i<j.
- `ρ : Equiv.Perm (Fin (p+1)) →* Aut W` is the action. Its coordinate formula
  `(ρ σ).hom ≫ j ≫ pr i = j ≫ pr (σ.symm i)` fixes the standard left action convention.
  The next clause states freeness on scheme-valued points with a nonempty test scheme.
  Restricting to nonempty test schemes is necessary: the empty scheme has a unique map
  fixed by every permutation, even for a free action. Equivalently, every nonidentity
  permutation has empty fixed scheme. This includes geometric points and disconnected tests.
- `configurationAntiInvariant X W (p+1) ρ F` is the intersection of additive equalizers
  of `F.obj.map (ρ σ).hom.op` and multiplication by the integer sign of σ. Thus its elements
  are precisely the node's sections s with sigma* s = sign(sigma) s. Since W is an object
  of the small site, `F.obj.obj (op W)` is Gamma(W,F restricted to W), without any auxiliary
  or enlarged-site extension of F.
- The family `e` consists of additive equivalences from Hom(exterior E,F) to this subgroup.
  `configurationWedge` is the sheafification-unit image of the wedge of the actual free
  generators `configurationGenerator`; the evaluation conjunct specifies the image of h
  on precisely the p+1 tautological lifts j >> pr i.
- The last conjunct is naturality for every morphism phi : F -> G, with no restriction on
  coefficient torsion. Applying it to each differential of an arbitrary complex is exactly
  the stated compatibility of cochain maps. No separate complex choice is needed.
- All scalar actions use integers; no inverse factorial or coefficient localization appears.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsEtale, IsSurjective,
  EtaleSite, etaleForget, etaleTopology, using the full-subcategory and scheme-test definitions.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale; the U.property witness uses it via IsEtale.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion, directly in the
  conclusion and through IsSeparatedPresheafMap in the hypotheses.
- Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal: diagonalPresheafMap,
  IsSeparatedPresheafMap (the already defined relative separatedness interface).
- Sheaf.CategoryTheory.SiteCoveringAxioms: Precoverage.IsSiteForCoverings, publicly available
  through AlgebraicSpace; the actual site topology is X.etaleTopology, and sheaves are Sheaf.
- Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf, toSheafify,
  sheafificationAdjunction; LeftExact supplies sheafification in the chosen coefficient size.
- Mathlib.LinearAlgebra.ExteriorAlgebra.Basic and ExteriorPower.Basic: ExteriorAlgebra,
  exteriorPower, exteriorPower.map, exteriorPower.ιMulti; ModuleCat.ExteriorPower imports
  these. integralExteriorPower only bundles these existing constructions in AddCommGrpCat.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: the recorded tensor module
  is publicly imported for the same sheafified tensor convention; the alternating quotient
  is expressed using the dependency's ordinary module exterior powers and sheafification.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etale_fibreProduct_isScheme, and etaleCover_pullback.
  The finite-product cone uses Mathlib Fan and IsLimit; no alternate fibre-product notion.

Proof dependency imports: SpaceSeparatedEtaleDiagonalComplement and ChartwiseEtalePermanence
are plain imports. The open/closed immersion base-change and open-restriction dependencies
are Mathlib leaves and arrive through the geometry imports. The general alternating
sheafification universal property is not yet stated in Lean; it is a proof dependency only,
so it does not prevent stating the present theorem and has no module to import.

Edge cases read against Stacks 0726 and checked in the formulation:

- p=0: one factor, no unequal index pair, the distinct set is all of T, S_1 is trivial,
  and wedge evaluation becomes the represented free-sheaf adjunction.
- Empty U/X and empty W: all objects and range predicates remain defined, and the empty
  test scheme is excluded only from the fixed-point implication, as freeness requires.
  Empty W gives the zero sign subgroup by the empty-object sheaf axiom.
- Too few lifts in a fibre: the distinct locus there is empty; there is no nonemptiness
  assumption on W or on its fibres.
- Two-torsion coefficients: sign anti-invariance is an equality of integer multiples,
  not the inference s=-s implies s=0. The docstring records paired cancellation for the
  alternating extension, so it is valid without inverting 2 or (p+1)!.
- Nonseparated ambient S and U are allowed: equality loci are closed because the given
  relative map f is separated; no absolute separatedness or affine chart is assumed.
- All scheme test universes are u and coefficients u+1, including in the freeness clause.

Searches made for reuse:

- msearch leanfinder: "Hom from exterior powers of free abelian etale sheaves to abelian
  sheaves equals alternating sections on distinct configurations": eight hits, ordinary
  exteriorPower.desc/mk and alternatingMapLinearEquiv; no sheaf/configuration theorem.
- msearch loogle: `"exteriorPower", "Sheaf"`: zero hits.
- msearch grep: `anti.invariant|alternating.*[Ss]heaf|[Ss]heaf.*exterior`: zero hits.
- msearch leansearch: "Exterior powers of the free abelian sheaf of an etale cover represent
  sign anti-invariant sections on distinct tuples": ordinary exterior-power presentation
  and pairing results, no match for the theorem.
- rg of lean/WeilConjectures and lean/Sheaf for exterior powers, free abelian sheaves,
  configuration and distinct tuples: the scheme-Zariski exteriorSheaf family and the
  scheme small-etale RawModuleScalarComparison.freeAbelian are existing specializations,
  neither an algebraic-space configuration theorem nor the present small-site free sheaf.
  Mathlib's AddCommGrpCat.free, ULift Yoneda, and presheafToSheaf are reused directly.
  Searching the exact node id in WeilConjectures found no declaration.
- rg of the DAG for configuration and exterior/sheaf terms found
  lem-sfb-etale-atlas-distinct-tuple-geometry (affine/quasi-separated geometry only) and
  lem-sfb-alternating-sheafification-universal-property (general multilinear proof input).
  Neither duplicates the theorem or supplies a recorded canonical configuration object.
- Full helper names were checked in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json; no collision found.

Source opened: literature/stacks-project/spaces-cohomology.tex, lemma-compute, lines 850ff,
including its entire stalkwise sign-quotient proof. The theorem docstring carries the accepted
six-step proof plan (the equivalent clopen-zero-extension argument). No statement fault,
statement correction, dependency-module repair, or new independent definition node was needed.
The helper declarations are canonical constructions belonging to this item's own notion,
authorized by the missing-helper paragraph, and all are listed in lean.declarations.

Validation: every compile uses scompile.py. The preliminary module compiled cleanly; the added
augmentation's first check found an obsolete extensionality lemma name, now corrected to
FreeAbelianGroup.lift_ext. Final compile passed in sandbox mode (3.3 s) and module-path mode (3.4 s), with no errors or
non-sorry warnings. deliver2.py --no-push passed server preflight and compilation
(OK, dry-run commit 17851d607f3); only the module, item node and report were staged.

## Second reading by Q51

No independent worker was started: the dispatcher brief forbids starting agents and assigns
independent review to the maintainer. This section does not claim a second independent reading.
