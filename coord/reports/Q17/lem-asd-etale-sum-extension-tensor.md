## Worker report

`Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor` states the isomorphism and fold-counit
identity of `lem-asd-etale-sum-extension-tensor`. Both complexes range over the entire
ordinary étale derived categories. The only postponed proof is the named theorem
`AlgebraicGeometry.Etale.isIso_etaleSumExtensionTensorComparison`; its docstring contains
all seven proof steps from the node, including their named dependencies.

The saved packet was incomplete: its module stopped after the comparison definition,
although its JSON and report described a theorem. The required initial dry run timed out
on that definition locally and on server confirmation. The repaired definition constructs
its map directly by the sum-extension adjunction. The helper
`etaleSumExtensionTensorPullbackIso` transports the existing canonical K-flat derived
pullback comparison through `leftDerivedUpperStarIsoMapDerivedCategory` in both arguments
and the value. Thus its source and target use the exact, termwise inverse image consistently.
These helpers belong to this node and are listed in `lean.declarations`; they introduce
neither a second tensor product nor an arbitrary comparison. Their data contain no `sorry`.

The correspondence with every hypothesis and conclusion is:

- Finite commutative coefficients: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
- Schemes and their map: `{V T : Scheme.{u}} (v : V ⟶ T)`.
- Separated étale: `[Etale v] [IsSeparated v]`.
- Finite type: `[LocallyOfFiniteType v] [QuasiCompact v]`, the conjunction used by its
  recorded definition node.
- Noetherian source and target: `[IsNoetherian V] [IsNoetherian T]`; Mathlib's scheme
  predicate includes local Noetherianity and quasi-compactness, equivalent to a finite
  affine cover by Noetherian rings.
- Arbitrary unbounded inputs: `(B : DerivedCategoryModule A T)` and
  `(M : DerivedCategoryModule A V)`, followed by `∀ C : DerivedCategoryModule A T`.
- The canonical map is `etaleSumExtensionTensorComparison A v B M`. It is the inverse
  transpose under the termwise derived sheaf adjunction of `1 ⊗ unit`, followed
  by the canonical tensor comparison. On the defining lift-indexed sum its inverse is
  `b ⊗ (s,m) ↦ (s,s^*b ⊗ m)`, which fixes its normalization.
- Its invertibility is the conjunct `IsIso (etaleSumExtensionTensorComparison A v B M)`.
- The fold counit is `(etaleLowerShriekUpperStarAdjunction (ModuleCat A) v _).mapDerivedCategoryAdjunction.counit.app C`.
  This is the dependency's degreewise sheaf adjunction, with fold counit, descended to
  derived categories.
- The left composite is the comparison at `v^*C`, followed by the second-variable
  `derivedTensor` functor applied to this counit; this is precisely `1_B ⊗ ε_C`.
- The right composite applies termwise derived sum extension to
  `(etaleSumExtensionTensorPullbackIso A v B C).hom`, then composes with the counit
  at `B ⊗ᴸ C`. This is exactly `ε_(B ⊗ᴸ C) ∘ v_!(θ_(B,C))`, with θ in the direction
  specified by the node. Lean composition `≫` follows traversal order.

Statement dependencies used (module and declarations):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek` and `etaleLowerShriekUpperStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  the sum-extension adjunction, used through its underlying sheaf adjunction and
  `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction` from
  `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its canonical constant-coefficient comparison is realized here by the existing
  `leftDerivedUpperStarTensorIso` and `leftDerivedUpperStarIsoMapDerivedCategory` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal` and `.UpperLowerStar`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact` identifies exact constant-coefficient
  inverse image with module pullback.
- Mathlib's recorded scheme, étale, separated, finite-type and quasi-compact declarations
  from `.Scheme`, `.Morphisms.Etale`, `.Morphisms.Proper`, `.Morphisms.FiniteType` are used
  directly; `.Noetherian` supplies the scheme predicate. The recorded ring predicate
  `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs` underlies this local condition.

All stated proof dependency modules are imported as required. The remaining five proof
nodes without Lean records are not needed to type the statement: cochain tensor coherence,
sum tensor totalization, K-flat total tensor, exact-functor derived factorization and
localization universal property. No prerequisite statement is replaced by a private copy.

Edge cases checked: identity and open-immersion maps, empty source, zero ring, zero
complexes and an empty set of lifts. The empty sum is zero. The counit equation has the
same source and target in every case. In odd bidegrees the two symmetry signs in the
node's construction cancel. Arbitrarily many nonzero degrees are allowed: no boundedness,
constructibility or Tor-amplitude hypothesis appears.

Searches retained from the earlier attempt: `msearch.py` LeanFinder for “extension by zero
along an etale morphism commutes with tensoring” returned Kähler differential and generic
sheaf hits; Loogle for projection formula and counit names returned generic monoidal
adjunctions; grep of Mathlib and WeilConjectures for `sumExtensionTensor`,
`extension.*zero.*tensor` and `projection.*formula` found no exact derived statement with
the counit identity; `rg` of `lean/Sheaf` likewise found no exact node declaration.
The existing underived `AlgebraicGeometry.Etale.etaleLowerShriekTensorIso` was inspected:
it concerns sheaves, so does not replace this unbounded theorem. During repair,
`msearch.py ... grep 'etaleSumExtensionTensor|etaleLowerShriek.*Tensor|derivedEtale.*projection'`
returned zero hits. The current `EtaleMap` and `EtaleMapProjection` sources were read via
`scompile.py --source`; the derived tensor comparison and exact/left-derived transport
were read in the upstream source tree. No node statement or dependency list was changed.

The compiler exposed a name collision in the inherited derived-adjunction interfaces: the
upstream generic declaration expects a coefficient category, while the side declaration
expects a ring. The final statement spells out `etaleLowerShriekUpperStarAdjunction` and
`.mapDerivedCategoryAdjunction` directly, precisely the construction in the recorded
ambient-adjunction dependency, without depending on the colliding short name.

Validation: the repaired packet passed `deliver2.py --no-push`: preflight and both per-file
compilation checks were clean. Final self-check verified the signature verbatim, all
non-`lean` node fields unchanged, explicit universe/variable binding, 100-column width and
one postponed theorem proof. No statement dispute or node correction was required.

## Second reading by Q17

Independent maintainer second reading, 2026-10-18, of the immutable delivery
7d518521ca3d96705f59c0b23fb87c41f5563ff4. This reading was performed by a reviewer who
did not write this delivery; the heading identifies the delivery group, not the reviewer's
affiliation. The item node, all twelve statement-dependency nodes and their recorded
interfaces, the module, its helpers and proof docstring, and the cited source were open.

Hypothesis and conclusion correspondence:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  No field, nonzero-ring, characteristic or invertible-prime assumption is present.
- Schemes and the morphism are `{V T : Scheme.{u}} (v : V ⟶ T)`.
  `[Etale v]` and `[IsSeparated v]` give precisely the two named morphism properties.
  `[LocallyOfFiniteType v] [QuasiCompact v]` give finite type, in the recorded Mathlib
  encoding. `[IsNoetherian V] [IsNoetherian T]` give finite affine covers by spectra of
  Noetherian rings; Mathlib Noetherian.lean:280-286 explicitly states this equivalence.
- `B : DerivedCategoryModule A T`, `M : DerivedCategoryModule A V`, and the quantified
  `C : DerivedCategoryModule A T` range over entire ordinary etale unbounded derived
  categories. There are no boundedness, constructibility or Tor-amplitude restrictions.
  The coefficient/site universes are the ones of the recorded DerivedCategoryModule
  interface, not a new restriction on the site or an independent small test universe.
- `etaleSumExtensionTensorPullbackIso` transports the existing canonical bifunctorial
  `leftDerivedUpperStarTensorIso` through `leftDerivedUpperStarIsoMapDerivedCategory`.
  Its hom goes from `v^*B tensor v^*C` to `v^*(B tensor C)` as required. Both input
  transports are inverse transports, followed by the inverse tensor comparison and the
  forward transport of the value. No tensor order is changed in this helper.
- `etaleSumExtensionTensorComparison` constructs `P_(B,M)` by the inverse adjunction
  Hom equivalence applied to `1 tensor unit`, followed by that tensor-pullback hom.
  For restriction along an etale map, the unit inserts the distinguished lift summand;
  its transpose sends `(s,s^*b tensor m)` to `b tensor (s,m)`. Thus this is the inverse
  of the pure-tensor map of the node, not an arbitrary map with the right endpoints.
  The construction is natural in both inputs because the tensor comparison, unit and
  adjunction Hom equivalence are natural. Its `IsIso` is exactly the first conjunct.
- The counit is the explicit sheaf sum/restriction adjunction's
  `.mapDerivedCategoryAdjunction.counit`, the same construction used in the ambient
  adjunction dependency. The upstream unit factorization identifies it with degreewise
  descent; at sheaf level the Hom equivalence makes the counit the fold of lift summands.
- The second conjunct is the equation for every C. In traversal order (`≫`), the left
  side is `P_(B,v^*C)` followed by the second-variable tensor functor's map of epsilon_C.
  The right side is termwise derived sum extension's map of theta_(B,C), followed by
  the counit at `B tensor C`. Both start at `v_!(v^*B tensor v^*C)` and end at `B tensor C`.
  All clauses and quantifiers agree with the node.

Source checks: blueprint thm-asd-smooth-tensor.md, proof paragraph beginning “By its
 definition as the transpose”, gives the etale-counit normalization. Stacks
more-etale.tex:1808-1885 (Tag 0GKF) constructs the pure-tensor projection map and proves
its stalkwise isomorphism; etale-cohomology.tex:11361-11442 (Tags 03S3/03S5) gives the
sum-extension presheaf, restriction, adjunction and exactness. sites-cohomology.tex:3508
and :3684 (Tags 0G7E/07A4) gives K-flat preservation and the canonical unbounded tensor
comparison. All seven node proof steps appear in the theorem docstring; the signed
symmetries in step 3 cancel, while step 6 permutes no factors.

Dependency and search checks: the recorded ordinary inverse image, sum extension,
unbounded tensor, coefficient derived category, ambient adjunction and canonical ringed
tensor-pullback interfaces were read in their source modules. The two missing local
WeilConjectures.AlgebraicGeometry modules were read with `scompile.py --source` from
current compiler sources. Mathlib's Scheme, Etale, IsSeparated, LocallyOfFiniteType,
QuasiCompact, IsNoetherian and IsNoetherianRing definitions were inspected directly.
Independent rg searches for etale sum/derived projection vocabulary in WeilConjectures
and lean/Sheaf and monoidal adjunction vocabulary in Mathlib found no exact replacement
for the whole theorem. The existing etaleLowerShriekTensorIso is underived; the generic
map_μ_comp_counit_app_tensor has different monoidal-adjunction data. The related
etaleSupportExactUpperTensorIso transports the same existing comparison as a bifunctor;
it does not state this item's isomorphism plus counit identity. The helpers here are
component/adjunction constructions using existing notions, not private definitions of
inverse image, derived tensor, or sum extension. The worker's LeanFinder, Loogle and
text-search records are retained above. No new DAG prerequisite is needed to type these
constructions. The proof-only prerequisites need not be restated in stage 2.

Edge cases: zero ring, zero inputs, empty source/target where the morphism exists, empty
lift sets, identity maps and open immersions are all admitted. Empty lift sums give zero;
no nonempty hypothesis or bounded degree range appears. Direct-sum totalization handles
unbounded degrees, and the signed-symmetry calculation also covers odd and negative
bidegrees. The finite-ring hypothesis adds no nontriviality condition.

Validation on 2026-10-18: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q17
lem-asd-etale-sum-extension-tensor
snapshot/lean/Sheaf/AlgebraicGeometry/EtaleSumExtensionTensor.lean` returned exit code 0.
The wrapper reported sandbox compilation in 7.7 s and library compilation in 8.3 s,
with no error, timeout or disallowed warning. The installed wrapper currently dispatches
these isolated overlay compilations on the server. The immutable module SHA-256 is
5c3ff7cd33ed2ef46c05993ccd8955149fc7b1eaf0db37c05de3f72512ec1629.
The recorded lean.statement equals the theorem signature verbatim. All three declarations
are recorded, autoImplicit is false, all variables/universes are bound, no line exceeds
100 characters, both definitions contain real terms, and the only local theorem proof
is `by sorry`. Module and all declaration docstrings name source and blueprint.

Finding and correction: H11, the original second-reading section contained only a
notice that no reading occurred. This complete independent reading replaces that notice.
There is no mathematical, declaration, universe or JSON correction. The Worker report is
preserved. No clone or branch head was edited; no global build, direct ssh, delivery,
claim or merge was run. The only compilation/source access used the prescribed wrapper.
