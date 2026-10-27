## Worker report

Item: `lem-sfb-normal-generic-lisse-cocycle`. The delivery states the entire node in
`Sheaf.Paper.NormalGenericLisseCocycle`, with main declaration
`AlgebraicGeometry.ProEtale.normal_generic_lisse_cocycle`. Its two postponed proofs
are that theorem and the elementary well-definedness theorem `automorphism_over`.
Their docstrings contain their complete mathematical arguments. Every definition
has actual data; the theorem asserts existence of a fully characterized fibre
functor and never chooses data from an undetermined existence theorem.

The previous refusal concerned reopening an already reviewed **stage-1** split.
This is a stage-2 statement assignment: the live node has a reviewed split and no
Lean record. No stage-1 proof, source or review field is changed.

### Hypotheses and objects

* `X : Scheme.{u}` uses the recorded Mathlib scheme.
* `[ConnectedSpace X]` includes nonemptiness, so an empty X is excluded exactly as
  in the node. It imposes no extra geometric connectedness condition.
* `[IsNoetherian X]` is Mathlib's class extending `IsLocallyNoetherian X` and
  `CompactSpace X`: locally Noetherian and quasi-compact, precisely the node's
  explicit convention, not merely topological Noetherianity.
* `hnormal` says `IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed ...` for every
  x. This is the dependency's inline normal-domain convention on every local ring.
* The first conclusion is `IsIntegral X`. Subsequent clauses quantify over its
  proof `hX`; this is a proof-indexed way to refer to the resulting function field,
  not a new integrality hypothesis. `IsIntegral X ∧ ∀ hX, Assertions X hX` says
  first that X is integral and then the remaining assertions for that integral X.
* `X.functionField` is the recorded stalk at `genericPoint X`;
  `genericMap X` is exactly `X.fromSpecStalk (genericPoint X)`. No field model or
  arbitrary generic-point map is introduced.
* `A : Type u`, `[NormedField A]`, `[IsUltrametricDist A]` express an arbitrary
  multiplicatively normed field with the nonarchimedean inequality. The metric
  ultrametric condition and the max inequality for its norm are equivalent by
  translating distance to norm of a difference. In particular this includes
  trivially normed and incomplete fields.
* `Ω : Type u`, `[Field Ω]`, `[Algebra X.functionField Ω]`,
  `[IsSepClosure X.functionField Ω]` supply exactly a separable closure and its
  structure embedding. `Ω ≃ₐ[X.functionField] Ω` has Mathlib's Krull topology.
* The existing `normContinuousRing A` is the recorded all-continuous condensed
  ring, with `C(S,A)` and the norm topology, and the existing `coefficientRing`
  and `condensedRingObj` pull it back to the actual small pro-etale site. All
  modules and arrows use the existing `Mod` category and its full lisse
  subcategory `NormContinuousLisse`, not another sheaf/module category.
* The existing size convention puts schemes and fields in a common universe u,
  the small site's objects in u+1 and morphisms in u, and abelian sections in u+1.
  A common universe accommodates any of the schemes and fields under discussion;
  no equality between the site's object and morphism universes is imposed.

### Clauses

1. Integrality is the first conjunct of `normal_generic_lisse_cocycle`.
2. `RestrictionAssertions` says that the actual `CondensedRing.upperStar` along
   `genericMap X` preserves lisse modules, induces a bijection on every Hom set,
   reflects isomorphisms, and preserves multiplication by actual constant scalars
   `normContinuousScalar`. The scalar-multiplied arrow is asserted to exist,
   with its underlying map fixed by that operation; no conditional premise
   conceals its existence. Source arrows are full-subcategory arrows; `.hom`
   passes their actual internal module morphisms to inverse image.
3. `RankAssertions` supplies a finite basis, `Module.finrank ... = n`, and says
   that every nonempty trivializing pro-etale object has precisely that rank.
   There is no positivity assumption on n and no rank constraint on empty charts.
4. The first conjunct of `Assertions` says that every nonempty affine `U : X.ProEt`
   has nonempty actual generic fibre `pullback U.hom (genericMap X)`.
5. `geometricSections` is the generic module evaluated at
   `FieldSeparableCech.closureObject X.functionField Ω`. By the definition of
   restriction to an object's slice site, this is exactly Gamma of the restricted
   module over Spec Ω. The field closure object is the existing canonical
   Spec Ω -> Spec k, not an abstract fibre. `FiberFunctor.sections` identifies
   the representation's vector space with these very additive sections;
   `FiberFunctor.IsNormalized` specifies its A-vector structure using the actual constant action.
   Thus the dimension in clause 3 is the dimension of V_A(L).
6. `automorphism` is the actual `Spec.map g` as an endomorphism of that object;
   `automorphism_over` proves it lies over Spec k. the action equation in `FiberFunctor.IsNormalized` is the
   restriction map on the actual sheaf along this endomorphism. Hence the action
   is the canonical descent action, not an unspecified action on an isomorphic
   vector space. the naturality equation in `FiberFunctor.IsNormalized` specifies every arrow by the actual restricted
   module map on these sections.
7. `CocycleAssertions` uses the existing Cech objects and every canonical coordinate
   system satisfying `FieldSeparableCech.AreCoordinates`. Its section ring
   equivalence theta is normalized by the actual adjoint continuous comparison at
   each test point. In every finite basis it supplies
   `c : (Matrix (Fin n) (Fin n) C(G_k,A))ˣ`. `HasDescentMatrix` equates the second
   vertex restriction of each basis section with the first vertex sections acted
   on by the entries of this actual ring section matrix. In particular c really
   represents the descent isomorphism on the double overlap. It also supplies
   `σ : G_k →* (Matrix (Fin n) (Fin n) A)ˣ`, continuous after inclusion in matrices,
   and identifies entrywise evaluation of c with sigma and the matrices of the
   section-normalized representation. The monoid-homomorphism structure includes
   sigma(gh)=sigma(g)sigma(h) and sigma(1)=1. Continuity after matrix inclusion
   is exactly the stipulated subspace topology on GL; no discrete topology is used.
8. `HomAssertions` says for every rectangular constant A-matrix T that it is the
   matrix of a unique module arrow iff it intertwines every Galois matrix. This
   identifies the whole Hom set, not a subset of continuous or integral arrows.
9. `BasisChangeAssertions` gives both transition-matrix formulas. The first is
   conjugation P inverse times c times P (the new-basis columns form P); the
   second is Q inverse times T times P for an arrow with independently changed
   source and target bases. Applying these identities entrywise to the normalized
   continuous matrices gives the same coordinate changes on c.
10. `FiberFunctor.functor` lands in the existing
    `NormContinuousRepresentations`, whose arrows are all equivariant linear
    maps. the full-faithfulness, additivity, linearity, and section naturality clauses of
    `FiberFunctor.IsNormalized`
    supply the asserted A-linear fully faithful functor with the specified fibre.
11. `UnitSumAssertions` identifies the regular object with the trivial
    representation on the size-lifted copy of A. Its matrices are therefore the
    identity in every basis; the evaluation equations in `CocycleAssertions`
    imply its continuous descent matrix is 1. For a sum it supplies a linear
    equivalence to the product of the two vector spaces, fixed by the actual
    projection arrows, and gives its componentwise action. A finite product is
    the vector-space direct sum. In concatenated bases these are exactly the
    block-sum matrices and hence, by the same entrywise equations, block-sum
    cocycles. The normalization does not permit an unrelated product map.
12. All bases are `Fin n`, with arbitrary n, and all matrices are `Fin m` by
    `Fin n`, with arbitrary m,n. Consequently empty square matrices and both
    empty rectangular dimensions are included throughout, as are zero modules.
13. `Assertions` explicitly states `TotallyDisconnectedSpace A` and clopen balls
    separating distinct points for every positive radius less than their distance.
14. `IsIso (ContinuousRingUniverse.comparison X A)` asserts the canonical
    continuous-function realization. That existing comparison is the adjoint of
    precomposition with the canonical profinite test projection, exactly the
    normalized comparison owned by `def-sfb-continuous-ring-canonical-comparison`.
    Its target has sections `ULift C(|U|,A)`; this is an isomorphism of ring objects,
    since the existing comparison is a ring-object morphism. It uses all continuous
    functions and is not a choice of an uncharacterized isomorphism.

### Dependencies used

The original statement dependencies retain their records and declarations:
`Mathlib.AlgebraicGeometry.Scheme` (`Scheme`, scheme morphisms);
`Mathlib.Topology.Connected.Basic` (`ConnectedSpace`);
`Mathlib.AlgebraicGeometry.Noetherian` (`IsLocallyNoetherian`, `IsNoetherian`);
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` (`IsDomain`,
`IsIntegrallyClosed`); `Mathlib.AlgebraicGeometry.Properties` (`IsIntegral`);
`WeilConjectures.Mathlib.FieldTheory.IsSepClosed` (the `IsSepClosure` interface);
`Sheaf.Topology.ContinuousMapCondensedRing`
(`continuousMapRingObjOfUniverse` and its monoid structure);
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
(`coefficientRing`, `condensedRingObj`);
`Mathlib.CategoryTheory.Monoidal.Mod` (`Mod`);
`Sheaf.Paper.CoefficientHeartStratificationDefs` (`IsLisseCoefficientModule`);
`Mathlib.AlgebraicGeometry.Sites.Proetale` (`Scheme.ProEt`, `topology`);
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`
(the canonical continuous coefficient comparison theorem).

The item also cites the following already landed nodes because their definitions
occur in the detailed signature. They are added to stmt_deps, with no change to
any dependency record:

* `def-sfb-norm-continuous-monodromy-data`, module
  `Sheaf.Paper.NormContinuousMonodromyData`: `normContinuousRing`,
  `NormContinuousLisse`, `NormContinuousRepresentations`, `normContinuousScalar`.
* `def-sfb-field-separable-cech-nerve`, existing module
  `Sheaf.Paper.FieldSeparableCechCoordinates`: `closureObject`, `closureArrow`,
  `object`, `power`, `cumulative`, `testPoint`, and `AreCoordinates`. The theorem
  node `lem-sfb-field-separable-cech-coordinates` remains in `proof_deps` for
  `coordinates`, `section_coordinates`, and `module_coordinates`.
* `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, module
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRings` and `sectionModuleFunctor`. `sectionAction` uses their actual
  pointwise module action with unchanged underlying sections and restrictions.
* `def-sfb-continuous-ring-canonical-comparison`, module
  `Sheaf.Paper.ContinuousRingUniverseRealization`: `comparison`, with its
  canonical adjoint normalization and ring-morphism instance.

Proof-only imports include
`Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents`
(`normal_topologicallyNoetherian_components`) and
`Sheaf.CategoryTheory.Sites.GrothendieckTopos`. The generic-section module
`Sheaf.AlgebraicGeometry.NormalGenericContinuousSections` gives
`normal_generic_continuous_sections`. The free-matrix and minimal-closed-subset
proof nodes have no recorded Lean declarations in the read clone, so there is
no module of theirs to import. They are not needed to type the present statement.
No proof-only missing node is replaced by a new assertion or assumed as a hypothesis.

### Edge cases and searches

Checked mathematically: X=Spec k; nonempty connected X versus the excluded empty
scheme; empty pro-etale objects and empty trivializing charts; zero module and
rank zero; arbitrary m=0 or n=0 in rectangular Hom matrices; trivial norm;
incomplete coefficient fields; finite, positive and mixed characteristics;
non-affine overlaps (handled by affine refinement in the proof, with no separatedness
hypothesis). Units of the empty square matrix ring exist despite that ring being
trivial, so no hidden `Nontrivial` assumption is introduced at n=0.

Searches on 2026-10-22:

* `msearch.py ... leanfinder "Generic restriction of lisse pro etale normed field
  coefficient modules is fully faithful and defines continuous Galois representations"`:
  eight related results, including `LightCondMod.LocallyConstant.fullyFaithfulFunctor`
  and `CondensedMod.LocallyConstant.fullyFaithfulFunctor`; none asserts generic
  restriction with all-continuous normed coefficients.
* `msearch.py ... leansearch "Generic restriction of lisse normed field coefficient
  modules on normal Noetherian schemes is fully faithful"`: eight related
  forgetful/scalar-restriction facts, none an exact match.
* `msearch.py ... loogle '"Sheaf", "FullyFaithful"'`: eleven results, including
  fully faithful sheaf/presheaf forgetful functors; none a match.
* `msearch.py ... grep '(generic|functionField).*(lisse|FullyFaithful)|(lisse|proetale).*cocycle'`:
  zero Mathlib hits.
* `rg` with that expression in `lean/WeilConjectures` and `lean/Sheaf` found
  unrelated generic lissity results, not this statement. Searching the item id
  found no existing statement module.
* Name searches for `NormalGenericLisse` and `normal_generic_lisse_cocycle` in
  Mathlib, the source roots and `dag/lean_names_upstream.json` found no existing
  declaration with those names. Topic searches found and reused
  `NormContinuousMonodromyData`, `FieldSeparableCechCoordinates`, and
  `NormalGenericContinuousSections` rather than duplicating those notions.

No mathematical statement correction, dependency interface repair, or
STATEMENT-DISPUTED flag is needed. The return repair adds the definition-ownership
node described below. The fibre and matrix helper
declarations are part of this node's detailed canonical construction and are all
listed in lean.declarations.

### Validation

All delivered definitions are concrete and autoImplicit is disabled. The module
uses module mode, public statement imports, plain proof imports, and no line
exceeds 100 characters. Compilation and the prescribed preflight are run through
the authorized wrappers only.

The original packet passed scompile.py and deliver2.py --no-push.
After the H2 ownership repair, a fresh scompile.py passed without warnings in
sandbox mode (17.1 s) and library-module mode (15.9 s), within the unchanged
per-file 60-second limit. The repaired packet includes the existing-definition
node as well as the item module, item node and report.

## New nodes

`def-sfb-field-separable-cech-nerve` owns exactly the seven existing plain
definitions in `Sheaf.Paper.FieldSeparableCechCoordinates`, without a new Lean file.
Its source is Bhatt–Scholze Example 4.1.4 and the separable-closure construction
in Section 7.4, expanded in the field-coordinate node's proof steps 1–4;
Stacks Tag 0BU2 supplies the Krull-limit description. The statement introduces
fields k and Ω with `Field`/`Algebra`/`IsSepClosure`, and then matches `U` to
`closureObject`, its final-target arrow to `closureArrow`, W_q to `object`,
G^q to `power`, ordered initial products h_j to `cumulative`, evaluation points
t_g to `testPoint`, and both the first-projection and all-vertex equations
to the two conjuncts of `AreCoordinates`. Degree zero has one vertex and an
empty Galois tuple; cumulative products are 1 for j=0 and stop after q entries.
The definition imposes no coefficient assumptions and asserts no coordinate
existence. Every construction has actual data; `weaklyEtale` is used only
for the structural Prop proof of the closure object. Universally quantified
coordinates are never chosen from the theorem.

New searches on 2026-10-22: LeanSearch for “Separable closure Cech nerve with
Galois cumulative vertex coordinates and profinite test points” returned eight
separable-closure results, with no whole notion; LeanFinder for “The Cech nerve
of Spec of a separable closure, profinite powers of the Galois group, and
cumulative vertex coordinates” returned eight general Cech/profinite results.
The prescribed Mathlib grep `closureObject|closureArrow|AreCoordinates|FieldSeparableCech`
returned zero hits. The source-root grep found the exact existing declarations
at FieldSeparableCechCoordinates.lean lines 59–120, no upstream copy.
The definition-node grep found no owner, and `blueprint_refs.py search` with
`separable.*[Cc]ech|[Cc]ech.*separable` returned zero blueprint nodes.
The new node records these actual searches, with raw wrapper log results.
`blueprint_refs.py ancestor` returned None, retained as null with the item's
place and prefixed via path, matching the existing-node precedent.

## Return repair

The independent reader's H2 finding on fd0bc2a3e42e is repaired by adding
`def-sfb-field-separable-cech-nerve` with `existing: true` and replacing
`lem-sfb-field-separable-cech-coordinates` in the item's added `stmt_deps`.
The theorem remains in `proof_deps` unchanged. All twelve original statement
dependencies remain. The item differs from the current live node only in
`lean` and `stmt_deps`. Its Lean module, theorem signature, hypotheses,
conclusions, constructions and imports are unchanged from the returned packet.
The first dry run of the saved packet passed at commit 5d80fcd9650; this
mechanical pass did not remove the need for the ownership repair.

The advisory on `BasisChangeAssertions` needs no change: its identities give
the basis-change clause exactly as the reader confirmed. The remaining
hypothesis/clause and edge-case checks above are retained from the reviewed
packet. No independent second reading is claimed by this worker; the
maintainer's independent delivery review remains the review step.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
