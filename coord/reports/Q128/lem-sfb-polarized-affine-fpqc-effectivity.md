## Worker report

The module `Sheaf.AlgebraicGeometry.PolarizedAffineFpqcEffectivity` states
`AlgebraicGeometry.exists_polarized_affine_fpqc_descent`. Its only theorem proof
is `sorry`. There are no new definitions, dependency modules, new nodes or
statement corrections. The original statement and dependency lists are unchanged.

Source checked: BLR, Néron Models, §6.1, Theorem 7, printed p.138 (PDF p.144),
and the preceding definition of descent of pairs on printed pp.137–138. The
[primary scan](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf)
was opened online. The theorem applies to a quasi-compact upstairs scheme with a
relatively ample line module. For affine bases this is precisely the absolute
ampleness condition in the node; no properness or finite presentation enters.
The eight-step proof in the node is recorded in the theorem docstring.

Hypotheses and conclusions, clause by clause:

* Commutative rings and their faithfully flat homomorphism: `{B C : Type u}`,
  `[CommRing B] [CommRing C]`, `φ : B →+* C`, `hφ : φ.FaithfullyFlat`.
* The bases are exactly `Spec (CommRingCat.of B)` and
  `Spec (CommRingCat.of C)`, with base map `Spec.map (CommRingCat.ofHom φ)`.
* The upstairs scheme and structure map are `V : Over (Spec (CommRingCat.of C))`;
  `X'` is `V.left`, its structure morphism is `V.hom`, and its quasi-compactness
  is `[QuasiCompact V.hom]`. This does not impose local finite type.
* The supplied scheme descent datum is exactly the dependency's
  `D : Over.DescentDatum (Spec.map (CommRingCat.ofHom φ)) V`.
* The specified invertible module is `M' : V.left.Modules`, `[M'.IsInvertible]`.
  Its absolute ampleness is `hM' : Scheme.Modules.IsAmple V.left M'`, using the
  recorded general scheme definition, not `AlgebraicGeometry.IsAmple` from
  `Modules.Ample` (the latter concerns projective schemes over fields).
* The module isomorphism over the scheme datum is the natural family `ell`.
  Given a test scheme `T`, lifts `f₀,f₁` of the same point of `S`, and a point
  `a : Over.mk f₀ ⟶ V`, write `b := D.transport f₀ f₁ h a`. The isomorphism
  `ell f₀ f₁ h a` is `a.left* M' ≅ b.left* M'`, exactly the two requested
  pullbacks after the scheme transition.
* `hell_natural` identifies its restriction along every `g : T' ⟶ T` with
  `g* (ell f₀ f₁ h a)`, normalizing both ends with the dependency's
  `tensorPullbackSectionComp`. This is the naturality required to present ONE
  overlap isomorphism by all of its pullbacks, not an additional descent axiom.
* `hell_cocycle` says that the two consecutive isomorphisms compose to the direct
  one for `f₀,f₂`. This is exactly the module cocycle on the triple overlap.
  No extra identity hypothesis is imposed; invertibility and the cocycle imply it.
* The descended scheme is `X : Over (Spec (CommRingCat.of B))`, and `M` is
  `X.left.Modules` with the explicit invertibility witness `hM`.
* `IsPullback q V.hom X.hom (Spec.map (CommRingCat.ofHom φ))` supplies the
  base-change isomorphism `X ×_S S' ≅ X'` over `S'`, with its map to `X`
  equal to `q`. The module part is the specified existential isomorphism
  `e : (tensorPullback q).obj M ≅ M'`.
* The first universally quantified conclusion is exactly the invariance clause
  of `Over.DescentDatum.IsEffective`: `(D.transport ... a).left ≫ q = a.left ≫ q`.
  Thus the cartesian identification induces the original scheme datum.
* The final universally quantified conclusion states that `a*e`, followed by
  `ell`, is the pullback `b*e` of the SAME `e`. Both are normalized from the
  composite maps to `X` with `tensorPullbackSectionComp`. This recovers the
  prescribed module datum, rather than only giving some line-module isomorphism.
* `@Scheme.Modules.IsAmple X.left M hM` states ampleness of that descended module.
  No Noetherianity, properness, finite presentation, nonemptiness, field, or
  projectivity hypothesis is present.

Why transport is equivalent to the node's overlap formulation:
let `p = Spec.map φ` and `R = X' ×_S S'`, with projections `a₀ : R → X'` and
`f₁ : R → S'`, and put `f₀ = a₀ ≫ V.hom`. Then `a₀` is a point over `f₀`,
and `D.transport f₀ f₁ ... a₀` is the second map `R → X'` given by the supplied
scheme isomorphism. Specializing `ell` to this universal tuple gives precisely
one module isomorphism on `p₀* X'`, identified canonically with `R`. Every test
tuple factors uniquely through `R`; `hell_natural` makes its `ell` the pullback
of that universal isomorphism. Likewise the universal triple gives the cocycle,
and pullback gives its formula for all triples. The conclusion is verified on
that same universal tuple. The recorded scheme datum already uses this Yoneda
transport formulation, and no second notion of scheme descent is introduced.

`HEq` is used only because source/target pullback objects are indexed by equal,
rather than definitionally identical, scheme maps. In naturality the equality
is `D.transport_homMk_comp`; in the cocycle it is `D.transport_transport`; in
the conclusion it is the preceding invariance equation for `q`. Thus `HEq`
expresses equality under equality transport, not an arbitrary comparison map or
an existential isomorphism. All tensor composition comparisons are actual
section-normalized ones from `def-pc-module-pullback`.

Dependency declarations read and used:

* `def-weil-pbc-faithfully-flat-ring-map`:
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`, and
  its recorded ring-map version `RingHom.FaithfullyFlat` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` (the latter is used directly).
* `def-weil-affine-spectrum`, `def-pc-scheme`:
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme`, and `Scheme.Hom`.
* `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its public dependency
  `Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`. Only the
  quasi-compact part of the definition node is needed here.
* `def-pd-descent-datum`:
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`,
  `CategoryTheory.Over.DescentDatum`, its transport laws, and `IsEffective`.
* `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
* `def-weil-pbc-ample-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.
* `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, the publicly
  imported upstream `AlgebraicGeometry.Scheme.Modules.tensorPullback`, and
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionComp`.
* `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback` and
  projections; effectivity uses the equivalent `IsPullback` predicate already
  used in the recorded `IsEffective` definition.
* `def-pc-base-change`:
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, its cartesian
  base-change convention. `moduleBaseChange` concerns an already chosen fibre
  product; the present identification uses its underlying `tensorPullback q`.

Available recorded proof-dependency modules are imported without `public`.
The Mathlib flatness criterion, faithfully flat spectrum surjectivity and fpqc
covering axioms are also proof imports. `Proj` is publicly supplied through the
recorded Proj-chart proof import. Two proof dependencies have no declaration
record yet and are consequently not imported: `lem-sfb-space-relative-ampleness-fpqc-descent`
and `lem-trf-affine-base-ample-canonical-data`. They remain in the unchanged
proof plan for stage 3. All statement dependencies have usable declarations.

Edge cases checked before drafting and again after elaboration:

* Empty upstairs scheme: there is no nonempty assumption on `V.left`; the ample
  covering condition is vacuous and the descended square may be empty.
* The zero ring is allowed for either ring. Faithful flatness supplies the
  necessary compatibility of empty spectra; no `Nontrivial` binder is present.
* Identity base map and identity transition: the family specializes to canonical
  identity comparisons; no restriction to distinct lifts occurs.
* All three lifts may coincide; cocycle still applies and forces the identity.
* Arbitrary characteristic and arbitrary faithfully flat maps are allowed,
  including maps not of finite presentation and non-Noetherian rings.
* The common universe `u` contains both rings and the schemes; all test schemes
  are `Scheme.{u}`, including the universal double and triple pullbacks. There
  is no independent smaller testing universe that would make a hypothesis vacuous.

Searches (2026-10-24):

* `msearch.py ... leansearch "A scheme with ample invertible module and compatible
  fpqc descent datum descends effectively"`: eight hits, on descent of morphism
  properties and affineness; none states effective descent of polarized schemes.
* `msearch.py ... leanfinder "Effective fpqc descent of schemes equipped with
  compatible ample invertible modules"`: eight hits, including
  `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`; these concern
  existing morphisms and do not construct the descended scheme/module pair.
* `msearch.py ... loogle "CategoryTheory.Over.DescentDatum,
  AlgebraicGeometry.Scheme.Modules.IsAmple"`: zero hits, with Loogle reporting
  the project-only `Over.DescentDatum` identifier unknown.
* `msearch.py ... grep "polariz|Polariz|DescentDatum" AlgebraicGeometry`:
  zero Mathlib hits.
* `rg` of `lean/WeilConjectures` and `lean/Sheaf` for polarized names and
  `IsAmple`, plus exact declaration-name searches and
  `grep -rn "lem-sfb-polarized-affine-fpqc-effectivity" lean/WeilConjectures`:
  no exact theorem or blueprint binding found. Existing `Ample` and `Invertible`
  notions are reused. `PolarizedSchemeEtaleDescent` treats an étale cover and
  relative ampleness, not arbitrary faithfully flat affine base change;
  `QuasiAffineFpqcDescent` assumes a quasi-affine morphism, which this theorem
  does not assume. Neither is the requested statement.
* `dag/lean_names_upstream.json` was included in the exact declaration-name
  search. No collision with `exists_polarized_affine_fpqc_descent` was found.

No node fault or statement dispute was found. The local compiler mirror reported
`OSError(28, 'No space left on device')`; the prescribed wrapper automatically
confirmed against the server, where the statement compiled cleanly in 2.7 seconds.

## Second reading by Q128

This was a second pass by the same dispatched worker, as this brief explicitly
prohibits starting another agent; the maintainer supplies the independent review.
I reopened the node statement and the final module, checked all ten statement
dependencies, and traced each input and output as above. The initially drafted
binder name `λ` was Lean syntax and was renamed `ell`; it had no mathematical
role. I checked the direction `a* M' → b* M'` against the node's direction
`p₀* M' → α* p₁* M'`, checked both composition normalizations in naturality,
and checked that the last equality uses the same `e` for both transports.
The cartesian square plus invariance is precisely the recorded effective scheme
datum; the module compatibility is additional and essential. The ample predicate
is the correct absolute, arbitrary-scheme one. There are no added finiteness or
separatedness binders. No mathematical mismatch remained and no statement field
was changed. All declarations are explicit in universe `u` with `autoImplicit`
disabled, and the single postponed proof is the whole theorem proof.
