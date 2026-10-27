## Worker report

Delivered `Sheaf.CategoryTheory.EquivariantHomQuasiIsomorphism`, namespace
`CategoryTheory.Endofunctor.IsoAlgebra`. The primary theorem is
`exists_equivariantHom_quasiIso`; the structural paragraph is the separate
`equivariantHom_forget_properties`, also listed in the node's declarations.
All three theorems have `sorry` proofs. Definitions have actual data. The third
postponed theorem, `equivariantHomTensorPair_naturality`, is precisely the
restriction compatibility needed by the pure-tensor helper; its docstring gives
the presheaf restriction and sheafification-naturality argument. No construction
is selected from a merely existential sorried theorem.

Source read: `literature/stacks-project/sites-cohomology.tex`, section
`section-hom-complexes` (0A8X), especially `lemma-RHom-well-defined` (0A95),
lines 8754 onward; `literature/stacks-project/derived.tex`,
`lemma-adjoint-preserve-K-injectives` (08BJ), lines 9857–9877. The current blueprint
anchor was read at `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-i-dl-a1-local/lem-a1-local-boundary-duality.proof.md`, including the opening
lisse-duality identity and the final evaluation/Frobenius paragraph.

Hypotheses and objects, matched to Lean:

- The site small in the coefficient universe is `{C : Type u} [SmallCategory C]`,
  `{J : GrothendieckTopology C}`. The commutative ring sheaf is
  `{R : Sheaf J CommRingCat.{u}}`. These variables are explicitly bound in the
  section, and `autoImplicit` is false. Site objects, arrows and coefficients
  belong to the one specified small universe; `w` independently bounds derived
  morphisms. No finite-type, geometric-point, or boundedness restriction appears.
- The topos automorphism and specified invertible ring map are the existing
  `RingedToposMorphism (localCoefficientRings R) (localCoefficientRings R)`
  with `[e.inverse.IsEquivalence] [IsIso e.ringMap]`. This is an arbitrary
  automorphism of the sheaf topos, not a site automorphism.
- The phrase “T is the induced additive exact autoequivalence” is represented
  by `P : RingedPresentationAt e`, universally quantified over presentations of
  that induced functor, with `T = P.transport.modules.functor`. This is the
  existing presentation data, not an arbitrary unrelated equivalence:
  `P.pushforward` identifies its inverse with the specified `e.modules`,
  `P.underlying` identifies its underlying inverse image with `e.inverse`, and
  `P.structural` fixes the unit map to be `e.ringMap`. Such presentations exist
  under exactly these hypotheses, by `ringed_presentation_transport` in
  `Sheaf.CategoryTheory.RingedPresentationTransport` (its `whole` field).
  The module never chooses a presentation from this existence theorem.
  Additivity is the named instance inherited from preservation of binary
  products; exactness and equivalence are already the recorded structures.
- C is `PresentationModules R`, literally the recorded `ringedSiteModules`
  abbreviation for Mathlib `SheafOfModules`. W is the existing `IsoAlgebra T`,
  and U is its existing `forget T`. No category, action, derived category or
  internal Hom is copied.
- K-injectivity is Mathlib `CochainComplex.IsKInjective`, whose field says that
  every map from an acyclic complex admits a homotopy to zero. The only two
  target hypotheses in the last clause are `I'.IsKInjective` and `I.IsKInjective`.
  There is no K-injectivity hypothesis on K or K'.
- The ordinary derived category is `DerivedCategory (IsoAlgebra T)` with the
  explicit size-model binder `[HasDerivedCategory.{w} (IsoAlgebra T)]`, and the
  localization is `DerivedCategory.Q`. Quasi-isomorphism is Mathlib `QuasiIso`.

Every construction and conclusion:

- Internal Hom is the existing `SheafOfModules.homObj (R := R) M N`. Its
  section over V is the linear morphism on the localized site in the upstream
  `InternalHom.lean` definition, not a presheaf of sectionwise module Hom sets.
- The existential tensor comparison χ is normalized by the pure-tensor equation
  using `P.underlying`, `prodComparison e.inverse`, and `e.inverse.map` of
  `equivariantHomTensorPair`. This latter map is the actual sheafification of
  `x ⊗ₜ y`, constructed with the existing tensor/sheafification unit. It specifies
  the geometric pullback tensor comparison without assuming tensor exactness.
- The existential γ is normalized by
  `T.map (equivariantHomEvaluation M N) = χ.hom ≫ (𝟙 _ ⊗ₘ γ.hom) ≫ evaluation`.
  The tensor-Hom adjunction makes this the unique comparison with that evaluation
  equation; it is not a bare arbitrary isomorphism.
- `equivariantHomPair T γ M N` has carrier the existing internal Hom. Its
  structure is `γ M.carrier N.carrier`, followed by precomposition with
  `M.str.inv` and postcomposition with `N.str.hom`. Thus its formula is exactly
  θ_N T(h) θ_M inverse; the contravariant variable uses `M.str.symm.op`.
- The integer-indexed product in degree n is specified by the equivariant
  projections `π K I n p` and `Nonempty (IsLimit (Fan.mk ... (π K I n)))` in W.
  The factor is `equivariantHomPair T γ (K.X p) (I.X (p+n))`.
- The natural identification of complexes is the natural isomorphism α of
  uncurried bifunctors. Its source is H followed by termwise U; its target is
  the existing `homComplexFunctor (R := R)` applied to UK and UI.
  The equality relating `U.map (π K I n p)` to `α.hom.f n ≫ homComplexπ ...`
  fixes α to be the identity on each Hom factor. Consequently it identifies
  the differential with the source's exact signed differential
  `d_I f - (-1)^n f d_K`, using `homComplex_d_π`. In particular neither a
  different sign nor a reindexing of factors can satisfy the projection equation.
- `equivariantHom_forget_properties` asserts creation of the ℤ products,
  preservation of finite limits and colimits (exactness), preservation of
  K-injective complexes, and `QuasiIso f ↔ QuasiIso (Ucomplex.map f)`.
  Creation is data-valued in Lean, so is stated with `Nonempty`, not a Prop
  coercion. Addition of morphisms is the existing inherited instance.
- The last clause universally quantifies arbitrary complexes K', K, I', I
  and maps `t : K' ⟶ K`, `v : I' ⟶ I`. Its four hypotheses are precisely
  K-injectivity of the two targets and quasi-isomorphism of both maps. The
  morphism is `(H.map t.op).app I' ≫ (H.obj (op K')).map v`.
  Being a morphism in `CochainComplex (IsoAlgebra T) ℤ` states both equivariance
  and the chain-map equation. Naturality of α identifies it with the ordinary
  componentwise map `v^(p+n) f_p t^p` by `homComplexFunctor_map_f_π`.
- The conclusion asserts both `QuasiIso` of that exact map and
  `IsIso (DerivedCategory.Q.map ...)`. There is no replacement by a merely
  isomorphic object or by an unspecified comparison map.
- All complexes are ℤ-indexed and unbounded. The module assumes neither
  boundedness, local freeness, flatness, exact tensoring, nor exact products.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `CategoryTheory.Endofunctor.IsoAlgebra`, `forget`, `mk`, `str`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `RingedToposMorphism`.
- `Sheaf.CategoryTheory.RingedPresentationData`: `PresentationModules`,
  `presentationForget`, `RingedPresentationAt`, including all its fields.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and inherited tensor structures.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`, `homFunctor`.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex`, `homComplexFunctor`.
- `WeilConjectures.Algebra.Homology.HomComplexProjections`:
  `homComplex_projections_exists`; its upstream components module exposes
  `homComplexπ`, `homComplex_d_π`, `homComplexFunctor_map_f_π`.
- Proof imports are the recorded Grothendieck theorem, fixed-pair derived
  forgetful comparison, and ordinary `quasiIso_homComplex_map`. The unstated
  proof-only `lem-sf-fixed-pair-created-abelian-structure` has no module to
  import. Its assertions are not assumed as new hypotheses.

The item's statement and reviewed split are unchanged. Its stmt_deps only gains
six existing, recorded nodes for the explicitly used presentation, ringed-topos,
Hom, tensor and projection interfaces. Their transitive dependencies were checked
not to reach this item. There are no new nodes or dependency repairs.

Edge cases checked by reading the mathematical construction and signature:
identity topos action and ring map; t or v an identity; zero K or I; the zero
ring; the empty site; complexes unbounded in both directions; negative degrees
and odd/even n. Identity action gives ordinary Hom with its usual conjugation.
Zero factors and empty sites give zero sheaves, compatible with product cones
and evaluation. Products have all p : ℤ, including arbitrarily negative p.
The ordinary Hom differential has the displayed parity sign at all integers.
No excluded edge case or statement fault was found.

Searches actually run, through the prescribed msearch wrapper:

- LeanFinder: “Equivariant product internal sheaf Hom complex preserves quasi
  isomorphisms into K injective fixed pairs”: eight generic K-injective,
  ordinary derived-Hom and representation results; no exact equivariant
  internal sheaf Hom construction or statement.
- Loogle: `"IsKInjective", "homComplexFunctor"`: zero hits.
- Grep: `homComplexFunctor|bifunctorHom`: twenty Mathlib bifunctor-complex
  results, no exact match.
- LeanSearch: “The product internal Hom of equivariant complexes into K
  injective targets preserves quasi isomorphisms”: eight generic preservation
  and detection of quasi-isomorphism results, no exact match.
- Direct rg of WeilConjectures and Sheaf for the item id, equivariant/Hom,
  homComplexFunctor, homObj, IsoAlgebra, and the new declaration names.
  Found the reusable ordinary Hom and fixed-pair interfaces above, plus
  the site-automorphism-only twisted presentation. That presentation does not
  cover arbitrary topos automorphisms. No existing exact statement was found;
  all new declaration names had no prior match. `lean_names_upstream.py show`
  supplied no exact attachment for this item.

Validation: scompile.py compiled both the sandbox module and its actual library
module successfully, with no diagnostics. The intermediate missing monoidal
instance import and inferred sheafification universe were repaired by using the
shared coefficient-universe tensor import and explicit universe arguments.

## Second reading by Q54

This is the author's second reading, as required by the dispatcher instruction
not to start another agent. Independent review belongs to the maintainer.
I reopened the node, all of its proof steps, the actual finished Lean module,
and the source 0A95 statement. I checked the correspondence above clause by
clause. In particular I checked the direction of θ_M inverse in the op variable,
the p+n target index, the source H(K,I') and target H(K',I), the two target-only
K-injectivity hypotheses, the exact same map inside QuasiIso and Q.map, and the
projection normalization of the natural identification. The pure-tensor equation
runs from U(TM)×U(TN), first through the tensor pairing and χ inverse, and on the
other side through the inverse product comparison and pullback of the pairing;
thus it has the canonical pullback orientation. Evaluation fixes γ in the same
orientation. The structural theorem contains all four forgetful clauses.
No mathematical mismatch was found on this reading. Initial compilation faults
were repaired as recorded above; no source statement was changed to do so.
