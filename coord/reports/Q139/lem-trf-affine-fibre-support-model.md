## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFibreSupportModel` states
`AlgebraicGeometry.Scheme.Modules.exists_affine_fibre_support_model`, with
`sorry` as its entire proof. No definitions, auxiliary theorems, new nodes,
dependency repairs, or statement corrections were needed. The item's JSON
changes only in `lean`.

Source read: `literature/stacks-project/flat.tex`,
`lemma-elementary-devissage` (Tag 057S), especially the affine reduction
at lines 536ff and the general-case application of
`lemma-sheaf-lives-on-subscheme` (Tag 057Q); the latter's statement and proof
at lines 445ff were also read. The statement and all six proof steps of the
item were read, together with its statement dependencies' records and their
actual Lean declarations. The docstring carries the six-step proof plan.

Hypotheses and clauses, in the order of the node:

1. Schemes and the locally finite type morphism are
   `{X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]`.
   There is no quasi-compactness or separation assumption on the original f.
2. The finite-type quasi-coherent module is `(F : X.Modules)` with
   `(hF : F.IsQuasiCoherentFiniteType)`. This is the dependency's existing
   conjunction of `SheafOfModules.IsQuasicoherent F` and
   `SheafOfModules.IsFiniteType F`; it does not impose coherence.
3. `(x : X)` is arbitrary, with `hx` saying that the stalk of
   `(tensorPullback (f.fiberι (f x))).obj F` at `f.asFiber x` is not
   subsingleton. `f.asFiber x` is the canonical point of `X_{f(x)}` over x,
   using Mathlib's homeomorphism between the scheme fibre and the inverse-image
   set. This renders exactly x in Supp(F_s), with s = f(x).
4. The symbol n is expanded, rather than introduced as an extra hypothesis:
   it is `topologicalKrullDimAt` of `⟨f.asFiber x, hx⟩` in the subspace
   `{y : f.fiber (f x) | ¬ Subsingleton (F_s.presheaf.stalk y)}`.
   Thus this is the minimum-over-open-neighbourhoods dimension of the support,
   not stalk-ring dimension or the dimension of the entire fibre.
5. The affine neighbourhoods are existential schemes U and V with morphisms
   u and v, `IsAffine U`, `IsAffine V`, `IsOpenImmersion u`, and
   `IsOpenImmersion v`. The point equation
   `u (j ((j ≫ p).fiberι sV z)) = x` ensures the image of u contains x;
   the witness `sV : V` and `hv : v sV = f x` ensure the image of v contains s.
   An affine open neighbourhood can equivalently be represented by an affine
   scheme with an open immersion and the specified point in its image.
6. The restricted morphism p is existential, with `LocallyOfFiniteType p`,
   `QuasiCompact p`, and `u ≫ f = p ≫ v`. The first two properties are
   exactly the node's finite type condition in its recorded interface.
7. The affine scheme Z and closed immersion j are existential, with
   `IsAffine Z`, `IsClosedImmersion j`, `LocallyOfFinitePresentation j`,
   `QuasiCompact j`, and `QuasiSeparated j`. This includes all three
   finite-presentation clauses specified in the node.
8. H is an existential `Z.Modules` with `H.IsQuasiCoherentFiniteType`.
   `LocallyOfFiniteType (j ≫ p)` and `QuasiCompact (j ≫ p)` render that
   Z → V is finite type. The witness `z : (j ≫ p).fiber sV` lies in the
   fibre formed over V, not a substitute fibre over S. Its point equation
   from item 5 is precisely j(z) = x after the open inclusion into X.
9. `Nonempty ((pushforward j).obj H ≅ (tensorPullback u).obj F)` is the
   requested isomorphism j_*H ≅ u*F of modules. Mathlib's existing
   `Scheme.Modules.pushforward` is the direct image specified by the node:
   `pushforward_obj_obj` at Modules/Sheaf.lean:170 identifies its sections
   on E with H on j^{-1}(E). No arbitrary functor is substituted.
10. `us : p.fiber sV ⟶ f.fiber (f x)` is uniquely characterized by BOTH
    projection equations. Its first projection is `p.fiberι sV ≫ u`;
    its second is `p.fiberToSpecResidueField sV` followed by
    `Spec.map ((S.residueFieldCongr hv).inv ≫ v.residueFieldMap sV)`.
    The residue-field congruence merely transports along hv; its direction
    was checked against the contravariant Spec map. These equations specify
    the actual canonical comparison, not an unconstrained map. The pullback
    universal property gives uniqueness. `IsOpenImmersion us` represents
    the identification U_s ⊆ X_s.
11. `js : (j ≫ p).fiber sV ⟶ p.fiber sV` is likewise uniquely fixed by
    both projections: its first is `(j ≫ p).fiberι sV ≫ j` and its second
    is `(j ≫ p).fiberToSpecResidueField sV`. It is therefore the canonical
    base change j_s. The conjunction `IsClosedImmersion js` and
    `Set.range js.base = {y | ¬ Subsingleton (((tensorPullback
    (p.fiberι sV)).obj ((tensorPullback u).obj F)).presheaf.stalk y)}`
    says it identifies Z_s homeomorphically with Supp((u*F)_s): a closed
    immersion is a topological closed embedding, hence a homeomorphism onto
    its range with the subspace topology. No reduced scheme structure on
    the support is asserted.
12. The following image equality under `us.base` says that this same local
    support is `Supp(F_s) ∩ Set.range us.base` inside X_s. Both support
    expressions are nonzero-stalk loci of the actual tensor pullbacks.
13. `topologicalKrullDimAt z = topologicalKrullDimAt (⟨f.asFiber x, hx⟩ : ...)`
    renders dim_z Z_s = n with precisely the support subspace from item 4.
14. `Etale u ∧ Etale v` states both etaleness conclusions. The final
    `∀ y : U, IsIso (u.residueFieldMap y)` and
    `∀ t : V, IsIso (v.residueFieldMap t)` include every point of U and V,
    rather than only the distinguished points.

Recorded dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; the same module supplies `Spec` and `Spec.map` for
  `def-weil-affine-spectrum`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; `QuasiCompact` is the recorded
  accompanying class from `Morphisms.QuasiCompact`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and universal property.
  `Mathlib.AlgebraicGeometry.Fiber` supplies the actual scheme specializations
  `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`, and `asFiber`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly exposing
  the upstream `Scheme.Modules.tensorPullback`. No Mathlib `Modules.pullback`
  is used in the statement.
- `def-weil-pbc-module-stalk`:
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj`. The displayed
  `.presheaf.stalk` is its underlying additive stalk, definitionally the
  same carrier; vanishing is `Subsingleton`, as required by the brief.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt`, defined as the infimum of dimensions of open
  neighbourhoods. Its values lie in `WithBot ℕ∞`, which admits empty and
  infinite-dimensional spaces without a new finiteness assumption.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, including its `isClosedEmbedding` field.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; the conjunction also uses
  `QuasiCompact` and `QuasiSeparated` from the recorded convention.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.

All statement-dependency modules are public imports. Proof-only imports give
`exists_finitePresentation_closedImmersion_fiber_support` from
`Sheaf.AlgebraicGeometry.FiniteTypeSheafFinitePresentationSupport`, the affine
morphism and affine-open-basis facts, the pointwise criterion in
`Morphisms.RingHomProperties`, `tensorPullback_isFiniteType` from
`WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType`, and
`isQuasicoherent_pullback` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`. The latter is the
Mathlib-pullback formulation; stage 3 transports it along the tensor-pullback
adjunction comparison rather than treating the two functors as definitionally
identical. The other proof-dependency modules are already public imports
(open and closed immersion base change, etaleness, residue-field naturality,
and `IsOpen.topologicalKrullDimAt_eq`). No import cycle was introduced.

Edge cases checked before and after writing:

- If F = 0, or the fibre support is empty, hx cannot hold. No nonempty
  support or finite positive dimension is smuggled into another hypothesis.
- An empty X has no x, as in the source. An empty affine scheme is not
  excluded by any of the affine predicates.
- Zero-dimensional support and a nonclosed x are allowed: the dimension is
  that of the support at its point, not the local ring or closure of x.
- Nonreduced supports are allowed. Z may be a nonreduced thickening;
  the comparison is topological, not an equality with a reduced support scheme.
- Non-quasi-compact and non-quasi-separated X and S remain allowed. Only
  p, j, and j ≫ p receive the stated finiteness hypotheses/conclusions.
- All schemes have arbitrary explicit universe u, the same universe required
  by the recorded scheme-module and tensor-pullback interfaces. There are no
  auto-bound universes or variables (`autoImplicit` and `relaxedAutoImplicit`
  are both false).
- Canonical fibre maps are pinned down by both projections, including the
  residue-field direction along the base open immersion. There is no arbitrary
  choice of a residue-field embedding or comparison morphism.

Searches performed (2026-10-24):

- `msearch.py ... leanfinder` with query
  `A locally finite type scheme morphism and finite type quasi coherent module admit an affine supporting model preserving fiber support and local dimension`:
  8 hits, including `Scheme.Hom.finiteType_appLE`, `LocallyOfFiniteType`,
  `locallyOfFiniteType_iff`, and finite affine morphism criteria; none states
  the support-model theorem.
- `msearch.py ... loogle` with query
  `"IsClosedImmersion", "LocallyOfFiniteType"`: one hit,
  `AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion`, which only
  provides local finite type for a closed immersion.
- `msearch.py ... grep` with regex
  `support.*(fiber|fibre)|(fiber|fibre).*support` in `AlgebraicGeometry`:
  0 hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  affine/fibre/support combinations, and the proposed declaration name:
  no existing declaration of this statement. The broader affine-support
  search found perfect-complex supporting models, affine homology support,
  and the existing finite-type support dependency; their signatures concern
  different statements. The exact item id and proposed name also have no
  match in `dag/lean_names_upstream.json`.

Validation: prescribed `scompile.py Q139 lem-trf-affine-fibre-support-model`
compiled the file both as sandbox and as its library module, cleanly, in
5.0 s and 1.9 s respectively. There are no diagnostics or warnings.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q139

The delivered section under this heading was a self-reread by the delivering dispatcher worker
(H11). It is replaced by the independent maintainer second reading of delivery 60a1fb61a5c5
(2026-10-24). The Lean file and the node record are unchanged.

Node clauses and the Lean that renders each one:

1. f : X → S locally of finite type ↔ `{X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]`.
   There is no qc/qs assumption on f, X or S, as in Stacks 057S. Correct.
2. F is a finite-type quasi-coherent module ↔ `hF : F.IsQuasiCoherentFiniteType`, the
   pqf-def-coherent record's conjunction of IsQuasicoherent and IsFiniteType. This is not
   coherence. Correct.
3. x ∈ Supp(F_s) with s = f(x) ↔ `hx`: the stalk of `tensorPullback (f.fiberι (f x))` F at
   `f.asFiber x` is not subsingleton. Here `f.fiber (f x)` is `pullback f (S.fromSpecResidueField (f x))`,
   which is X ×_S Spec κ(s). `asFiber x` is the unique point of X_s over x (Mathlib Fiber.lean:116,
   with `fiberι_asFiber`). The `.presheaf.stalk` carrier is the def-weil-pbc-module-stalk carrier.
   Correct.
4. n = dim_x Supp(F_s) ↔ `topologicalKrullDimAt ⟨f.asFiber x, hx⟩` on the nonzero-stalk subspace
   of X_s. This is the def-kun-dimension declaration, the infimum over open neighbourhoods. Correct.
5. Affine open neighbourhoods u, v ↔ U, V existential with IsAffine and IsOpenImmersion.
   x ∈ im u is witnessed by `u (j (fiberι z)) = x`, and s ∈ im v by `sV`, `hv`. Correct.
6. p of finite type with fu = vp ↔ `LocallyOfFiniteType p ∧ QuasiCompact p ∧ u ≫ f = p ≫ v`.
   This is the recorded finite-type convention. Correct.
7. Z affine, j a closed immersion of finite presentation (lfp, qc, qs) ↔ all five conjuncts.
   Correct.
8. H finite-type quasi-coherent, and j_*H ≅ u^*F ↔ `H.IsQuasiCoherentFiniteType` and
   `Nonempty ((pushforward j).obj H ≅ (tensorPullback u).obj F)`. Mathlib's `Scheme.Modules.pushforward`
   has sections H(j⁻¹E), as the node's inline definition says. No DAG def node owns another
   declaration for it, and the landed 057Q dependency lem-trf-finite-type-sheaf-fp-support uses the
   same functor. Correct.
9. pj of finite type ↔ `LocallyOfFiniteType (j ≫ p) ∧ QuasiCompact (j ≫ p)`. Correct.
10. z ∈ Z_s, with Z_s formed over V at the point corresponding to s, and j(z) = x ↔
    `z : (j ≫ p).fiber sV` with `u (j ((j ≫ p).fiberι sV z)) = x`. Correct.
11. U_s ⊆ X_s ↔ `us`, pinned by both pullback projections. The second projection is
    `p.fiberToSpecResidueField sV ≫ Spec.map ((S.residueFieldCongr hv).inv ≫ v.residueFieldMap sV)`.
    The direction is κ(f x) → κ(v sV) → κ(sV), contravariant, which is right. The square commutes
    because fromSpecResidueField is natural. So us is the canonical map. It is an open immersion:
    since v is a monomorphism and κ(sV) ≅ κ(s), U_s ≅ U ×_X X_s. Correct.
12. j_s identifies |Z_s| homeomorphically with Supp((u^*F)_s) ↔ `js`, pinned by both projections,
    with `IsClosedImmersion js` (a closed embedding) and `Set.range js.base` equal to the
    nonzero-stalk locus of the iterated tensor pullback on U_s. Together these give a homeomorphism
    onto the support with no reduced structure imposed. Correct.
13. Supp((u^*F)_s) = Supp(F_s) ∩ U_s ↔ the `us.base ''` image equality inside X_s. Correct.
14. dim_z Z_s = n ↔ the `topologicalKrullDimAt` equality, using the same support subspace as
    clause 4. This is true: js and us are open/closed embeddings, so the dimension at a point is
    preserved under homeomorphism and under passing to the open subspace Supp(F_s) ∩ U_s. Correct.
15. u and v are étale, with residue-field isomorphisms at every point ↔ `Etale u ∧ Etale v` and
    `∀ y, IsIso (u.residueFieldMap y)`, `∀ t, IsIso (v.residueFieldMap t)`. Correct.

Edge cases checked:
- F = 0 or empty fibre support: hx fails, so the statement is vacuous, as in the source.
- Empty affine schemes are not excluded.
- Non-closed x, zero-dimensional support, and non-reduced Z are all allowed.
- Non-qc and non-qs X and S are allowed.
- A single universe u is used throughout, as the Modules and tensorPullback interfaces require.
  autoImplicit is off.

Searches: the worker's loogle, leanfinder and grep searches were re-read. No DAG def node records
`Scheme.Modules.pushforward`. The item is not landed in side-live. The item JSON differs from
side-live only in `lean`, and `lean.statement` is verbatim in the file.

Mismatches found: none in the mathematics. The only change is this section.
