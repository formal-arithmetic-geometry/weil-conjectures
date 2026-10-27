## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricNodeResidueRationalization` states
`AlgebraicGeometry.geometric_node_residue_rationalization`. Its sole theorem has
proof `sorry`; the docstring supplies all seven proof steps of the DAG node.
There are no new definitions, dependency repairs, or changes to the node's
statement or dependencies. Only its `lean` record changes.

The source was read at `literature/stacks-project/curves.tex`,
`lemma-etale-local-structure-nodal-family` (Tag 0CBY), first proof's residue-field
paragraph, and `lemma-nodal-family` (Tag 0C59), together with
`literature/stacks-project/morphisms.tex`, `lemma-unramified-over-field` (Tag 02G7).
The latter explains the finite separable residue extension; the two projections
of a fibre product specify the residue-field rationalization canonically.

Hypotheses, individually:

- The base is an arbitrary field: `{k : Type u} [Field k]`.
- The finite type k-scheme is `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`
  with `[LocallyOfFiniteType f] [QuasiCompact f]`. These are precisely the two
  parts of finite type in the recorded dependency, not an added separatedness
  or integrality assumption.
- Every algebraically closed extension is quantified in `hgeom` as
  `∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]`.
  No algebraicity condition is imposed here. The base change is the actual
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))`.
- Empty or pure dimension one is `(...).IsPureDimension 1`. The dependency
  defines pure dimension by all irreducible components; it holds for the empty
  scheme as well, so the disjunction with emptiness is equivalent to this form.
- Every nonsmooth geometric point is quantified as `∀ y` of that base change,
  with premise `y ∉ (pullback.snd ...).smoothLocus`.
- Its completed local ring is the actual `AdicCompletion` at
  `IsLocalRing.maximalIdeal` of the scheme's `presheaf.stalk y`.
  `Nonempty (... ≃+* (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}))`
  states exactly the specified ring isomorphism with Ω[[u,v]]/(uv).
- The original point and nonsmoothness are `(x : C) (hx : x ∉ f.smoothLocus)`.
  Local finite presentation needed by smooth loci is synthesized from finite
  type over the Noetherian field, using Mathlib's existing Noetherian instance;
  it is not a new hypothesis.

Conclusions, individually:

- Closedness is `x ∈ closedPoints C`.
- F is literally `C.residueField x`. Its structural embedding is
  `f.residueFieldAlgebraMap x`, not an arbitrary k-algebra structure.
- F/k finite is `(f.residueFieldAlgebraMap x).Finite`. Over fields this means
  finite vector-space dimension.
- F/k separable algebraic is `@Algebra.IsSeparable k (C.residueField x) _ _
  (f.residueFieldAlgebraMap x).toAlgebra`. This existing predicate includes
  algebraicity, as its Mathlib docstring explains.
- D is the actual `pullback f (Spec.map (CommRingCat.ofHom
  (f.residueFieldAlgebraMap x)))`; its structural map is `pullback.snd`.
- The existential `z : Spec (C.residueField x) ⟶ D` has the two equations
  `z ≫ pullback.fst ... = C.fromSpecResidueField x` and
  `z ≫ pullback.snd ... = 𝟙 (Spec (C.residueField x))`.
  The fibre-product universal property determines this map uniquely. This
  existential asserts the canonical construction, rather than admitting an
  unconstrained map or assuming its existence as extra data.
- D finite type over F is the displayed conjunction `LocallyOfFiniteType
  (pullback.snd ...) ∧ QuasiCompact (pullback.snd ...)`.
- D topological dimension one is `topologicalKrullDim D = 1`.
- The underlying point of z is `z (IsLocalRing.closedPoint (C.residueField x))`.
  Its closedness is membership in `closedPoints D`, and lying over x is the
  explicitly displayed equality under `pullback.fst`.
- F-rationality is `Function.Bijective ((pullback.snd ...).
  residueFieldAlgebraMap (z (IsLocalRing.closedPoint ...)))`. A bijective ring
  homomorphism is an isomorphism, and the map is exactly the structural map.
- Every algebraic closure is quantified with `[Algebra (C.residueField x) Ω]`
  and `[IsAlgClosure (C.residueField x) Ω]` (not only a fixed implementation).
  The iterated pullback is literally D_Ω. `zbar` is its point with first
  projection equal to the underlying point of z.
- Rationality identifies the fibre over z with Spec Ω, so this fibre has
  exactly one point. Thus the universal assertion over `zbar` with that first
  projection is equivalent to the property of the induced geometric point;
  it adds no geometric assumption. Its existence follows by base changing
  the section z, using the identity second-projection equation. The section
  is the existing `sectionBaseChange` construction of `def-pc-base-change`.
- This point is nonsmooth by `zbar ∉ (pullback.snd ...).smoothLocus`.
  The final `Nonempty (AdicCompletion ... ≃+* (... ⧸ Ideal.span {X 0 * X 1}))`
  uses its actual stalk, maximal ideal and coefficient field Ω. There is no
  algebra compatibility condition on that ring isomorphism.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its quasi-compact companion is
  `AlgebraicGeometry.QuasiCompact` from `Morphisms.QuasiCompact`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`.
  The algebraic-closure dependency's `mathlib_match` explicitly names both.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: scheme base
  change is Mathlib `CategoryTheory.Limits.pullback` with `pullback.fst` and
  `pullback.snd`, as the recorded declaration's module docstring and note
  specify; the module-only `moduleBaseChange` is not mistaken for scheme
  base change. The module also records induced sections.
- `Sheaf.AlgebraicGeometry.PureDimension`:
  `AlgebraicGeometry.Scheme.IsPureDimension`, read in full.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, `Scheme.Hom.smoothLocus` and its membership
  characterization. The latter is the canonical pointwise smooth locus.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`:
  `AdicCompletion` and its commutative ring instance.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.
- `Mathlib.AlgebraicGeometry.ResidueField`:
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  `Scheme.fromSpecResidueField`; `WeilConjectures.ZetaSeries`:
  `Scheme.Hom.residueFieldAlgebraMap`, the structural embedding used here.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, for the field extension structures.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.

All recorded proof-dependency modules are also imported (plain imports when
needed only for the future proof): `FirstFittingSingularSubscheme`,
`NodalFamilyFittingSingular`, `UnramifiedOverFieldLocalCriterion`,
`WeilConjectures.AlgebraicGeometry.DimensionBaseChange`,
`DimensionAffineOpenCover`, `Dimension`, and the Mathlib modules for flatness,
finite presentation, closed immersions, affine pullbacks, irreducible-component
covering and finite presentation of finite type Noetherian algebras. Finite type
composition and base change are in the public finite type import (with the
quasi-compact companion). No proof import creates an import cycle.

Edge cases checked before finalizing:

- Empty C and geometrically empty base changes are allowed: the purity condition
  is vacuous; no x exists on empty C, so its conclusion is never spuriously used.
- Smooth curves satisfy the geometric assumptions but supply no nonsmooth x.
- Reducible or disconnected geometrically nodal curves are included; there is
  no integrality or connectedness hypothesis.
- Nonseparated finite type schemes are included; neither the declaration nor
  its proof plan uses separatedness.
- Imperfect ground fields and characteristic two are included; the field
  extension is the structural extension, and the uv equation is used unchanged.
- F = k and any chosen algebraic closure structure on Ω are included.
- Completion comparisons are ring isomorphisms, not the stronger coefficient
  algebra isomorphisms. Stalks are taken on the correct iterated base change.
- Every variable and the universe u are explicitly bound with `autoImplicit false`.
  Field and scheme sizes use the common ambient scheme universe. Algebraic
  closures exist in that universe; there is no smaller independently quantified
  test universe making a condition vacuous.

Searches (2026-10-24, using the prescribed msearch.py wrapper):

1. LeanFinder: "A nonsmooth point of a geometrically nodal finite type curve
   has finite separable residue field and becomes a rational geometric node
   after base change to its residue field". Eight hits: unramified residue-field
   separability/finiteness, residue-field construction, and Weierstrass-specific
   results. None states this theorem or its full geometric conclusion.
2. Loogle: "AlgebraicGeometry.Scheme.fromSpecResidueField,
   AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap". Zero hits; Loogle's
   Mathlib index does not know the upstream residueFieldAlgebraMap declaration.
   It was instead found and read directly in WeilConjectures.ZetaSeries.
3. Mathlib grep: "residueFieldAlgebraMap|fromSpecResidueField|residue.*[Ll]ift"
   restricted to AlgebraicGeometry. Twenty-five reported hits, notably
   `Scheme.fromSpecResidueField`, `Scheme.Hom.asFiberHom`, and the residue-field
   maps. None states the node's theorem.
4. LeanSearch: "Every nonsmooth point of a geometrically nodal curve has finite
   separable residue field and is rational after base change to its residue
   field". Eight hits: residue-field definitions, unramified separability,
   Weierstrass nonsingularity under base change, and separability of quotients.
   None supplies the rationalization theorem with dimension and completions.
5. Local rg over `lean/WeilConjectures` and `lean/Sheaf` for
   `residue.*[Ll]ift|geometric_node_residue|GeometricNodeResidue|` followed by the
   node id: no complete statement; neighbouring rational and separable node
   quadratic-completion lemmas assume the desired residue hypotheses instead.
   The exact node-id search in WeilConjectures returned no hits. The upstream
   name index was also searched for geometric-node/residue names.

No STATEMENT-DISPUTED flag or source fault was found.

## Second reading by Q60

Independent second reading (maintainer reviewer; the delivered section was a
same-worker self-check, H11). Node read against Stacks Curves 0CBY (first proof,
residue-field paragraph), 0C59, 0C5B and Morphisms 02G7; every stmt_dep record
opened. Item by item:

Hypotheses.
1. k a field — `{k : Type u} [Field k]`. Exact.
2. C finite type over k (def-weil-finite-type-morphism = LocallyOfFiniteType ∧
   QuasiCompact) — `f : C ⟶ Spec (.of k)` with both instances. Exact; no
   separatedness/integrality added.
3. ∀ algebraically closed Ω/k (def-weil-algebraic-closure: IsAlgClosed) —
   `∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]`. Ω : Type u is forced
   by `Spec` on `Scheme.{u}`; restricting the hypothesis to that universe only
   weakens it, and the proof uses it only at Ω = F̄ : Type u.
4. C_Ω (def-pc-base-change: `pullback f (Spec.map …)`, pr = `pullback.snd`)
   empty or pure dimension 1 — `IsPureDimension 1` (Sheaf.PureDimension: every
   irreducible component has topologicalKrullDim 1; vacuous for ∅). Equivalent
   to the disjunction.
5. Every nonsmooth point (def-sbc-smooth-morphisms; Mathlib `smoothLocus` =
   formally smooth stalk map, = smooth-at under lfp, lfp synthesized from finite
   type over a Noetherian field) has completion Ω[[u,v]]/(uv) as a ring
   (AdicCompletion of maximalIdeal of the stalk; MvPowerSeries (Fin 2) Ω ⧸ (X0·X1))
   — `Nonempty (… ≃+* …)`. Exact, no coefficient-field compatibility.
6. x nonsmooth — `hx : x ∉ f.smoothLocus`. Exact.

Conclusions.
7. x closed — `x ∈ closedPoints C` (def-weil-closed-points mathlib_match). Exact.
8. F/k finite separable with the structural map — `(f.residueFieldAlgebraMap x)
   .Finite ∧ Algebra.IsSeparable` for that algebra. residueFieldAlgebraMap is the
   STATE "RESIDUE FIELD" convention for k → κ(x) under def-weil-residue-field
   (= Spec.residueFieldIso⁻¹ ≫ residueFieldMap), as the landed sibling
   lem-trf-unramified-over-field-local-criterion uses. Exact.
9. D = C_F and z with pr_C ∘ z = residue point, pr_F ∘ z = id — `∃ z` with both
   projection equations, which pin z uniquely (pullback.hom_ext). Exact.
10. D finite type over F — LocallyOfFiniteType ∧ QuasiCompact of `pullback.snd`.
11. dim D = 1 — `topologicalKrullDim D = 1` (def-kun record). Exact.
12. z closed, over x — membership in `closedPoints D` and `pullback.fst (z pt) = x`.
13. F-rational — `Function.Bijective` of the structural map F → κ_D(z)
    (`(pullback.snd …).residueFieldAlgebraMap`). Bijective ring hom = iso. Exact.
14. ∀ algebraic closure F̄ (`[Algebra F Ω] [IsAlgClosure F Ω]`, Ω : Type u forced),
    the induced point z̄ ∈ D_F̄ is nonsmooth with completion F̄[[u,v]]/(uv):
    rendered as ∀ zbar ∈ D_Ω with pr_D zbar = z. Since κ_D(z) = F, the fibre of
    D_Ω → D over z is Spec(F ⊗_F Ω), one point, which is the induced point; the
    ∀-form is therefore equivalent (nonvacuous). Nonsmoothness is relative to
    D_Ω → Spec Ω; completion on the stalk of the iterated pullback D_Ω. Exact.

Edge cases: C = ∅ or geometrically empty (purity vacuous, no x); smooth C (no x);
F = k (split node, z = x); nonsplit node over imperfect k / char 2 (uv unchanged,
separability from the conclusion not assumed); reducible, disconnected,
nonseparated C (no such hypotheses). Universes: everything in u, forced by
Scheme.{u}; no hidden universe restriction.

Records: node json differs from live only by its new `lean` record; the
`lean.statement` is verbatim the file signature. Proof `sorry`, no definitions;
module docstring and theorem docstring carry the source place,
`(blueprint: lem-trf-geometric-node-residue-rationalization)` and all seven
proof steps. All imported modules exist on live. Searches: no live declaration
of this name/module; the worker's LeanFinder/Loogle/LeanSearch/grep hits give
only local residue/unramified facts.

Changed: only this report section (H11). Lean module and node record accepted
as delivered.
