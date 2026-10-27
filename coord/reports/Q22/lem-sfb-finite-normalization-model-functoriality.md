## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteNormalizationModelFunctoriality` states
all clauses of `lem-sfb-finite-normalization-model-functoriality` as seven named
theorems, each with proof `sorry`. No definition, axiom, new node, dependency repair,
or statement correction is introduced. Only the item's `lean` record changes.
The declaration namespace is `AlgebraicGeometry.Scheme`. The main record names
`finite_normalization_model`; `lean.declarations` records all seven theorems.

Hypotheses and conclusions, clause by clause:

1. `finite_normalization_model`: `k : Type u`, `[Field k]`, `V : Scheme.{u}`,
   `[IsIntegral V]`, and `q : V ⟶ Spec (.of k)` introduce the field and integral
   scheme over it. `[LocallyOfFiniteType q] [QuasiCompact q]` mean finite type,
   using precisely the recorded two-part definition. `H` is the existing
   `V.functionField`, rather than a new carrier with an arbitrary identification.
   `M : Type u`, `[Field M]`, `[Algebra V.functionField M]`, and
   `[FiniteDimensional V.functionField M]` give the finite extension, including
   inseparable extensions. `N` is exactly `V.normalizationIn M`; its canonical map
   is `V.fromNormalizationIn M`. The first conjunct is `IsIntegral N`. The next
   gives `IsDomain (N.presheaf.stalk x)` and `IsIntegrallyClosed` of that stalk
   at every point, explicitly rendering normality as stated in the node. The
   two finite-type conjuncts concern the composite `V.fromNormalizationIn M ≫ q`.
   `IsFinite` and `Surjective` apply to the canonical normalization map.
   `IsNoetherian V ∧ IsNoetherian N` gives both Noetherian assertions: the Mathlib
   class means locally Noetherian and compact. The unique isomorphism
   `Spec M ≅ Spec N.functionField`, with its triangle through `N.fromSpecFunctionField`
   and the existing `toNormalization`, expresses the canonical identification
   of the function field with `M` by the affine spectrum correspondence. Finally,
   `IsSeparated q → IsSeparated (V.fromNormalizationIn M ≫ q)` retains the
   conditional separatedness clause; separatedness is not a blanket hypothesis.

2. `finite_normalization_model_restrict`: the same finite-model data are bound,
   followed by `U : V.Opens` and `[Nonempty U]`. The existential
   `a : Algebra U.toScheme.functionField M` is the restriction of the given field
   embedding to the canonically identical generic stalk of `U`. Its first
   triangle, `@fromSpecOfAlgebraFunctionField ... a ≫ U.ι =
   V.fromSpecOfAlgebraFunctionField M`, fixes this embedding, so `a` is not an
   arbitrary field structure. The source of `e` is the existing normalization
   of `U` in `M` with this algebra structure; the target is
   `pullback (V.fromNormalizationIn M) U.ι`, exactly `N_U`. The base triangle
   compares their maps to `U`, and the generic triangle compares their canonical
   maps from `Spec M` after projection to `N`. Existence and uniqueness of this
   compatible isomorphism give the canonical restriction identification. No
   assumption that intersections of affine opens are affine is imposed.

3. `finite_normalization_model_intermediate`: the same data and nonempty `U`
   are followed by `[Algebra U.toScheme.functionField M]` and `hU`, the same
   generic compatibility as in the restriction theorem. The preceding theorem
   supplies this structure for every nonempty open, so this interface does not
   restrict the opens in the assertion. `Z : Scheme`, `[IsIntegral Z]`, and `hZ`
   explicitly give a normal integral model, using both domain and integrally
   closed local-ring clauses. `p : Z ⟶ U.toScheme`, `[IsFinite p]`, and
   `[IsDominant p]` give the finite dominant map; Mathlib's latter class is dense
   image. `j : Z.functionField →+* M` is injective since its source is a field.
   `hj` says the generic composite to `V` agrees with its prescribed generic map
   from `M`. This is precisely the assertion that `j` fixes `H`: both composites
   induce the same map on the generic stalk of `V`. The existential map `f` has
   source `U.toScheme.normalizationIn M`, canonically `N_U` by the restriction
   theorem. Its first triangle makes it a `U`-morphism; the second fixes its
   generic-field embedding to be `j`; `IsFinite f` is the finiteness conclusion.
   The final universal quantifier gives uniqueness among *all* morphisms with
   those two triangles, without imposing finiteness on a competing `f'`.

4. `finite_normalization_model_semilinear`: independently binds two copies of
   all the field, integral-scheme, finite-type, and finite-extension data.
   `κ : k' ≃+* k` and `φ : M' ≃+* M` are in pullback direction, and `f : V ≅ V'`
   is the scheme isomorphism. `hk` is its semilinear structure-map square.
   `hM` is the generic square saying that `φ` extends the induced isomorphism
   on `H' → H`; it uses the fixed algebra embeddings into `M'` and `M`.
   The unique `F : V.normalizationIn M ≅ V'.normalizationIn M'` has both the
   base square over `f` and the generic square over `Spec φ`. Its base square
   together with `hk` also gives its prescribed semilinearity over `κ`.

5. `finite_normalization_model_identity`: binds the same finite-model data
   and a lift `F` of the identity scheme and field maps. `hV` and `hM` are
   exactly the base and generic identity triangles. The conclusion
   `F = Iso.refl (V.normalizationIn M)` states identity preservation.

6. `finite_normalization_model_composition`: binds three copies of the model
   data, two coefficient-field isomorphisms `κ, κ₂`, two scheme isomorphisms
   `f,g`, and two field isomorphisms `φ,ψ`, all with their two compatibility
   squares `hk₁,hk₂,hm₁,hm₂`. `F,G` are compatible lifts of the first two data;
   `H` is any compatible lift of their composite. `hF,hG,hH` are the base
   squares and `hFM,hGM,hHM` are the generic squares. The latter composite
   uses `φ.toRingHom.comp ψ.toRingHom`, the contravariant composite field map.
   The conclusion `F ≪≫ G = H` states preservation of composition even when
   the three coefficient fields differ. The semilinear theorem provides the
   lifts to which this characterization applies.

7. `finite_normalization_model_action`: keeps all the original model data
   and binds `G : Type v` with `[Group G]`; its universe is independent of
   the scheme universe. `κ : G →* (k ≃+* k)`, `ρ : G →* Aut V`, and
   `σ : G →* (M ≃+* M)` give the three compatible left actions. `hk,hM`
   state their coefficient and generic compatibility. Pullback uses
   `(κ g).symm` and `(σ g).symm`, as required for left actions and the
   contravariance of `Spec`. The unique monoid homomorphism
   `τ : G →* Aut (V.normalizationIn M)` with the two compatibility squares
   gives existence, the group laws, and uniqueness of the lifted action.
   There is no faithfulness, finite-group, trivial-coefficient-action,
   separability, or characteristic assumption.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`,
  `Mathlib.Algebra.Field.Defs`; `def-pc-field-extension`: `Algebra` and
  `algebraMap`, `Mathlib.Algebra.Algebra.Defs`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`. Its nonempty and domain-section
  definition supplies the integral schemes in all seven theorems.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; both are retained.
- `def-sc-function-field`: module
  `WeilConjectures.AlgebraicGeometry.FunctionField` is imported; its docstring
  explicitly points the arbitrary-integral-scheme clause to the existing
  Mathlib `Scheme.functionField` in `Mathlib.AlgebraicGeometry.FunctionField`.
  We use that clause, not the component-product construction for general curves.
- `def-fin-normalization-extension`: `Scheme.normalizationIn` and
  `Scheme.fromNormalizationIn` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`. The existing
  `fromSpecOfAlgebraFunctionField` and Mathlib `Scheme.Hom.toNormalization`
  supply the canonical generic maps. Their signatures and docstrings were read.
- `def-weil-finite-integral-morphism`: `IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; normalization itself is built
  using Mathlib's `IsIntegralHom` and relative normalization, with no copied
  definition. `def-weil-proper-morphism`: `IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, available through the
  explicitly imported recorded module `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-pc-fibre-product`: `pullback`, `pullback.fst`, `pullback.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.

The proof-dependency modules are imported with plain imports where not already
public statement dependencies. They expose integral-closure fraction fields,
localization of integral closure and normal domains, lying over, finite-algebra
integrality, the affine spectrum and local-ring constructions, finite-type
Noetherian and separated composition, finite locality, and morphism gluing.
In particular the existing finite-normalization theorem is
`Scheme.isFinite_fromNormalizationIn` in the same upstream normalization module.
Each postponed theorem has a source/blueprint docstring giving its relevant
steps of the node's proof. Together the seven docstrings cover all ten steps.

Edge cases checked before writing and reread after elaboration:

- The empty scheme is excluded by `IsIntegral`, exactly as in the node; an
  empty open is excluded only where the node says nonempty. `U = V` is allowed.
- A zero-dimensional `V = Spec k` and the degree-one extension are included;
  normality of `V`, regularity, positive dimension, or nontriviality of `M/H`
  are never assumed. Non-normal `V` with `M=H` is also included.
- Purely inseparable finite extensions and arbitrary characteristic remain
  included. Normality is asserted for `N`, without assuming it for `V`.
- No separatedness hypothesis is needed for normalization, restriction,
  intermediate models, or semilinear functoriality. The separated conclusion
  is explicitly conditional only in the geometry theorem.
- No affine intersection or quasi-compactness assumption on `U` is needed.
  In this finite-type situation `V` is Noetherian, so every open is in fact
  quasi-compact; the statement does not add this as a hypothesis.
- A trivial group, a nonfaithful action, infinite groups, group elements
  acting trivially on model and field, and moving constants are included.
  Scheme automorphism multiplication is geometric composition; the inverse
  field actions in the pullback squares respect this convention.
- The canonical open-field algebra and the restriction isomorphism are
  existential conclusions characterized by generic triangles; they are not
  assumed arbitrary maps or unspecified `Nonempty` choices.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder` with query “Normalization in a finite field
  extension is finite normal integral and functorial under compatible
  semilinear isomorphisms”: eight hits, including `AlgEquiv.liftNormal` and
  algebraic integral-closure Galois restriction; no scheme statement matching
  the node.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Scheme.normalizationIn, AlgebraicGeometry.Scheme.Hom.normalizationMap`:
  zero hits, unknown identifier `normalizationIn` in that index. The live source
  was searched and read directly; its `normalizationIn` is reused.
- `msearch.py ... grep` query `normalization(Map|Iso)|normalizationIn`,
  subdirectory `AlgebraicGeometry`: zero indexed Mathlib hits. Direct `rg`
  of Mathlib's `Normalization.lean` found the relative universal property,
  `normalizationDesc`, `normalization.hom_ext`, and `normalizationPullback`.
  They do not state the finite-model, intermediate, semilinear, and action clauses.
- `msearch.py ... leansearch` with query “Normalization of an integral finite
  type scheme in a finite field extension admits unique compatible semilinear
  isomorphisms”: eight hits, including `Scheme.Hom.normalization.hom_ext`
  and `normalizationDesc`; these support a future proof but are not the node.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `normalizationIn`, function-field maps,
  semilinear normalization, and finite-normalization model names found the
  upstream normalization definitions, its finiteness and generic-spectrum
  identification theorems, and normalization-cover/curve results. No complete
  matching statement or conflicting declaration name was found. Searching
  for this exact node id under `lean/WeilConjectures` returned no declaration.

The Stacks source was read locally in `literature/stacks-project/algebra.tex`,
labels corresponding to Tags 034L, 00GY, 0307 and 00GQ, with the tag mapping
checked in `literature/stacks-project/tags/tags`. The node's full affine proof
is the source of its additional synthesized semilinear and group clauses.
No statement fault or disputed clause was found.

Validation: every file is compiled through `scompile.py`; no local Lake or global
build is used. Initial syntax issues and a line-length warning were repaired.
The final corrected file compiled cleanly in both sandbox and library module
contexts. `deliver2.py Q22 lem-sfb-finite-normalization-model-functoriality
--no-push` printed OK: commit `8c59f80ac61` passes preflight and compiles; nothing
pushed. Its staged files were exactly this report, the item node, and its module.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
