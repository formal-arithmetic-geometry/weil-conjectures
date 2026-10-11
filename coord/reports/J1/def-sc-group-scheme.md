## Worker report

Existing declarations implement the whole definition. No Lean module is written and no theorem
is proved. The primary record is `CategoryTheory.GrpObj` in
`Mathlib.CategoryTheory.Monoidal.Grp`, with its signature copied verbatim, excluding `where`.
The component declarations are recorded in `lean.declarations`. In particular, the module
docstring of `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, lines 20–28, already names this
blueprint node and explicitly gives its group-scheme, commutative, homomorphism, kernel, finite,
order and étale conventions. The source's missing single `GroupScheme` alias is not a missing
notion: its established representation is `Over (Spec (.of k))` together with `GrpObj`.

Clause-by-clause reading (all the declarations below were opened, including their docstrings):

- “Let k be a field”: `(k : Type u) [Field k]`, for arbitrary universe `u`.
- “A k-scheme G”: `G : CategoryTheory.Over (AlgebraicGeometry.Spec (.of k))`.
  Its underlying scheme is `G.left` and its structure morphism is `G.hom`.
- Multiplication, inverse and identity with their diagrams: `[CategoryTheory.GrpObj G]`.
  The inherited `MonObj.mul : G ⊗ G ⟶ G` and `MonObj.one : 𝟙_ _ ⟶ G` and the
  field `GrpObj.inv : G ⟶ G` give these three maps. The cartesian monoidal product on the
  over-category is the fibre product over `Spec k`; the unit is `Spec k` over itself.
  `MonObj.mul_assoc`, `one_mul`, `mul_one`, `GrpObj.left_inv` and `right_inv` are exactly
  associativity, the two unit diagrams and the two inverse diagrams. Working in `Over`
  ensures all these morphisms are over k, as required, without introducing unrelated maps.
- Equivalent group-valued functor of points: `CategoryTheory.Hom.group` in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` gives `Group (X ⟶ G)` for every test object
  `X`. Take `X = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))` for a commutative
  k-algebra R. Conversely, that module's `GrpObj.ofRepresentableBy` recovers the group object
  from a represented presheaf of groups. No separate or arbitrary point-group data is used.
- Commutative: `[CategoryTheory.IsCommMonObj G]` in
  `Mathlib.CategoryTheory.Monoidal.Mon`; its `mul_comm` field is
  `(β_ G G).hom ≫ μ = μ`. In this cartesian category the braiding swaps the factors.
- Homomorphism: `f : G ⟶ H` with `[CategoryTheory.IsMonHom f]`, in the same module.
  `mul_hom` says `μ ≫ f = (f ⊗ₘ f) ≫ μ`. Its `one_hom` is not an additional mathematical
  restriction: a multiplication-preserving map between groups automatically preserves the
  identity (apply the induced map on each test object's points and cancel).
- Kernel: `CategoryTheory.GrpObj.ker f`, in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, is definitionally
  `pullback f η[H]`. Its `kerι` is `pullback.fst`. Forgetting from `Over` gives the displayed
  scheme fibre product `G ×_H Spec k`. The over-category has these pullbacks; the generic
  `HasPullback` binder excludes no group scheme in this specialization. The existing
  `AlgebraicGeometry.isClosedSubgroupScheme_kerι` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` supplies the forward pointer's
  closed-subgroup conclusion, and that module also supplies normality. No assumption of
  finite type, separatedness, commutativity or finiteness is added here.
- Finite: `[AlgebraicGeometry.IsFinite G.hom]` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`. This is affine with finite ring maps on affine
  opens, exactly the dependency's convention. Since `Spec k` is affine, a finite G is affine;
  its global sections are finite as a k-module. Thus the explanatory clause
  `G ≅ Spec Γ(G, ⊤)` with finite-dimensional coordinate algebra uses the existing affine
  spectrum equivalence, not another definition of finite group scheme.
- Order: `G.hom.finrankΓ`, defined in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. Its body is
  `letI := G.hom.ΓAlgebra; Module.finrank (.of k) Γ(G.left, ⊤)`.
  The `ΓAlgebra` is the algebra induced by the structure morphism, not an independently
  chosen k-action. For finite G this is exactly `dim_k Γ(G, 𝒪_G)`.
- Étale: `[AlgebraicGeometry.Etale G.hom]` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, exactly the dependency's étale convention.
- Finite étale algebra: `Module.Finite k A ∧ Algebra.Etale k A` for a commutative k-algebra A.
  `Algebra.Etale.iff_exists_algEquiv_prod` in `Mathlib.RingTheory.Etale.Field` identifies this
  with an algebra isomorphism to `Π j, L j`, where the index type is finite and every `L j`
  is a field, finite over k and separable over k. This is the stated product definition;
  it has no perfect-field hypothesis. The already existing bundled form is
  `AlgebraicGeometry.Scheme.FiniteEtale.FiniteEtaleAlgebra` in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`:
  `{A : CommAlgCat k // Module.Finite k A ∧ Algebra.Etale k A}`.
- The final equivalence for finite G: existing
  `AlgebraicGeometry.Scheme.Hom.etale_iff_etale_ΓAlgebra_of_isFinite` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` says, for `[IsFinite h]`,
  `Etale h ↔ letI := h.ΓAlgebra; Algebra.Etale k Γ(X, ⊤)`.
  With the preceding product characterization it gives exactly the stated criterion.
  Like kernel closedness, this is a forward reference to its own lemma, not a new theorem
  or proof introduced by this definition delivery.

Dependency used: `def-weil-pbc-scheme-conventions` has an `existing: true, convention: true`
record with null module and declaration. Its statement expressly fixes no notion of its own.
The record points to the component Mathlib declarations; its finite and étale components are
`AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Etale` in the modules given above. Their full
class signatures, defining affine-local conditions and docstrings were read. There is no
unusable dependency and no missing notion requiring a new node.

Edge cases checked before choosing this representation: the trivial group scheme `Spec k`
is allowed and has order one (`Scheme.Hom.finrankΓ_id` in FiberDegree); noncommutative and
nonfinite group schemes remain allowed; arbitrary characteristic and imperfect fields are
allowed; no smoothness or reducedness is assumed. An empty scheme over a field cannot carry
the required identity section, which is exactly right. The empty finite product of fields is
allowed in the finite-étale-algebra characterization (the zero algebra/empty finite étale
scheme); it is not artificially excluded by a nonempty index binder. All schemes and rings
can be instantiated in any universe u; the functor-of-points characterization uses test
algebras in that same universe, not a smaller independent universe. Order is used only under
the stated finiteness condition, so the convention `finrank = 0` for infinite-dimensional
modules causes no weakening.

Searches for existing notions:

- `msearch.py ... leansearch "group object in category of schemes over field group scheme"`:
  service unavailable (Internal Server Error), recorded in `searches.jsonl`; the other
  search services and source reading supplied the declarations.
- `msearch.py ... leanfinder "group scheme over a field group object multiplication inverse
  identity commutative kernel finite order finite etale algebra"`: eight hits, including
  `AlgebraicGeometry.Scheme.GrpObjAsOverPullback`; no single composite alias.
- `msearch.py ... loogle "CategoryTheory.GrpObj, AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.Etale"`: zero hits. This multi-name query does not mean the components
  are absent; their source declarations were located and read directly.
- `msearch.py ... grep "GrpObj|IsFinite|Etale" AlgebraicGeometry/Group`: fifteen hits,
  including group objects over fields, commutative group objects and affine Hopf algebras.
- `rg` in Mathlib located `GrpObj`, `MonObj`, `IsCommMonObj`, `IsMonHom`, `Hom.group`,
  `IsFinite`, `Etale` and the finite separable product characterization, in the modules above.
- `rg` in `WeilConjectures` for group-scheme and finite-étale declarations located the
  existing kernel, order, finite étale algebra and the entire terminology documentation in
  `GroupScheme/Defs.lean`. The required search for `def-sc-group-scheme` specifically finds
  that documentation and the subgroup/translation references; it is not a declaration tag
  on a new `GroupScheme` definition.
- `rg` in `lean/Sheaf` found constant group schemes and their points, not a second general
  group-scheme definition. `dag/lean_names_upstream.json` has no exact definition-node
  attachment for this composite terminology; it does list the existing kernel declaration
  for the torsion nodes. The source documentation and actual declarations supply the match.

No statement correction, disputed statement, new node, dependency module or private copy is
needed. Every recorded component is an existing declaration. The primary generic declaration
is specialized to the exact category in the node; its generality does not force a replacement
because `Over (Spec (.of k))` has the required cartesian monoidal structure.

## Second reading by J1

I opened the node statement (source: `def-sc-group-scheme.md`, node order 422) and the
recorded declarations. The item-by-item rendering is:

- The field is `(k : Type u) [Field k]`; no characteristic, perfection, or finiteness
  hypothesis is added.
- A k-scheme is `G : Over (Spec (.of k))`, so `G.left` is the scheme and `G.hom` its
  structure map. The over-category is the required category of schemes over k.
- The group operations and all associativity, unit, and inverse diagrams are the
  `CategoryTheory.GrpObj G` fields (`MonObj.mul`, `MonObj.one`, `GrpObj.inv` and their
  laws). This includes the empty-scheme edge case correctly: an identity section is still
  required, so an empty object cannot satisfy the group-object instance.
- The functor-of-points clause is rendered by `CategoryTheory.Hom.group`, specialized to
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))` for each commutative k-algebra R.
- Commutativity is `[IsCommMonObj G]`, whose `mul_comm` is multiplication after the
  cartesian braiding. A homomorphism is `f : G ⟶ H` with `[IsMonHom f]`.
- The kernel is `GrpObj.ker f` with inclusion `GrpObj.kerι f`; its underlying pullback is
  `G ×_H Spec k`. The existing `isClosedSubgroupScheme_kerι` supplies the stated closed
  subgroup fact, without adding it as a hypothesis.
- Finiteness is `[AlgebraicGeometry.IsFinite G.hom]`; the order is
  `G.hom.finrankΓ`, i.e. the k-dimension of `Γ(G, O_G)` under the induced algebra. No
  finite-type, separatedness, or commutativity assumption is introduced.
- Étaleness is `[AlgebraicGeometry.Etale G.hom]`. The finite étale algebra clause is the
  existing `Algebra.Etale.iff_exists_algEquiv_prod` characterization (also recorded by
  `Scheme.FiniteEtale.FiniteEtaleAlgebra`), allowing the empty finite product/zero algebra.
  The final finite-scheme equivalence is exactly
  `Scheme.Hom.etale_iff_etale_ΓAlgebra_of_isFinite`.

Universes remain arbitrary and aligned (`R : Type u` in the point specialization); n = 0
and characteristic-zero/positive cases are irrelevant to this definition and are not
excluded. `Spec k` is the trivial group scheme and has order one. I found no mismatch
between the node clauses and the recorded existing declarations, so no Lean module or
statement correction was needed. The worker's existing-declaration record was retained,
with `CategoryTheory.GrpObj` as the primary declaration and the component declarations
listed in `lean.declarations`.

The searches were independently checked: Mathlib contains `CategoryTheory.GrpObj`,
`IsCommMonObj`, `IsMonHom`, `IsFinite`, `Etale`, `GrpObj.ker`, and `finrankΓ`; the source
`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents this exact representation
and contains the kernel and finite-étale criterion. No composite `GroupScheme` alias or
class exists in Mathlib, the source repository, or `lean/Sheaf`, so recording the existing
component representation avoids a second definition. No mismatch was found or changed.
