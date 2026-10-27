## Worker report

The module `Sheaf.RingTheory.HenselianResidueLiftDiagram` states all clauses of
`lem-wf-henselian-residue-lift-diagram` in four named theorems. Each proof is
`sorry`; there are no definitions, choices of unspecified algebra data, instances,
or helper proof obligations. Only the item's `lean` record changes.

Source read: `algebra.tex`, Tag 04GK (`lemma-henselian-cat-finite-etale`,
lines 42450 onward), and Tag 0BSL (`remark-construct-sh-from-h`, lines 43156
onward); `fields.tex`, Tags 09DT (`lemma-normal-closure`, lines 2086 onward),
0BMG (`lemma-normal-closure-inside-normal`, lines 2134 onward), and 0EXM
(`lemma-normal-closure-galois`, lines 2704 onward). The latest blueprint
`sec-purity-real-sheaves/sk-i-real-boundary/lem-wf-boundary-stalk-invariants.md`
was read to check the ancestor's intended finite-level construction. The node's
seven proof steps are explained across the four declaration docstrings.

Hypotheses and clauses, matched against the original node:

| Node text | Lean rendering |
| --- | --- |
| Commutative henselian local ring `(H,m,k)` | `(H : Type u) [CommRing H] [HenselianLocalRing H]`; locality is a superclass, `m = IsLocalRing.maximalIdeal H`, `k = IsLocalRing.ResidueField H`. |
| Chosen separable closure `K/k` | `[Field K] [Algebra (IsLocalRing.ResidueField H) K] [IsSepClosure (IsLocalRing.ResidueField H) K]` in all four declarations. |
| Finite separable intermediate fields, ordered by inclusion | Subtype `{e : IntermediateField k K // FiniteDimensional k e}` with its inherited partial order/category. Separability is automatic from `IsSepClosure`, not an omitted condition; every such field is separable. |
| Small index | This subtype is `Type u`, with Mathlib's small category instance for a preorder; no additional smallness assumption or tautological conclusion is inserted. |
| Finite commutative etale `H`-algebras `B_e` | `D : I ⥤ CommAlgCat.{u} H`, `∀ e, Module.Finite H (D.obj e)` and `∀ e, Algebra.Etale H (D.obj e)` in `exists_henselian_residue_lift_diagram`. |
| Specified `k`-algebra isomorphisms `B_e/mB_e ≃ e` | `q : ∀ e, D.obj e →+* e.val`, surjectivity, kernel exactly `m.map (algebraMap H _)`, and `q e (algebraMap H _ h) = algebraMap k e.val (IsLocalRing.residue H h)`. These conditions are exactly quotient isomorphisms respecting the specified `k` structure, not arbitrary maps or unidentified residue extensions. |
| Each `B_e` local with maximal ideal `mB_e` | `∃ loc : ∀ e, IsLocalRing (D.obj e)`, followed by the equality of the maximal ideal for that explicit instance with the mapped ideal. |
| Structural maps local | `∀ e, IsLocalHom (algebraMap H (D.obj e))`. |
| One residue-compatible map for every inclusion | For `t : e ⟶ f`, `D.map t` exists and satisfies the equation in `K`; `map_unique` is written inline as `∀ g, (∀ b, ...) → g = (D.map t).hom`. This quantifies over all algebra maps, without assuming locality. Equality in `K` is equivalent to equality after the field inclusion, since intermediate field embeddings are injective. |
| These maps local | `∀ {e f} (t : e ⟶ f), IsLocalHom (D.map t).hom.toRingHom`. |
| Identity and composition | The `Functor` data includes `map_id` and `map_comp`, exactly the two coherence identities. |
| Any two lifts of an identified field have exactly one compatible isomorphism | `henselian_residue_lift_unique` quantifies over arbitrary finite etale `B,C` and both quotient identifications, concluding `∃! i : B ≃ₐ[H] C, ∀ b, qC (i b) = qB b`. No extra local-ring hypothesis on `B,C` is assumed. |
| `I` directed; Galois full subposet `J` directed and cofinal | `henselian_residue_lift_galois_cofinal`: `IsFiltered I`, `IsFiltered (ObjectProperty.FullSubcategory ...)`, and every `e` has a normal finite overfield `f` inside the fixed `K`. On a poset `IsFiltered` includes nonemptiness and is directedness. `Normal k e.val`, together with the inherited separability, is exactly Galois, including the specified minimal-polynomial splitting meaning. |
| For any chosen lift diagram and any commutative `H`-algebra `T`, cocone restriction is bijective | `henselian_residue_lift_galois_cocones` quantifies over `D,q` with finite etale fibre identifications and compatible arrows. Locality and uniqueness need not be separate hypotheses: they follow from these data by the preceding assertions. Its conclusion quantifies over every `T : CommAlgCat H` and states `Function.Bijective` for `Functor.whiskerLeft (ObjectProperty.ι ...)` on natural transformations from `D` to the constant diagram at `T`. These are exactly cocones with the fixed vertex `T`, not cocones with varying vertices. |
| Canonically the same colimit, preserving `H` structure | Existence of `c : Cocone D` with `Nonempty (IsColimit c)` and its Galois restriction also a colimit; every restricted colimit `c'` has exactly one `i : c'.pt ≅ c.pt` satisfying `c'.ι.app g ≫ i.hom = c.ι.app g.obj`. An isomorphism in `CommAlgCat H` preserves the structural map. |
| Compatible residue maps to `K` preserved | `ρ : c.pt →+* K` has `ρ ((c.ι.app e).hom b) = (q e b : K)`. Every map `ρ'` from `c'.pt` agreeing with the restricted residue legs satisfies `ρ.comp i.hom.hom.toRingHom = ρ'`. The scalar equation on the stages also forces the induced residue map's structural compatibility. |

All rings, fields, index objects and diagram algebras live in an explicitly
bound common universe `u`, arbitrary and not fixed to `0`. The indexing type is
in the same universe as the algebras, matching the project's colimit convention.
There are no auto-bound implicit variables or file-local notation/instances.
The four declarations collectively state the node: the primary record points
to lift existence and `lean.declarations` lists all four clause declarations.

Dependency declarations used/read:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: `HenselianLocalRing`
  (Mathlib class, root lifting; upstream docstring identifies the node's henselian
  terminology); the strictly henselian class is not needed here.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, whose body is
  the standard `IsLocalRing.ResidueField` of a local ring. Here the local ring is
  given directly, so the same Mathlib residue quotient is used directly.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, and Mathlib's `IsSepClosure`
  (separably closed and separable/algebraic), used for the specified closure.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, defined
  affine-locally by the ring-map property; the algebras here use its ring form
  `Algebra.Etale`. No alternative etale notion is introduced.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`
  and the generated colimit interface; the statement uses universal colimit
  cocones rather than an arbitrary ring isomorphism.
- Proof imports: `Sheaf.RingTheory.HenselianFiniteEtaleFieldLift`,
  `CommAlgCat.FiniteEtale.exists_finiteEtale_residueField_equiv_of_finite_separable`;
  `Sheaf.RingTheory.HenselianFiniteEtaleMapBijective`,
  `CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`;
  `Mathlib.RingTheory.Ideal.GoingUp`,
  `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`.
- Remaining Mathlib proof dependencies are available through the public imports:
  `IsSepClosure.isGalois`, `FiniteGaloisIntermediateField.adjoin` and
  `subset_adjoin` in `Mathlib.FieldTheory.Galois.GaloisClosure`, and the
  `HasColimits (CommAlgCat R)` instance in
  `Mathlib.Algebra.Category.CommAlgCat.Basic`.

Edge cases checked before writing: the trivial intermediate field is included
(`⊥`, degree one), including when the residue field is already separably closed;
therefore neither index is empty. The local-ring hypothesis excludes the zero
base ring, and each surjective quotient to a field excludes a zero lift. The
vertex `T` of a cocone may be the zero algebra; it is not excluded. Imperfect
residue fields are allowed: there is no perfect-field or algebraically closed
hypothesis. `Normal` inside a separable closure gives exactly the Galois objects,
without including purely inseparable fields. The reduction identity is required
in the specified closure, not in an independently chosen abstract extension.
Uniqueness quantifies over arbitrary compatible algebra maps, so nonlocal
competitors are not silently discarded. The final isomorphism is characterized
by its legs and residue equation, not an unconstrained isomorphism.

Searches actually run with `batch2/msearch.py`, group Q30 and this item:

- LeanFinder: `Finite separable residue extensions of a henselian local ring admit a coherent finite etale lift diagram with unique compatible maps and cofinal Galois restriction preserving cocones.` Result: eight hits, including `HenselianLocalRing.TFAE`, prescribed-residue-field etale algebra construction, unramified local-ring residue results and `Algebra.Etale.iff_exists_algEquiv_prod`. None states this coherent diagram and its cocone restriction.
- Loogle: `HenselianLocalRing, Algebra.Etale`. Result: zero hits.
- LeanSearch: `Finite etale lifts of residue field extensions over a henselian local ring form a directed diagram with cofinal finite Galois subfields.` Result: eight hits, including `HenselianLocalRing.TFAE`, `HenselianLocalRing`, `Field.henselian` and residue-field lift results. No exact statement.
- Mathlib grep: `henselian.*etale|etale.*henselian|finite.*galois.*colimit`. Result: zero hits.
- Local `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id and for `henselian.*[Dd]iagram|residueLift|[Ff]inite[Ss]eparable[Ii]ntermediate|Galois.*[Cc]ofinal`, plus the upstream name index. No exact existing statement. `StrictHenselizationFiniteLifts.lean` has related bundled data and a larger theorem. That is a downstream consumer of this node; importing it here would close a dependency cycle. The present statement introduces no second definition or replacement structure: the index is just a subtype of Mathlib intermediate fields, and the diagram is Mathlib's functor.
- Local `rg` of all four proposed full declaration names in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  zero collisions.

Server validation: `scompile.py Q30 lem-wf-henselian-residue-lift-diagram
.../HenselianResidueLiftDiagram.lean` passed both sandbox and library-module
compilation with no errors or warnings. The first compile identified the
qualified namespace `Functor.whiskerLeft` and the need for explicit subtype
annotations on the Galois predicate; both were repaired before this successful
compile. No statement correction, dependency repair, new node or disputed
mathematical assertion is needed.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
