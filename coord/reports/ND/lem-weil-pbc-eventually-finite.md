## Worker report

The new module `Sheaf.AlgebraicGeometry.EventuallyFinite` states
`AlgebraicGeometry.eventually_finite`, with `sorry` as its entire proof. No definitions,
new nodes, dependency modules, or statement corrections are needed. The original node is
unchanged except for its `lean` record. Its source is Stacks Project, Limits, Tag 09ZN,
label `lemma-eventually-finite`; I read the statement and proof in `limits.tex:914–953`.
The five numbered assumptions and eventual conclusion agree with the node.

Hypotheses and conclusion, clause by clause:

- The base scheme is `(S : Scheme.{u})`. Its quasi-compactness and quasi-separatedness
  are `[CompactSpace S] [QuasiSeparatedSpace S]`, using the underlying scheme space.
- The nonempty directed index set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. As in the recorded affine-limit statement,
  schemes and the index type share a universe, avoiding a separate smaller index
  universe. The arbitrary universe `u` places no fixed cardinal bound on the system.
  A preorder accommodates directed sets without adding an antisymmetry requirement.
- The inverse system is `(D : Iᵒᵖ ⥤ Scheme.{u})`. An arrow `op i ⟶ op j` represents
  `j ≤ i`, hence its map has the node's transition direction `X_i ⟶ X_j`.
- Finite transitions are `[∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsFinite (D.map g)]`.
  `IsFinite` extends `IsAffineHom`; affineness is therefore included, without an
  additional assumption.
- The stages' quasi-compactness and quasi-separatedness are
  `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
- The structure morphisms are the components of
  `(h : D ⟶ (Functor.const Iᵒᵖ).obj S)`. Naturality is exactly compatibility of
  transitions with the structure morphisms; thus this is an inverse system over S.
- Locally finite type structure maps are
  `[∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]`.
- The limit in schemes is `(c : Cone D) (_hc : IsLimit c)`; its underlying scheme
  is `c.pt`, and its projections are `c.π.app i`. This is the limit notion used in
  the recorded dependency `exists_limit_affine_transition`, without duplicating a
  chosen limit or imposing an extra existence assumption on the mathematics.
- The induced limit structure map is `(f : c.pt ⟶ S)` together with
  `(_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f)`. This explicitly identifies f with
  the induced map and does not permit an unrelated integral map.
- Integrality of this structure map is `[IsIntegralHom f]`.
- The complete conclusion is `∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsFinite (h.app (op i))`.
  It asserts finiteness at every stage in one upper tail, including i₀ itself.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 36–47 and 73–75.
- `def-weil-pbc-scheme-conventions` has a convention-only record, expressly defining
  no object. The relevant standard predicates are `CompactSpace`,
  `QuasiSeparatedSpace`, `LocallyOfFiniteType`, `IsAffineHom`, `IsFinite`,
  `IsIntegralHom`; there is no additional convention declaration to import.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`, lines 44–48, the affine-preimage
  condition; this is inherited by both finite and integral maps.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, lines 35–40, and
  `AlgebraicGeometry.IsIntegralHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`, lines 32–36. Both require affine
  preimages and the corresponding ring-map property on every affine open.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 39–46, as exposed by the
  imported finite-morphism module. This is the all-affine-pairs equivalent of the
  node's affine-cover condition. `QuasiCompact` there is a morphism predicate;
  compactness of the base and stages is correctly stated on their spaces.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition` in
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`. I read the full statement and
  its docstring, including the limit cone, affine projections, open restrictions,
  and affine-stage spectrum-of-colimit comparison. Its module is publicly imported.
  The present statement specifies an arbitrary limiting cone, as does the neighboring
  eventual-affineness statement, rather than selecting the existential witness.

Proof-only imports retain the existing plan for stage 3:
`Sheaf.AlgebraicGeometry.EventuallyAffine` (`AlgebraicGeometry.eventually_affine`),
`Mathlib.Algebra.Category.Ring.FilteredColimits` (filtered ring colimit preservation),
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
(`Concrete.isColimit_exists_rep`, `Concrete.isColimit_rep_eq_iff_exists`), and
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`
(`Algebra.finite_adjoin_of_finite_of_isIntegral`). The other proof nodes are Mathlib
leaves already exposed by the public imports: `locallyOfFiniteType_iff`,
`HasAffineProperty.iff_of_iSup_eq_top`, `IsZariskiLocalAtTarget.iff_of_iSup_eq_top`,
`IsZariskiLocalAtTarget.restrict`, and finite-composition instances in
`Mathlib.AlgebraicGeometry.Morphisms.Finite`. The declaration docstring carries all
seven proof steps, including image-algebra finiteness and the explicit product of
module generators. Nothing from this plan is proved in this delivery.

Edge cases checked: The base and stages may be empty; the finite affine cover may
have zero members, and nonemptiness of I still supplies an index. Zero rings and
empty lists of algebra generators cause no excluded case. A singleton index makes
this the usual locally finite type plus integral implies finite result. Noninjective
ring transition maps are permitted: the proof passes through their image, never
assumes injectivity. No Noetherian, separated, surjectivity, or nonempty-scheme
hypothesis is added. All binders and the universe are explicit. No disputed statement
or dependency fault was found.

Searches actually run via `msearch.py ND lem-weil-pbc-eventually-finite`:

- `leanfinder`, query `inverse system schemes finite transition integral limit locally
  finite type eventually finite`: 8 hits, including affine-limit factorization and
  affine-stage results, `LocallyOfFiniteType`, and finiteness of fibers; no theorem
  asserting eventual finiteness of the structure morphisms.
- `loogle`, query `AlgebraicGeometry.IsFinite, CategoryTheory.Limits.IsLimit`:
  0 hits.
- `leansearch`, query `inverse system schemes finite transitions integral limit
  eventually finite`: unavailable, Internal Server Error; not recorded as no match.
- `grep`, query `eventually.*finite|exists.*isFinite`, subdirectory
  `AlgebraicGeometry`: 2 hits in `ZariskisMainTheorem.lean`, concerning a finite
  restriction from a finite singleton preimage; neither concerns inverse systems.
- Direct `rg` of upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream
  name index for `eventually.?[Ff]inite|eventually_finite|lem-weil-pbc-eventually-finite|09ZN`:
  only upstream `AlgebraicGeometry.eventually_finite_image` in abelian-variety rigidity,
  a different statement about images of fibers. An additional exact-name search
  `eventually_finite` across Mathlib's algebraic geometry, upstream, and `lean/Sheaf`
  confirmed that the chosen declaration name is unused. A node-id grep of upstream
  likewise found no matching declaration.

Validation: the delivered file compiled cleanly through `scompile.py` on the server
in 1.3 seconds (nice 19, two threads, 60-second per-file limit). No local Lean compiler
or library build was run. The mandatory delivery dry run is the final mechanical check;
the independent second reading is intentionally left to the next worker.


## Second reading by ND

Independent second reader: read the node, its seven proof steps, the submitted module,
all six statement-dependency records and their declarations, Stacks `limits.tex`
Introduction and Lemma 09ZN with its proof. The source introduces no standing field,
Noetherian, characteristic or separatedness assumptions. No mismatch was found;
the Lean module and node record are retained unchanged.

Object/hypothesis/conclusion inventory and matching verdicts:

- Base scheme S: `(S : Scheme.{u})`; qcqs: `[CompactSpace S]
  [QuasiSeparatedSpace S]`. Exact. Mathlib compactness has no Hausdorff condition;
  quasi-separatedness means compact intersections of compact opens.
- Nonempty directed set I: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Exact Stacks directed-set convention;
  no antisymmetry or finite-index restriction is imposed.
- Inverse system of schemes: `(D : Iᵒᵖ ⥤ Scheme.{u})`. Exact: arrows from
  `op i` to `op j` encode j ≤ i, hence maps from X_i to X_j.
- System over S: `(h : D ⟶ (Functor.const Iᵒᵖ).obj S)`. Exact: components are
  structure maps, and naturality imposes precisely compatibility with transitions.
- Finite, hence affine, transitions: `[∀ {i j : Iᵒᵖ} (g : i ⟶ j),
  IsFinite (D.map g)]`. Exact: the recorded Mathlib `IsFinite` extends
  `IsAffineHom`, whose defining field requires affine inverse images of affine opens.
- Every stage qcqs: `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`. Exact.
- Every structure map locally of finite type:
  `[∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]`. Exact: the recorded class tests
  all affine pairs, equivalent to the affine-cover formulation in the node.
- Limit scheme X with projections: `(c : Cone D) (_hc : IsLimit c)` and `c.pt`.
  Exact: an arbitrary limiting cone expresses the node's given limit; the dependency
  `exists_limit_affine_transition` supplies its existence under affine transitions.
  I read that declaration's existence, projection, restricted-open and affine-comparison
  clauses; no replacement limit construction is introduced here.
- Induced structure map X → S: `(f : c.pt ⟶ S)` and
  `(_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f)`. Exact. This equality identifies
  the same induced map, rather than assuming integrality of an unrelated morphism.
- Integral limit structure map: `[IsIntegralHom f]`. Exact: the dependency's class
  means affine with integral ring maps on all affine target opens.
- Conclusion: `∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsFinite (h.app (op i))`.
  Exact order of quantifiers: one index works for every later stage, including itself.

Dependency audit: `Scheme`/`Scheme.Hom`, `IsAffineHom`, `IsFinite`, `IsIntegralHom`
and `LocallyOfFiniteType` are the recorded Mathlib notions, whose source signatures
were opened. The conventions node introduces no declaration of its own. The public
limit import and proof-only `EventuallyAffine` import use the recorded dependency
modules. No new definition node or dependency module occurs in this delivery, so
H12/H13 require no additional node. No statement correction or citer verdict is needed.

Edge cases: the empty index set is excluded by the source itself. Empty S and empty
stages remain allowed; over empty S all stages are empty and any index works. Zero
rings and zero algebra generators are allowed; the proof plan explicitly accommodates
the empty affine cover. For a singleton I the assertion reduces to integral plus
locally finite type implies finite. No characteristic, field, nonzero, injectivity,
Noetherian or extra separation restriction appears. There is no numerical n binder;
zero-length covers and lists cover its relevant n = 0 cases. Universe u is explicit
and arbitrary; index and scheme universe agree with the project's limit convention.
All variables are explicitly bound, with no independent small test universe.

Independent duplicate searches, using different wording from the worker:

- `msearch.py ... leanfinder "filtered family schemes finite bonding maps integral
  structural morphism of limit descends finiteness"`: eight hits. These include
  finite coproducts, finite implies integral, integral plus locally finite type iff
  finite, finite fibers, and affine-limit morphism equality descent. None states
  eventual finiteness for a directed inverse system.
- `msearch.py ... loogle "AlgebraicGeometry.IsIntegralHom,
  AlgebraicGeometry.IsFinite"`: three hits, the implication, iff and predicate
  equality for a single morphism. None is this inverse-system statement.
- Direct `rg` over Mathlib algebraic geometry, upstream `WeilConjectures` and
  project `lean/Sheaf`, with `finite.*[Cc]olimit|[Cc]olimit.*finite|09ZN`, and
  exact searches for `eventually_finite|eventuallyFinite|09ZN` over all upstream,
  project modules and the name index, found no duplicate. Opened the similarly
  named `AlgebraicGeometry.eventually_finite_image`: it concerns finite images of
  fibers in a topological neighbourhood, a different statement.

H5/H6/H8/H9: no definitions, hidden local objects, instances or notation are added;
the sole theorem has exactly `by sorry`. Both docstrings name Tag 09ZN and the
blueprint id. Its seven-step proof plan preserves the node's affine tail, finite
cover, colimit relations, image algebra, product module generators and uniform-tail
arguments. Imports retain the stated proof dependencies. Signature equality with
`lean.statement` was checked literally. No Lean or node repair was necessary;
this second-reading report is the only authored change.
