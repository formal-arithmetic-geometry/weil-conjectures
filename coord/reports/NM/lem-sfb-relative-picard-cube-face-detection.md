## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePicardCubeFaceDetection` states
`AlgebraicGeometry.relative_picard_cube_face_detection`, with precisely one postponed
theorem proof (`sorry`). It also constructs the canonical helper
`AlgebraicGeometry.groupIdentityFace` by the product universal property. The helper's data
are fully written; there is no choice of an arbitrary map or postponed construction.

This is stage 2, not a new split. The inherited BLOCKED ending concerns stage-1 resplitting.
The maintenance handoff in brief-stage2 section 0 explicitly authorizes recording Lean on
a reviewed split. The live item has Q23's accepted split and no Lean record; there is no
repair note for the item. The natural-language statement, proof, proof dependencies, and
all review fields are preserved. Only `lean` and the authorized addition of three existing,
landed definition dependencies change. There is no statement correction or disputed
statement flag.

### Every hypothesis and clause

| Node text | Lean rendering and meaning |
| --- | --- |
| S is any scheme | `{S : Scheme.{u}}`, with the universe explicitly declared. No connectedness, nonemptiness, Noetherianity, reducedness or normality is imposed on the proper branch. |
| Three schemes p_i : G_i → S | `G : Fin 3 → Over S`; `(G i).left` is G_i and `(G i).hom` is p_i. Fin 3 relabels 1,2,3 as 0,1,2 without excluding any triple. |
| Addition, inverse and identity are S-morphisms satisfying the commutative group identities | `[∀ i : Fin 3, CommGrpObj (G i)]`, using the existing Cartesian group-object API in the category `Over S`. The identity morphism is the group object's `η`; the unit `1` in a morphism set is its composite with the structure map. |
| Each p_i is smooth | `[∀ i : Fin 3, Smooth (G i).hom]`. This is Mathlib's affine-local smooth-ring definition recorded by the dependency node. |
| Each p_i is separated, meaning its diagonal is a closed immersion | `[∀ i : Fin 3, IsSeparated (G i).hom]`. Mathlib's defining field is `isClosedImmersion_diagonal`. |
| Each p_i is of finite presentation | `[∀ i : Fin 3, LocallyOfFinitePresentation (G i).hom]` and `[∀ i : Fin 3, QuasiCompact (G i).hom]`; quasi-separatedness follows from the already required separatedness. Thus this is finite presentation, not just local finite presentation. |
| Each p_i has geometrically connected fibres | `[∀ i : Fin 3, GeometricallyConnected (G i).hom]`. |
| Either all three structure maps are proper | The first disjunct of `hbase` is `(∀ i : Fin 3, IsProper (G i).hom)`. The disjunction applies to the whole family, not independently to different factors. |
| Or S is normal and every geometric fibre is semiabelian | The second disjunct of `hbase` is a conjunction of the normality clause and the following geometric-fibre extension clause. |
| Normal means every local ring is an integrally closed domain | `∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)`. This is exactly the dependency's inline normal-domain interface applied to each local ring; no global integral-domain or Noetherian assumption is added. |
| Take every algebraically closed residue-field extension k and geometric fibre | `∀ i : Fin 3, HasSemiabelianGeometricFibres (Grp.mk (G i))`. The imported shared definition quantifies over `(k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)` and uses `(Over.pullback s).mapGrp.obj (Grp.mk (G i))`, so it tests the actual pulled-back group laws. |
| The torus is (G_m,k)^r, r ≥ 0, with G_m,k = Spec k[t,t⁻¹] | The shared predicate quantifies over `r : ℕ` and uses `MultiplicativeType.splitTorus k r`. Its rank-zero product is the trivial group. |
| The quotient A is a proper smooth geometrically connected commutative k-group scheme | The shared predicate uses a bundled group `A : Grp (Over (Spec (.of k)))` with `IsAbelianVariety A.X`, defined as proper, smooth and connected. Over the algebraically closed test field this is geometrically connected, and an abelian variety's group law is commutative. This is the equivalent interface requested by the independent return. |
| An extension exact as fppf sheaves, 1 → torus → geometric fibre → A → 1 | The shared predicate requires group homomorphisms `i`, `q`, the full kernel square `IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus k r).X) q.hom.hom η[A.X]`, and `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k))) (yoneda.map q.hom.hom)`. The consumer reuses the predicate without expanding or redefining it. |
| P is the triple fibre product | `(∏ᶜ G).left`. Products in `Over S` are the existing limits over S, so these are scheme fibre products with their canonical projections. |
| j_i has domain the product of the other two factors and inserts e_i | `groupIdentityFace G i : (∏ᶜ (fun j : { j : Fin 3 // j ≠ i } ↦ G j.1)) ⟶ ∏ᶜ G`. Its `Pi.lift` component is `1` when the coordinate equals i and the product projection `Pi.π ... ⟨j,h⟩` otherwise. `.left` is the required scheme morphism. |
| M is any invertible O_P-module | `(M : (∏ᶜ G).left.Modules) [M.IsInvertible]`, using the dependency's exact invertible-module class. |
| Each j_i^* M is isomorphic to the structure sheaf | `hfaces : ∀ i : Fin 3, Nonempty ((Scheme.Modules.tensorPullback (groupIdentityFace G i).left).obj M ≅ SheafOfModules.unit _)`. This is a proposition asserting existence for each face. No chosen frame or compatibility is supplied. |
| Pullbacks are tensor inverse images | `Scheme.Modules.tensorPullback` is the dependency's existing sheafified `O_X ⊗_(g⁻¹ O_Y) g⁻¹ M`, not a replacement abstract functor. |
| Then M is isomorphic to O_P | `Nonempty (M ≅ SheafOfModules.unit _)`. Only existence of a trivialization is asserted, with neither uniqueness nor prescribed face values. |
| No trivialization, cubical structure or symmetry supplied | No extra hypothesis or field of these types occurs. The existential face isomorphisms are exactly the stated face-triviality assumptions. |

The geometric-fibre test fields have the same universe as the scheme's local rings, as
in the standard geometric-property API; there is no independent smaller universe making
the condition vacuous. Geometric extensions of residue fields are included up to their
usual small isomorphic models. In particular the statement does not require that the
base or its residue fields are perfect or algebraically closed.

### Dependency declarations read and reused

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  its public separatedness dependency defines `AlgebraicGeometry.IsSeparated`.
* `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `IsDomain` is used together with it for each stalk, following the normal-ring record.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes the canonical
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` defined in
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; its actual tensor formula was read.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: existing `pullback`
  and its projections; the existing over-category product construction is used to
  express iterated fibre products and canonical faces without equality transports.
* `Mathlib.CategoryTheory.Monoidal.Grp`, via `def-sc-group-scheme`:
  `CategoryTheory.GrpObj`, `Grp`, `IsCommMonObj`, group morphisms and their laws.
  The same existing categorical definition works over arbitrary S. The landed node's
  field-specific applications are not redefined.
* `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`, via the already landed
  `def-sfb-tori-multiplicative-type`: `AlgebraicGeometry.MultiplicativeType.splitTorus`,
  now available through the public imports of the shared geometric-fibre predicate.
* `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`, via the landed
  `def-sfb-semiabelian-geometric-fibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`. Its full definition and docstring
  were read, together with the underlying `IsAbelianVariety` definition in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.
  The group-scheme, torus and semiabelian-fibre nodes are the three added `stmt_deps`.
* The shared predicate owns the kernel square, local-surjectivity and geometric
  base-change ingredients. Their former direct imports in this consumer are removed.

Every already stated proof dependency is imported, with proof-only imports non-public:
smooth-connected generic geometry, universal openness, relative unit factorization,
proper flat global sections, the three Picard-locus statements, the field cube theorem,
finite Galois tensor decomposition and fpqc descent. Other proof dependencies have no
Lean record or usable Mathlib match and are not needed to type the statement; they are
not restated here. No import cycle was introduced. The docstring reproduces all twelve
steps of the accepted DAG proof, with its cited nodes and source places.

### Edge cases checked before writing

* Empty S: there is no nonemptiness binder; normality and fibre clauses may be vacuous,
  all schemes over S are empty, and the claimed line triviality is the expected one.
* A trivial group factor: its identity face parametrizes all of P. The corresponding
  face-triviality assumption already gives the conclusion up to the canonical product
  isomorphism. No factor is required to have positive dimension.
* r = 0: the existing `splitTorus k 0` is the trivial group. The kernel-square/local-lift
  expression reduces to a trivial-kernel quotient, so abelian fibres are included.
* Nonreduced proper base: the first disjunct of `hbase` imposes no stalk condition.
* Disconnected normal base: normality is local at every point, not `IsIntegral S`.
* Imperfect residue fields: algebraic closedness occurs only on geometric test fields;
  the original residue fields are unrestricted.
* Nontrivial split tori: local surjectivity is for the fppf topology, not surjectivity
  of rational points, and no global quotient section is demanded.
* Compatible or incompatible choices of face frames give the same hypothesis:
  `Nonempty` keeps existence only; the statement does not accept chosen frame data.

### Searches actually run

1. `msearch.py ... leanfinder` with query
   `An invertible sheaf on a product of three semiabelian schemes trivial on each identity face is trivial`:
   eight hits, concerning pullback-carrier identities and Cartesian products; none states
   this relative Picard assertion.
2. `msearch.py ... loogle` with query
   `CommGrpObj, AlgebraicGeometry.Scheme.Modules.IsInvertible`:
   zero hits; service reported unknown identifier `CommGrpObj`. This is recorded as
   an unavailable identifier search, not evidence that the group-object API is absent.
3. `msearch.py ... grep` with query
   `theorem.of.the.cube|Semiabelian|semiabelian`: zero Mathlib hits.
4. `rg` in both project Lean roots for `Semiabelian|SemiAbelian|semiabelian|semiAbelian`
   initially found only a comment in StableLevelVersalBranchFreeness. This historical
   result is superseded by the repair search below.
5. `rg` in both project Lean roots for
   `relative_picard_cube|groupIdentityFace|identity.faces|Picard.*cube`: no existing
   exact theorem or canonical face helper. The explicit item-id grep in
   `lean/WeilConjectures` also had no result.
6. Broader group-scheme and torus searches found the existing Cartesian group objects,
   ToriMultiplicativeType, StandardGroupSchemes, and quotient geometry; these were read
   and reused. The initial DAG search preceded the semiabelian-fibre node landing;
   the repair uses that landed node as recorded below.
7. Reading the existing `GeneralTheoremOfCube` and upstream AbelianVariety/Cube confirms
   they are field/proper results, not this arbitrary-base proper-or-normal-semiabelian
   assertion; attaching either as `existing: true` would omit the second case.

8. `msearch.py ... leansearch` with query
   `A line bundle on a triple product of semiabelian group schemes trivial on all three identity faces is trivial`:
   eight hits, all unrelated fibre-bundle trivializations or additive subgroups; no exact
   relative scheme/Picard statement.

### Source check and limitations

The live source describes this as an agent-extracted geometric prerequisite, not the
cubical-category equivalence itself. Its stage-1 report Q23 explicitly marks
Moret-Bailly I 2.6 and Lan Proposition the project server WANTED. I do not claim to have read either
missing original. I read the current blueprint unit from `literature/blueprint/latest`
and the accepted node/proof instead of an old snapshot. The inherited source status is
unchanged. No new proof or source-based correction is asserted in this delivery.

The geometric extension interface agrees with the kernel/quotient interpretation in
[Conrad's notes](https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf),
Definition 2.2 and Theorem 3.1. I read that primary online PDF; its discussion allows
arbitrary, possibly imperfect fields. The local canonical group/tensor definitions
were checked directly in their defining modules.

### Validation

The repaired module compiled through the prescribed `scompile.py` under both its
sandbox name and its final library module name (2.6 s and 2.2 s), with no errors
or unexpected warnings. The final node's `lean.statement` is extracted verbatim
from the theorem keyword up to `:=`; helper and theorem are both listed in
`lean.declarations`. All variables and universes are explicit, both auto-implicit
options are disabled, and the self-check confirmed line widths and the single
whole-proof `sorry`. The saved original packet passed its initial dry run;
the repaired packet is separately checked with `deliver2.py --no-push` before push.

## Returned-delivery repair (H4)

The independent return on head `4ece8a59a715` identified a duplicate inline rendering
of semiabelian geometric fibres. The saved packet first passed the prescribed dry
run; that mechanical success did not resolve H4. I read the current landed node
`def-sfb-semiabelian-geometric-fibres`, its `lean` record, its module's full predicate
and docstring, and the underlying abelian-variety definition. A fresh `rg` search
for `HasSemiabelianGeometricFibres` in the two allowed project Lean trees found
its defining module and the existing `SymmetricLinePowerProlongation` consumer.

The repaired module publicly imports
`Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres` and the normal-base branch now
uses exactly `∀ i : Fin 3, HasSemiabelianGeometricFibres (Grp.mk (G i))`.
The node gains `def-sfb-semiabelian-geometric-fibres` in `stmt_deps`; its `lean.statement`
is re-extracted verbatim. The direct Fpqc, Sites.Over, LocallySurjective and
ToriMultiplicativeType imports are removed; the shared predicate publicly imports
those ingredients. Every proper-base, normal-stalk, group-geometry, identity-face,
invertible-module and face-triviality clause is retained. The natural-language
statement and accepted proof plan are unchanged. No statement correction or new
node is needed. Comparison with the current main node found only the authorized
`lean` and `stmt_deps` differences, including the two previously reviewed landed
notions and the newly required shared predicate.

Repair self-check: empty base still makes the geometric-point quantification vacuous;
rank zero remains allowed by the shared predicate's natural-number rank; the test
fields retain universe `u`; the proper disjunct still imposes no normality or
semiabelian hypothesis. The final theorem contains one whole-proof `sorry` and
`groupIdentityFace` retains its fully specified universal-property construction.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
