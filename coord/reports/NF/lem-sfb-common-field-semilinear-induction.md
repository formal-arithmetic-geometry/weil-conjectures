## Worker report

This is the stage-2 statement of `lem-sfb-common-field-semilinear-induction`, in
`lean/Sheaf/AlgebraicGeometry/CommonFieldSemilinearInduction.lean`, with main declaration
`AlgebraicGeometry.common_field_semilinear_induction`. Its sole theorem has proof `sorry`.
The helper `AlgebraicGeometry.invariantSchemeFiberMap` is the actual `pullback.map` induced
by an invariant endomorphism, with identity maps on the point and base. Its data are fully
specified, without any postponed theorem or choice of an arbitrary morphism. Both declarations
are listed in the node's `lean.declarations`. No definition node or dependency module is needed:
actions are existing monoid homomorphisms into automorphism groups; the contracted product is
specified directly by an existing coproduct universal property and the explicit equations.

Source read: ILO, Travaux de Gabber, Expose X 2.3 Step 2, printed pp.150--151, PDF pp.156--157.
The displayed graph enlargement and contracted products preceding (2.b) give the construction;
the node already records its finite-family common-normal-field elaboration. I read the node's
ten proof steps, all eleven statement-dependency statements and records, and the signatures and
docstrings of the recorded declarations. I also read the proof-dependency records and their
field, coproduct, going-down and Zariski-lemma declarations. The theorem docstring contains
all ten steps and their named dependencies.

The prior BLOCKED report mistook an accepted stage-1 split for a completed stage-2 statement.
At the time of reading, `coord/ledger.md:24378` and the ND report record the stage-1 delivery
and its two field-theory leaves. The item has `reviewed.result = pass`, but no `lean` and no
`reviewed_lean`. Thus that delivery is used as the proof outline, not split or delivered again.
This delivery changes only the item's `lean` field, adds its statement module, and adds this
report. It does not change the mathematical statement, dependencies or proof.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| Base field e | `(e : Type u) [Field e]` |
| Nonempty finite set I | `(I : Type w) [Finite I] [Nonempty I]` |
| Finite extensions F_i/e | `F`, the dependent `Field`, `Algebra e`, and `Module.Finite e` instances |
| Finite groups J_i | `J`, dependent `Group` and `Finite` instances |
| Their e-automorphisms of F_i | `rho : ∀ i, J i →* (F i ≃ₐ[e] F i)` |
| Schemes V_i and B_i, with their scalar maps | `V B`, `p`, and `b` |
| Finite-type F_i-schemes | `LocallyOfFiniteType (p i)` and `QuasiCompact (p i)` |
| Semilinear J_i-actions on V_i | `a : ∀ i, J i →* Aut (V i)` and `ha` |
| Invariant e-morphisms v_i | `f`, `hbase` and `hinvariant` |

`ha` uses `Spec.map (rho i j⁻¹).toRingHom`, with `CommRingCat.ofHom` around the ring map.
This is the inverse convention explicitly required by proof step 3; `Aut` multiplication is
function-composition order. Neither normality of F_i/e nor faithfulness of either action is
assumed. B_i has no finiteness, separatedness, normality or nonemptiness assumption.

Clause-by-clause correspondence, in the order of the statement:

| Node conclusion | Lean rendering |
| --- | --- |
| A common finite normal K/e | Existential `K`, `Field K`, `Algebra e K`, `Module.Finite e K`, `Normal e K` |
| Embeddings F_i into K | `emb : ∀ i, F i →ₐ[e] K`; field algebra homomorphisms are injective |
| Finite G and surjection to Aut_e(K) | Existential `G`, `Group G`, `Finite G`, `pi`, and `Function.Surjective pi` |
| Subgroups Gamma_i and surjections to J_i | `Gamma`, `r` and `∀ i, Function.Surjective (r i)` |
| Agreement of the two field actions | The equality `pi gamma (emb i x) = emb i (rho i (r i gamma) x)` |
| W_i is exactly V_i times_{F_i} K | Every occurrence uses `pullback (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom))` |
| Its diagonal Gamma_i-action | `d`, with its two projection equations specifying the original action on V_i and inverse-Spec scalar action on K |
| The fixed extension K^G/e is purely inseparable | `IsPurelyInseparable e (IntermediateField.fixedField pi.range)` |
| The induced scheme exists | `Y`, `q`, `aY`, `fY`, `t` and `s`, with the following universal property and equations |
| Copies indexed by left cosets | `s : ∀ i, G ⧸ Gamma i → G`, with `Quotient.mk (QuotientGroup.leftRel (Gamma i)) (s i c) = c` |
| Disjoint union of those copies | `Nonempty (IsColimit (Cofan.mk (Y i) (fun c ↦ t i (s i c))))` |
| Scalar structure twisted by g | `t i g ≫ q i = pullback.snd ... ≫ Spec.map (CommRingCat.ofHom (pi g⁻¹).toRingHom)` |
| Relation (g gamma,w) equivalent to (g,gamma w) | `t i (g * gamma) = (d i gamma).hom ≫ t i g` |
| G acts by left multiplication | `t i g ≫ (aY i h).hom = t i (h * g)` |
| This G-action is semilinear | The equality `(aY i g).hom ≫ q i = q i ≫ Spec.map ... (pi g⁻¹)` |
| [g,w] maps to v_i(pr_1 w) | `t i g ≫ fY i = pullback.fst ... ≫ f i` |
| The resulting morphism is over e | `fY i ≫ b i = q i ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))` |
| It is invariant | The existential proof `hinvariantY : ∀ i g, (aY i g).hom ≫ fY i = fY i` |
| Every geometric point b | Arbitrary `Omega : Type u`, `[Field Omega] [IsAlgClosed Omega]`, and `z : Spec (.of Omega) ⟶ B i` |
| Nonempty single J_i-orbit implies nonempty single G-orbit on the underlying geometric fibre points | The penultimate conjunct: `Nonempty` of the coerced pullback scheme and `∀ x y, ∃ j/g`, equality after the actual `invariantSchemeFiberMap` |
| Generic points map to generic points with finite residue extension if v_i does | The final implication, using `genericPoints` and `((f i).residueFieldMap x).hom.Finite`, then the corresponding terms for `fY` |
| Normal does not mean separable | `Normal e K` is algebraicity and splitting of minimal polynomials; no `IsSeparable` or `IsGalois` assumption appears |

`IsColimit` is data in Mathlib, so its existence is expressed by `Nonempty`, rather than put
directly in a conjunction. This is the actual universal property, not an unspecified equivalence
or an arbitrary comparison map. For schemes this coproduct is the disjoint union by the
recorded coproduct-family node. The `t` equations characterize all copies from the coset
representatives, and specify exactly the contracted-product relation and induced action.
The existential proof `hinvariantY` is the invariant-map clause itself, bound so that the
canonical base-changed maps can use it. The orbit condition explicitly retains nonemptiness;
it is not replaced by vacuous pairwise transitivity on the empty fibre.

The scheme and field universe is `u`, as in the dependency's `SpecToEquivOfField` convention;
the finite index and group universes `w` and `v` are independent. The output group lives in
`Type (max u v w)`, accommodating Aut_e(K) times the dependent product of the J_i. Its finite
coset sets are small in the scheme universe, so the coproduct conclusion does not impose an
extra size hypothesis. No equality between the group/index universes and the scheme universe
is required. All variables and universes are explicitly bound; `autoImplicit` is false.

Dependency declarations used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-field-extension`: `Algebra` and `algebraMap`, Mathlib.Algebra.Algebra.Defs;
  `RingHom.injective` ensures the maps `emb` really are embeddings.
- `def-pc-field-tower`: Sheaf.FieldTheory.FieldTower, `FieldExtension.degree`; its module's
  recorded finite-extension convention is the existing `Module.Finite`, used directly here.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, Mathlib.AlgebraicGeometry.Scheme.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `AlgebraicGeometry.QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact (available through FiniteType).
- `def-pc-fibre-product` and `def-weil-geometric-fibre`: `CategoryTheory.Limits.pullback`,
  its projections and `pullback.map`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  with scheme pullbacks available through Mathlib.AlgebraicGeometry.Limits.
- `def-weil-finite-integral-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  `AlgebraicGeometry.IsFinite`; imported as recorded, for the finite scalar projection in the proof.
- `def-sc-generic-point`: `IsGenericPoint`, Mathlib.Topology.Sober; the same module's
  `genericPoints` is the set of generic points of irreducible components.
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  Mathlib.AlgebraicGeometry.ResidueField; ring-map finiteness is used to avoid choosing
  independent algebra instances for residue extensions.
- `def-weil-geometric-point`: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, and
  `Scheme.SpecToEquivOfField`, Mathlib.AlgebraicGeometry.ResidueField. Geometric points are
  written inline with the exact field/morphism binders in that node's record.

All stated proof dependencies are imported without `public` when not also statement
dependencies: `Field.exists_common_extension` (WeilConjectures.FieldTheory.CommonExtensionFields),
`Normal.fixedField_purelyInseparable`
(WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable),
`IntermediateField.adjoin_rank_le_of_isAlgebraic_right`
(Mathlib.FieldTheory.IntermediateField.Adjoin.Basic), the normal closure interfaces
(Mathlib.FieldTheory.Normal.Closure), `AlgEquiv.liftNormal` and its commuting equation
(Mathlib.FieldTheory.Normal.Basic), `Normal.algHomEquivAut` and `Normal.tower_top_of_normal`
(available through the public normal/Galois interfaces), `fieldOfFiniteDimensional` and
`FiniteDimensional.exists_mul_eq_one` (Mathlib.LinearAlgebra.FiniteDimensional.Basic),
`Algebra.HasGoingDown.of_flat` (Mathlib.RingTheory.Ideal.GoingDown),
`finite_of_finite_type_of_isJacobsonRing` (Mathlib.RingTheory.Jacobson.Ring), and the coproduct
existence, `sigmaOpenCover` and `disjoint_opensRange_sigmaι` (Mathlib.AlgebraicGeometry.Limits,
also used publicly for the statement's coset coproduct). No required dependency remains unstated.

Edge cases checked mathematically before and after writing:

- A singleton family and trivial groups recover scalar extension with its possible extra
  automorphisms. `G` need not be trivial even when the `J i` are trivial.
- The original field extensions may be nonnormal, for example Q(cuberoot(2)); the common
  extension is normal, and the compatible-pair subgroup retains the correct restricted action.
- Purely inseparable normal extensions are allowed. Their automorphism groups may be trivial;
  the fixed field is then all of K and remains purely inseparable over e. Tensor algebras in
  geometric fibres may have nilpotents, so using the actual pullback's underlying points matters.
- Nonfaithful group actions are allowed: surjectivity of `r i` concerns all elements of J_i,
  not just their images as field automorphisms.
- Empty V_i and empty geometric fibres satisfy the construction; the orbit implication's
  premise explicitly fails on an empty fibre. Generic-point assertions are vacuous there.
- Disconnected V_i or B_i are allowed. `genericPoints` quantifies over every irreducible
  component and places no irreducibility requirement on either scheme.
- Characteristic zero and positive characteristic are both included. No characteristic
  restriction, separability assumption or prime-to-characteristic condition is inserted.
- Arbitrary geometric points, not just a fixed algebraic closure of a residue field, appear.
- Nonempty I is exactly the node's assumption; no additional inhabited V_i/B_i is introduced.

Searches actually performed (all through the prescribed `msearch.py` unless marked `rg`):

1. LeanFinder query `Induce finite semilinear group actions on schemes to a common finite normal
   field preserving transitive geometric fibres`: 8 hits, including
   `CategoryTheory.PreGaloisCategory.toAut_surjective_isGalois_finite_family` and
   `Ideal.isPretransitive_of_isGalois`. These concern fibre functors or prime ideals, not this
   scheme contracted product and its full set of properties.
2. Loogle query `Scheme, MulAction, AlgEquiv`: no results, with diagnostic
   `unknown identifier 'Scheme'`. This query is not treated as evidence of absence.
3. Corrected Loogle query `"AlgebraicGeometry.Scheme", "Aut"`: OK, 0 hits.
4. Mathlib grep query `semilinear|contractedProduct|contracted_product|induced.*action`, restricted
   to AlgebraicGeometry: 4 hits in StructureSheaf, all scalar-localization semilinear maps.
5. `rg` across lean/WeilConjectures and lean/Sheaf for semilinear actions, contracted products
   and generic-point interfaces: related sheaf/torsor contracted products and coefficient-system
   semilinearity exist. EquivariantSmoothGaloisModel cites this node in its proof; it does not
   state the common-field induction construction. No existing declaration matches the item.
6. `rg -l` across dag/nodes and both Lean roots for
   `contracted.product|contractedProduct|[Ii]nduced[Ss]cheme|[Ss]emilinear[Ss]cheme`: existing
   torsor contracted-product presentation nodes concern torsor/sheaf constructions, not the
   finite coset coproduct of semilinear schemes. No missing independently defined notion is
   introduced: the statement uses the existing coproduct and action interfaces directly.
7. Exact-name `rg` for `common_field_semilinear_induction`, `invariantSchemeFiberMap`, and the
   item id in both Lean roots and dag/lean_names_upstream.json: only the consumer's proof
   citation of the item id; neither new declaration name exists there.

Validation: server compilation via `scompile.py NF lem-sfb-common-field-semilinear-induction`
passes in both its sandbox and actual module modes (about 2.2 and 2.3 seconds). The initial
elaboration correctly rejected a bare `IsColimit` as a proposition and ambiguous pullback
coercions; I used `Nonempty (IsColimit ...)` and explicitly coerced the Scheme pullbacks to
their underlying point types. No mathematical clause changed. The resulting file has no
errors or unexpected warnings, no auto-implicit variables, no local notation or instances,
and no line longer than 100 characters. Dry-run and delivery results follow from the wrappers.

No `STATEMENT-DISPUTED` issue, statement correction, new node, or dependency repair is claimed.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
