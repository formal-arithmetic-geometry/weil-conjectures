## Worker report

The new module `Sheaf.Paper.OrdinaryDerivedProductLegTransposes` states
`WeilConjectures.FiniteProperProduct.ordinaryDerivedProductLegTransposes`.
Its proof is exactly `sorry`. It asserts the two identities of the live node;
there is no statement correction, re-split, new node, or dependency repair.
The previous worker's stage-1 live-wins refusal does not apply to this stage-2
statement delivery: the reviewed Q75 split is preserved verbatim.

Sources read: Stacks `sites-cohomology.tex`, lines 13657--13748,
`equation-projection-formula-map` and Tag 0E48,
`remark-compatible-with-diagram`; current blueprint
`main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`,
last paragraph on the two counits. Stacks defines the projection without any
extra assumption as the adjunct of tensor comparison followed by counit tensor
identity. The blueprint identifies the exchange/projection composite with the
transpose of the pulled-back counit. The node supplies the explicit symmetry
calculation for the other leg. The declaration docstring records all three
proof steps, including the identification of the two descriptions of mu.

Every hypothesis and clause is represented as follows (names below belong to
`WeilConjectures.FiniteProperProduct` unless explicitly qualified).

| Node content | Lean rendering |
| --- | --- |
| Fixed finite-field and finite coefficient datum | `P : PurityFiniteSetting.{u}`; its `field`, `coefficients`, `extension`, `finiteExtension`, `level`, and `level_pos` are the recorded datum. |
| Coefficients A at positive level n | Existing `A P` is `finiteCoefficientRing P.coefficients.l P.extension (P.level - 1 + 1)`; `P.level_pos` gives `P.level - 1 + 1 = P.level`. This is the existing quotient, not a new coefficient ring. |
| B,Y,Z are k-schemes and a,b are k-maps | `B Y Z : Over (Spec (.of P.field.k))`, `a : Y ⟶ B`, `b : Z ⟶ B`; the Over homomorphisms include the structure-map compatibility. |
| B is separated and finite type over k | `[IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]`. |
| Y is separated and finite type over k | The same three instances on `Y.hom`. |
| Z is separated and finite type over k | The same three instances on `Z.hom`. |
| a is separated and finite type | `[IsSeparated a.left] [LocallyOfFiniteType a.left] [QuasiCompact a.left]`. |
| b is separated and finite type | The same three instances on `b.left`. |
| C, r, t | Mathlib `pullback a.left b.left`, `pullback.fst a.left b.left`, `pullback.snd a.left b.left`. |
| Ordinary unbounded D(T_proet,A) | Existing `D P T` unfolds to `Scheme.proEtaleDerivedCategory T (A P)` on the small pro-etale site. |
| Arbitrary H and J | `(H : D P Y.left) (J : D P Z.left)`; there is no boundedness, constructibility, perfection, Tor, or invertibility condition. |
| P_u, R_u and their canonical adjunction | Existing `pull P u`, `push P u`, and `adj P u`, defined using `finiteDerivedPullback`, `proEtaleConstantDerivedDirectImage`, and `sfIntrinsicConstantModuleAdjunction` followed by the recorded derived adjunction. |
| Tensor and signed symmetry | Existing `tensor` is `finiteIntrinsicDerivedTensor`; `sigma` is the `pullbackTensorBraiding` of the same finite closed structure and K-flat tensor models. |
| Canonical tensor comparison mu | Existing `mu P u sX sY M N` is exactly `canonicalFinitePullbackTensor`. Its residue-field invertibility witnesses are constructed from `P.coefficientPrime_isUnit_stalk`, not added hypotheses. |
| Square comparison theta | Existing `theta P a.left b.left`: inverse t,b compositor, the pullback square equality, then the r,a compositor. `comp` uses `sfIntrinsicDerivedPullbackComp`. |
| F, G, T | `(push P a.left).obj H`, `(push P b.left).obj J`, `(pull P (pullback.fst a.left b.left)).obj H`; the statement expands these expressions rather than introducing let-binders. |
| Q and E | Q is the source of existing `v P a.left b.left Z.hom H J`; E is existing `external P a.left b.left H J`. Their expressions use the same tensor bifunctor and pullbacks. |
| x | Existing `exchange P a.left b.left H` is the ordinary `mateEquiv` of theta for `adj P a.left` and `adj P t`. It is the specified exchange map, not an arbitrary comparison. |
| pi | Existing `projection` is `adj.homEquiv` applied to `mu.hom` followed by tensor of counit and identity, exactly the unit/right-image definition in def-exchange-projection. |
| v = pi_t (x tensor 1) | Existing `v`: `tensor.map (Prod.mkHom exchange (𝟙 J)) ≫ projection` along t. |
| w with both signed symmetries | Existing `w`: `sigma.hom ≫ projection P b ... J F ≫ (push P b).map sigma.hom`, exactly the order in the node. |
| Transpose h-hat = epsilon P(h) | `((adj P u).homEquiv _ _).symm h`; Mathlib's `Adjunction.homEquiv` defines this as `(pull P u).map h ≫ (adj P u).counit.app _` (Basic.lean:161--169). |
| First asserted identity | First conjunct: transpose of v equals `mu_t.hom ≫ tensor_C.map (Prod.mkHom (theta.hom.app F ≫ pull_r.map epsilon_a) (𝟙 _))`. Thus the actual source comparison on `P_t Q` is retained. |
| Second asserted identity | Second conjunct: transpose of w equals `mu_b.hom ≫ tensor_Z.map (Prod.mkHom (𝟙 _) epsilon_b)`. Its source is exactly `P_b(F tensor G)` and its target Q. |
| Both identities and no further conclusion | A conjunction of exactly those two equations. No isomorphism claim about exchange or projection, and no composite/product-swap theorem. |

Dependency declarations inspected and reused:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting` and `coefficientPrime_isUnit_stalk`.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, the canonical
  constant-ring pullback/pushforward and adjunction; the publicly available
  intrinsic finite interface is `sfIntrinsicConstantModuleAdjunction`,
  `sfIntrinsicDerivedPullback`, `proEtaleConstantDerivedDirectImage`.
- `def-weil-scheme-morphism-properties` is explicitly a convention node;
  its record names no single declaration. Its referenced Mathlib notions
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` were inspected in
  `Morphisms/Separated.lean:43`, `FiniteType.lean:43`, `QuasiCompact.lean:43`.
- `def-pc-fibre-product`: Mathlib `Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; signatures/docstrings
  read at lines 95--121, with the existing scheme pullback instance.
- `def-weil-derived-pullback-tensor-hom`:
  `Sheaf.Paper.DerivedPullbackTensorHom`, `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, `finiteIntrinsicClosed`,
  `finiteIntrinsicTensorModels` (finite part, lines 69--125).
- `lem-pur-derived-pullback-tensor-iso`:
  `Sheaf.Paper.DerivedPullbackTensorIso`, `derivedPullbackTensorIso` and its
  finite comparison/naturality and signed-braiding clauses, with the
  `canonicalFinitePullbackTensor` it identifies.
- `lem-weil-pbc-proetale-derived-pullback-composition`:
  `Sheaf.Paper.IntegralFinitePullbackComposition`,
  `integralTowerGeneralPullbackComposition` and its published canonical
  finite specializations; the existing helper `comp` is the intrinsic
  finite canonical compositor `sfIntrinsicDerivedPullbackComp`.
- `def-exchange-projection`:
  `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, the `mateEquiv`
  construction of `ExchangeProjectionStage.exchange` and
  `Adjunction.rightAdjointProjectionMap` (from the public
  `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap` import).
  The actual finite components are already spelled out by the published
  helpers `FiniteProperProduct.exchange` and `.projection` and reused here.

One definition per notion: `Sheaf.Paper.FiniteProperProductTranspose` already
exports the exact ordinary maps `A`, `D`, `pull`, `push`, `adj`, `comp`, `tensor`,
`sigma`, `mu`, `theta`, `exchange`, `projection`, `external`, `v`, and `w`.
I read their complete definitions (lines 43--213); none requires properness.
They are imported and used directly, with no copy or alternative comparison.
The theorem `finiteProperProductTranspose` in that module is not used: it has
properness hypotheses and six conclusions, so it is not an existing match.
The new signature has the two conclusions and the weaker geometric assumptions
specified by this node, with proof left sorry.

Import bookkeeping: the containing module is also the module for a consumer
whose DAG proof_deps contains this item. No current import cycle is introduced:
its published source does not import this module. Under stages/2-statements.md
section 3(7), the maintainer must omit the automatic reverse proof import into
`FiniteProperProductTranspose`, since it would close a cycle. The new theorem
uses only that file's helper definitions, not its theorem. A future proof module
can import both, or the helpers can later be factored into a shared definitions
module. No false DAG dependency on the consumer theorem is added here.

Edge cases checked against the formulas: H=0 and J=0 give zero arrows; identity
maps give the ordinary counit/unit identities with the same mu; empty Y or Z
has the same well-typed fibre product and zero category, with no nonempty
hypothesis. For odd shifts, `sigma` is the signed derived braiding, so the two
Koszul swaps cancel by involutivity rather than being replaced by an unsigned
swap. Positive level 1 is represented by index 0; the shift by one excludes
no allowed level. A nonproper open immersion is allowed by the actual theorem
binders, unlike the existing proper-product theorem. The site retains objects
in universe u+1 and morphisms in u, with the existing coefficient lift; no new
universe equality or smallness assumption is imposed. No disputed statement
or mathematical node fault was found.

Searches actually run:

- `msearch.py ... leanfinder "Adjunction transpose of derived exchange followed
  by projection and symmetry conjugated projection equals pulled counit tensor
  identity and identity tensor counit"`: 8 hits, including
  `mateEquiv_counit`, `mateEquiv_counit_symm`, and
  `Adjunction.map_μ_comp_counit_app_tensor`. These are general ingredients;
  none asserts both identities for these finite pro-etale maps.
- `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.BraidedCategory.braiding"`: 0 hits.
- `msearch.py ... grep "projection.*(counit|mate)|counit.*tensor"
  CategoryTheory`: 16 hits, general monoidal counit/tensor equations. No exact
  two-leg pro-etale statement.
- `msearch.py ... leansearch "The adjunction transpose of exchange followed by
  projection is pulled back counit tensor identity, and the transpose of symmetry
  conjugated projection is identity tensor counit"`: 8 hits, including
  `Adjunction.homEquiv_symm_id`, `counitAsIsoOfIso`, and Cartesian pullback
  adjunction counit equations. No exact match.
- `rg -n 'ordinaryDerivedProductLegTransposes|leg[Tt]ranspose|[Ll]eg.*[Tt]ranspose'`
  in both `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration.
- `rg -n 'lem-pur-ordinary-derived-product-leg-transposes' lean/WeilConjectures`:
  no attachment. The same search in `lean/Sheaf` returned no statement.
- Searches for ordinary projection/external-product definitions in both trees
  found `FiniteProperProductTranspose.lean`, whose definitions are reused, and
  generic fixed-scalar product maps in `FiniteProductCompactification.lean`.
  The latter use a different coefficient presentation and do not state this node.

Validation: scompile.py compiled the final module in both sandbox and library
module modes cleanly, 14.1 s and 13.5 s, with no warning or error. An earlier
line-length warning was fixed by separating the H,J binders; all lines are at
most 100 characters. Every universe and variable is explicitly bound, with
`autoImplicit false`. The only new declaration is the named theorem, whose
three-step proof docstring and DAG node accompany its sorry.

## Second reading by Q37

Final reread by the same worker; this is not represented as an independent
review. The dispatcher explicitly prohibited starting another agent; the
maintainer performs the independent delivery review. I compared the live node,
its proof, the definition bodies of v/w/mu/theta, and the final theorem.
In particular I checked the pullback orientation r=fst, t=snd, the theta
component at F (not H), the tensor identity at P_t J, the order of both signed
symmetries in w, and the second counit at J. The two source mu comparisons are
present. All three schemes and both arrows carry exactly the separated
finite-type assumptions; properness and any boundedness assumption are absent.
Only a line-length formatting defect was found during compilation and fixed.
The consumer/helper import bookkeeping issue is explicitly recorded above.
