## Worker report

The module `Sheaf.AlgebraicGeometry.StackFlatScalarSections` states
`CategoryTheory.stack_flat_scalar_sections`. It also supplies the canonical
restriction along an arbitrary flat affine scalar extension; the earlier
`moduliBaseChangeAlgebra` interface only accepts an etale chart, so it cannot
be applied to an arbitrary flat algebra. The construction here is literal
precomposition on the existing actual 2-fibre product, not a substitute map.
No node statement has been corrected. No new independent definition node or
dependency repair is needed: all helper declarations belong to the canonical
maps and algebra structures in this item's own statement.

Hypotheses and clauses, with the node and final module open:

- `k : Type u`, `[Field k]` is the given field. `R S : Type u`, the two
  `[CommRing]` and `[Algebra k]` binders are the two commutative k-algebras.
  `[Algebra R S] [IsScalarTower k R S]` specifies the given k-algebra map,
  with `_hflat : (algebraMap R S).Flat` its flatness. No finite type,
  finite generation, finite presentation, nonzero-ring or Noetherian
  assumptions are present. Schemes all lie in the node's fixed universe u;
  the stack's object and arrow universes v,w remain independent.
- `F : BasedCategory.{v,w} (Over (Spec (.of k)))` and
  `hF : IsAlgebraicModuliStack F` are the algebraic stack over k.
  `p` is its based functor to the representable Spec R groupoid.
  `_hpqc` and `_hpqs` are exactly the recorded quasi-compact and
  quasi-separated morphism predicates, in the same universe specialization
  as `adequatelyAffine_iff_global_power_lifting`.
- `flatScalarSpecMap` is Spec of the actual algebra map, with its structural
  triangle supplied by `IsScalarTower.algebraMap_apply`.
  `flatScalarStack` is `moduliTwoFiberProduct p flatScalarSpecMap`.
  `flatScalarProjection` is the existing first projection q and
  `flatScalarBaseProjection` is the existing second projection p_S.
- `flatScalarRestriction` has presheaf `q.toFunctor.op` followed by A's
  presheaf. Its operations are unchanged, its sheaf proof is the named
  `flatScalarRestriction_isSheaf`, and its structure map is whiskering
  A's structure map after the named canonical equality of structure
  presheaves. The fibredness proof is `flatScalarStack_isFibred`.
  These are proof obligations about uniquely specified constructions;
  no definition contains postponed data or arbitrary choices.
- The first conjunct preserves `IsQuasicoherentModuliAlgebra`.
  The second quantifies over A, B and an algebra morphism f, assumes
  both quasi-coherent and f locally surjective, and concludes local
  surjectivity of `flatScalarRestrictionMap p f`. This is the precise
  sheaf-surjection notion, not pointwise surjectivity.
- `moduliSectionsAlgebra p A` bundles the EXISTING compatible-family
  ring `moduliGlobalSectionsRing A.right` with structural R-action.
  Its carrier and ring operations are unchanged. The action evaluates
  at x as A's structure hom applied to `moduliScalarMap p x r`.
  The target algebra uses `flatScalarBaseProjection p`, so its action
  is specifically p_S^*, rather than an arbitrary S-action.
- `e A hA` is an S-algebra equivalence from
  `S ⊗[R] moduliSectionsAlgebra p A` to the restricted section algebra.
  This is the node's tensor extension with factors swapped by the
  canonical `TensorProduct.comm`, as already allowed by the recorded
  `def-weil-module-base-change` interface. Its pure tensor equation
  is `e A hA (s ⊗ₜ[R] a) = flatScalarSectionRestriction p A a * p_S^*s`.
  Thus it specifies the canonical map, not mere abstract isomorphism.
- The next equation is naturality in every algebra morphism. Both
  section maps are the componentwise `moduliAlgebraSectionsMap`;
  `flatScalarRestrictionMap` precomposes the same components. Equality
  is stated on every pure tensor, which determines equality of the
  additive maps on all tensors.
- The last conjunct explicitly specializes to the structure algebra
  `Under.mk (𝟙 (moduliStructureSheaf F hF.1.1))`, and states that
  `s ⊗ₜ[R] 1` maps to its structural section. Its `hO` binder is the
  proof argument required by the same quasi-coherent comparison,
  not an extra theorem hypothesis. This is the node's 1 tensor s
  after the standard tensor flip. The structure algebra is always
  quasi-coherent (the free rank-one module).

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (180).
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map` (470,479);
  Mathlib.AlgebraicGeometry.GammaSpecAdjunction: `Scheme.ΓSpecIso`.
- Mathlib.RingTheory.RingHom.Flat: `RingHom.Flat` (27).
- Mathlib.LinearAlgebra.TensorProduct.Tower: `LinearMap.baseChange`
  (661), and Mathlib.RingTheory.TensorProduct.Basic for the algebra
  tensor structures. The base-change node's recorded tensor-order
  convention is observed.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack:
  `IsAlgebraicModuliStack` (including fibredness through its stack field).
- Sheaf.AlgebraicGeometry.StackQcqsMorphism:
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  `BasedCategory`, `BasedFunctor`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `IsFibredInGroupoids`.
- Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra:
  `ModuliAlgebraSheaf`, `moduliStructurePresheaf`, `moduliStructureSheaf`,
  `moduliGlobalSectionsRing`, `IsQuasicoherentModuliAlgebra`,
  `IsSurjectiveModuliAlgebra`, `moduliFppfTopology`.
- Sheaf.AlgebraicGeometry.StackScalarAlgebra:
  `moduliScalarMap`, `moduliScalarMap_naturality`; its already landed
  owner `def-sfb-stack-scalar-algebra` is added to stmt_deps.
- Sheaf.AlgebraicGeometry.OpenModuliSubstack: `moduliTwoFiberSnd`;
  its already landed owner `def-sfb-open-moduli-substack` is added
  to stmt_deps. It supplies the actual second projection over k.
- Proof imports: Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction,
  `exists_moduliSchemeRestriction`, and
  WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections,
  `Scheme.Modules.exists_tensorPullback_affine_sections`. Their full
  docstrings/signatures were read. The proof dependency
  `lem-sfb-stack-higher-images-flat-comparison` has no Lean record yet,
  so there is no module to import for it; it is mentioned in the
  complete natural-language proof, following the DAG.

Source checks: read stacks-cohomology.tex lemma-flat-comparison (0765)
and proposition-loc-qcoh-flat-base-change (0771), especially (4), and
stacks-sheaves.tex lemma-quasi-coherent (06WK) and
lemma-pullback-quasi-coherent (06WH). These give exactly the restriction
conventions and flat degree-zero comparison used here. The helper proofs
are documented separately; the main theorem docstring retains all four
DAG proof steps and their cited node names.

Edge cases checked: S=0 is allowed and Spec S can be empty; an empty
stack has the zero compatible-family section ring; identity scalar
extension is included; arbitrary characteristic is included; arbitrary
quasi-coherent algebras, including the zero algebra, are quantified over.
The projection keeps all automorphisms and the source and target sites
are not replaced by sets of isomorphism classes. There are no extra
algebraicity or geometric-flatness hypotheses on q.

Searches actually run with batch2/msearch.py for this item:

- LeanFinder: "Flat scalar extension commutes with global sections of
  quasi coherent algebras on a quasi compact quasi separated algebraic
  stack". Eight hits, including `Flat.flat_appLE`, `Spec_Γ_naturality_assoc`,
  and flat scheme morphism instances. None states the stack theorem.
- LeanSearch: same query. Eight hits, including
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, `RingHom.Flat`,
  and `comonadicExtendScalars`; none states the theorem.
- Loogle: `"AlgebraicStack"`: zero hits.
- Mathlib grep via msearch: `AlgebraicStack|flat.*base.change.*stack`:
  zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for scalar-flat and
  moduli-section names found the existing scalar algebra and structural
  map helpers used above, but no theorem. Exact proposed names
  `moduliAlgebraSectionsMap|moduliSectionsAlgebra|flatScalarStack|stack_flat_scalar_sections`
  had no matches in either source tree before writing. The required
  node-id grep of lean/WeilConjectures had no matches. Searches and
  source reading avoided duplicating `moduliScalarMap` and the
  existing second projection.

Validation: prescribed scompile.py compiled both the sandbox probe and
`Sheaf.AlgebraicGeometry.StackFlatScalarSections` cleanly. All universes
are explicitly declared and `autoImplicit false` is set. Theorems use
`sorry` as required for stage 2. No STATEMENT-DISPUTED issue found.

## Second reading by NL

This is a separate self re-reading, as this dispatcher assignment forbids
starting another agent. Compared the final node and module clause by
clause again. The initial draft's unbundled base action was not inferable
from a bare section ring: it is now bundled as `moduliSectionsAlgebra`,
retaining exactly the structural map p and the unchanged carrier. Checked
that its target uses the actual second projection and that the pure-tensor
formula multiplies q^*a by this structural scalar. The source's tensor
order is exchanged canonically, not changed mathematically. Checked
naturality for every morphism and tensor generator, local surjectivity,
and both quasi-coherence hypotheses on a surjection. The final explicit
unit clause uses the structure algebra itself; it no longer states an
extra arbitrary-A normalization clause. Fibredness and descent helper
proofs refer to the same total 2-fibre product, and no missing map is
replaced by an arbitrary existential choice. No statement mismatch
remains. The unchanged higher-image proof dependency is not available
as a module and therefore is not spuriously imported.
