## Worker report

Module `Sheaf.RingTheory.NoetherianArrowEventualInjectiveFlatCokernel` states
`Module.eventually_injective_flat_cokernel_of_noetherian_local_stages`, with one
postponed theorem and no new definitions. The node is unchanged except for `lean`.
The current stage-1 split/review is a prerequisite for this stage-2 statement, not
an attempt to split the already reviewed node again. There is no repair note.

Clause-by-clause correspondence:

- Small nonempty directed set: `{I : Type u}`, `[Preorder I]`, `[Nonempty I]`,
  `[IsDirected I (· ≤ ·)]`. All rings, modules and indices inhabit a common
  sufficiently large universe, explicitly allowed by the statement. A preorder
  representation is equivalent to a directed-set presentation and excludes no poset.
- Stage rings and transition identities/composition: `Ri Si : I ⥤ CommRingCat`.
  Ring cocones `cR`, `cS` include cocone compatibility; `hcR`, `hcS : IsColimit`
  express the recorded categorical colimits.
- Stage and limit local rings: the four families/instances of `IsLocalRing`.
  Stage arrows and limit arrow are `algebraMap` with `IsLocalHom` instances;
  `hR_local`, `hS_local` assert transition locality, and the cocone `IsLocalHom`
  instances assert cocone locality. For local rings Mathlib's unit-reflection
  definition is equivalent to inverse image of the maximal ideal being maximal.
- Cocone ring maps: `hR`, `hS` identify the algebra maps with the specified cocones.
  The two scalar towers into `cS.pt` encode the commuting limit squares;
  `h_ring_arrow` encodes the commuting stage squares. Algebra and tower instances
  only package the given maps and their restrictions, not extra constraints.
- Algebraic ring colimits: `hR_represent`, `hS_represent`, `hR_equal`, `hS_equal`
  explicitly give representatives and common-later-stage equality detection.
- Stage Noetherianity: `[∀ i, IsNoetherianRing (Ri.obj i)]` and the same for `Si`.
- Finite stage modules: `Mi Ni : I → Type u`, additive group and `Si` module
  instances, and both `Module.Finite` instances. The `Ri` module and scalar tower
  instances are exactly restriction through the stage arrow.
- Stage arrows: `ui : ∀ i, Mi i →ₗ[Si.obj i] Ni i`.
- Additive semilinear transitions: `m`, `n` with `hm_smul`, `hn_smul`.
  Identity and composition are `hm_id`, `hn_id`, `hm_comp`, `hn_comp`.
  The commuting module-arrow square is `h_stage_arrow`.
- Limit modules and additive semilinear cocones: `M`, `N`, their additive groups
  and `cS.pt` module instances, `mu`, `nu`, `hmu_smul`, `hnu_smul`.
  Compatibility is `hmu_comp`, `hnu_comp`. The `cR.pt` actions and towers are
  the induced restrictions. `u` is the limit linear arrow and `h_limit_arrow`
  is precisely `nu_i u_i = u mu_i`.
- Algebraic abelian-group colimits: `hM_represent`, `hN_represent`, `hM_equal`,
  `hN_equal`. Together with the cocone laws these are the elementwise filtered
  colimit, including the induced scalar actions already specified above.
- Localized ring base change: `hloc` quantifies a ring homomorphism `q`, specifies
  its values on every pure tensor, and asserts `IsLocalization W` for `q.toAlgebra`.
  Mathlib's three localization axioms are exactly units, fractions, and annihilators
  as in the node. These values uniquely determine the canonical map.
- Both module base-change isomorphisms: `hbaseM`, `hbaseN`, as linear equivalences
  with their pure-tensor formulas. New scalar ring first is the tensor symmetry
  of the source convention, with no change in the canonical map.
- Flat limit target: `[Module.Flat cR.pt N]`.
- Injective limit closed-fibre arrow: `h_fibre` is injectivity of
  `(u.restrictScalars cR.pt).lTensor (IsLocalRing.ResidueField cR.pt)`.
  `TensorProduct.quotTensorEquivQuotSMul` identifies this naturally with the
  map on the quotients by maximal-ideal multiples.
- Given eventual threshold: `i₁` and `h_source`. Write `k = ResidueField cR.pt`.
  `k ⊗[Ri.obj j] Mi j` canonically identifies with
  `k ⊗[ResidueField (Ri.obj j)] (ResidueField (Ri.obj j) ⊗[Ri.obj j] Mi j)`
  by `TensorProduct.AlgebraTensorModule.cancelBaseChange`. The inner tensor
  identifies with the quotient fibre by `quotTensorEquivQuotSMul`.
  The scalar map `Ri.obj j → k` is explicitly the composition through `cR.pt`;
  locality makes its factorization through the stage residue field the canonical
  residue-field embedding. The existential `Ψ` is constrained on ALL pure tensors
  by `Ψ (c ⊗ x) = c ⊗ mu j x`, uniquely determining it. This is the original
  `Ψ_j` under these canonical identifications. Existence is automatic from the
  given semilinearity and commuting scalar square; its only additional property
  is exactly the node's assumed injectivity for every `j ≥ i₁`.
- Conclusion threshold: `∃ i₂, i₁ ≤ i₂ ∧ ∀ j, i₂ ≤ j → ...`.
  The four conjuncts are respectively target flatness `Module.Flat (Ri.obj j) (Ni j)`,
  fibre-map injectivity via residue-field `lTensor`, `Function.Injective (ui j)`,
  and `Module.Flat (Ri.obj j) (Ni j ⧸ LinearMap.range ((ui j).restrictScalars ...))`.
  The range quotient is precisely the cokernel as an `Ri.obj j` module. There is
  no injectivity assumption on the target fibre cocone.

Dependencies read and used:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.Cocone` and `CategoryTheory.Limits.IsColimit`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
- `def-weil-pbc-module-tensor-product`: Mathlib tensor product and pure tensors,
  imported through `Mathlib.RingTheory.TensorProduct.Basic` and
  `Mathlib.LinearAlgebra.TensorProduct.Quotient`; the recorded `TensorProduct`
  definition and universal property supply the notion, not a private copy.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `Module.Flat`.
- All stated proof dependencies are imported without `public`:
  `WeilConjectures.RingTheory.ColimitEventuallyFlat` (`RingTheory.exists_flat_stage`),
  `WeilConjectures.RingTheory.FlatOfLocalCriterionBaseChange`
  (`Module.flat_of_local_criterion_baseChange`),
  `WeilConjectures.RingTheory.FlatModInjective` (`flat_mod_injective`), and
  `Mathlib.LinearAlgebra.TensorProduct.Basis` (`Module.Basis.baseChange`, for
  `def-weil-vector-space-scalar-extension`). Their source signatures/docstrings
  were read. The proof docstring gives all five DAG proof steps.

Edge cases checked before writing: singleton directed index; a directed poset that
is not linearly ordered; zero source; zero target (the limit fibre assumption and
finite-source local criterion then force eventual zero source); zero vector-space
fibre; arbitrary characteristic; no empty-index case is claimed because nonemptiness
is explicit in the node. Local rings are nontrivial, so the zero ideal used in the
proof is proper. Neither Noetherianity nor finiteness is imposed on limit rings
or limit modules. No additional hypothesis on target cocone injectivity occurs.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: “Noetherian local directed module arrow systems with flat limit target
  and eventually injective scalar extended closed fibre comparisons have eventually
  injective maps with flat cokernels”. Eight hits: `Module.DirectLimit.lift_injective`,
  adic-completion injectivity/flatness, the equational flatness criterion,
  `Module.FaithfullyFlat`, `LinearMap.lTensor_injective_of_exact_of_flat`, and formal
  smoothness flatness. None states the varying-ring eventual four-part conclusion.
- LeanSearch: “A directed system of Noetherian local ring module arrows with flat
  limit target and eventually injective scalar extended source residue fibres has
  eventually injective arrows and flat cokernels”. Eight hits, all concerning
  fixed-ring or additive direct limits (`Module.DirectLimit.lift_injective`,
  `AddCommGroup.DirectLimit.lift_injective`, `ModuleCat.directLimitIsColimit`,
  `DirectLimit.mk_injective`, and direct-limit construction/induction declarations).
  None states the varying-ring eventual flat-cokernel conclusion.
- Loogle: `Module.Flat, IsLocalRing, Function.Injective`: zero hits.
- Mathlib grep: `eventually.*flat|flat.*cokernel|cokernel.*flat` in `RingTheory`: zero hits.
- Project `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for eventual
  injectivity/flat cokernel patterns found the sibling localized-limit theorem and
  the enclosing essentially-finite-presentation theorem, not this stage theorem.
  Their full signatures were read. The prescribed node-id grep in
  `lean/WeilConjectures` returned no hits.

Source checked directly in `literature/stacks-project/algebra.tex`, the whole
`lemma-mod-injective-general` proof (046Y), including its first and final paragraphs,
plus `lemma-colimit-eventually-flat` (00R6). The proof dependencies give 00MO and 00ME.
No statement fault or disputed claim was found. No new nodes or dependency repairs
are necessary. All compiles use the authorized `scompile.py` wrapper.

## Worker verification pass

The dispatcher forbids starting other agents and assigns independent maintainer
review to the delivery. This section records a second pass by the same worker,
not an independent review. I reopened the node and full module, checked each
hypothesis against the correspondence above, and checked all four ordered
conclusion conjuncts. In particular the source-only comparison injectivity is
retained, the target comparison remains unrestricted, the threshold is above i₁,
and no finiteness is imposed on limit modules. The pure-tensor normalization of
Ψ excludes an arbitrary substitute comparison. No change was needed on this pass.

Validation: `scompile.py` compiled the module both as sandbox source and at its
library module name, with no errors or non-sorry warnings.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
