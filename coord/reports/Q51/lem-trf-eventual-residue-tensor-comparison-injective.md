## Worker report

The item is stated by
`LocalAlgebraApproximationSystem.eventual_residue_tensor_comparison_injective` in
`Sheaf.TraceFormula.EventualResidueTensorComparisonInjective`.
It asserts `Nonempty (ResidueTensorComparison A)` for every approximation system `A`.
The result record contains all the canonical actions and maps, their pure-tensor
normalizations, all the quotient isomorphisms, the Noetherian and finite-kernel
claims, the localization claims, the group colimit property, and the final uniform
eventual injectivity. The main theorem has only `sorry` as proof. Its docstring
reproduces the seven-step proof plan, including all balancing identifications.
Definitions and structures have actual data and no sorry. No arbitrary comparison
map, localization assumption on the residue diagram, or injectivity assumption is
supplied as a hypothesis. The existential record is the whole conclusion: it is
not a choice of an unspecified isomorphism used to define an object.

The local node had a stage-1 PASS by Q150 but no `lean` or `reviewed_lean` record.
This is a stage-2 statement delivery, leaving the reviewed statement and proof
unchanged. There is no released repair note for the item. Its previous worker's
stage-1-style unchanged-node failure does not apply to this new Lean record.

Hypothesis-by-hypothesis correspondence with the node:

- The small nonempty directed set is `A.I : Type u` with `preorder`, `nonempty`,
  and `directed : IsDirected A.I (· ≤ ·)`. All ring and group carriers and the
  index type are in this same universe, exactly the node's size convention.
- The rings `R_i,S_i` are `A.R.obj i,A.S.obj i` in `CommRingCat.{u}`. The rings
  `R,S` are the specified cocone vertices `A.r.pt,A.s.pt`, not replacement
  rings chosen as some other colimits.
- `stageAlgebra` and `limitAlgebra` supply precisely the maps `φ_i,φ` as their
  `algebraMap`s. `localR`, `localS`, `localLimitR`, `localLimitS`, `stageLocal`,
  and `limitLocal` say the rings and maps are local. Mathlib's `IsLocalHom` is
  equivalent for these local rings to inverse image of maximal ideal equality.
- Ring transitions are `A.R.map (homOfLE h)` and `A.S.map (homOfLE h)`;
  functor identity/composition are exactly the transition laws. `transitionLocalR`
  and `transitionLocalS` impose locality at every comparable pair.
- The cocone maps are `A.r.ι.app i` and `A.s.ι.app i`. Their cocone naturality
  supplies compatibility; `coconeLocalR` and `coconeLocalS` impose locality.
  `square` and `coconeSquare` are the stated commuting algebra squares.
- `colimitR` and `colimitS` use Mathlib `CategoryTheory.Limits.IsColimit` on
  those very cocones. `repR`, `eqR`, `repS`, and `eqS` additionally state the
  element and eventual-equality criteria explicitly required by the node.
- `A.M : A.I ⥤ AddCommGrpCat.{u}` supplies the underlying groups of `M_i` and
  their additive transitions. `stageModule` is their `S_i`-action and
  `finiteStage` is the recorded `Module.Finite` predicate. `baseModule` and
  `baseTower` express restriction through `φ_i`; they add no new mathematical
  action or condition.
- `A.μ.pt` is `M`, `limitModule` is its `S`-action, and `limitBaseModule` with
  `limitTower` is its restricted `R`-action. `semilinear` is the transition
  semilinearity, and `coconeSemilinear` is semilinearity of `μ_i`. The functor
  and cocone laws give all identity, composition and compatibility laws.
  `colimitM : IsColimit A.μ` is the abelian group colimit hypothesis on these
  very maps; hence the action is the induced action stipulated in the node.
- `localization` says that for each comparable pair the canonical tensor ring
  map has a submonoid `W` for which `IsLocalization` holds, with its actual
  algebra structure `g.toAlgebra`. The normalization is
  `g (x ⊗ b) = s_ji(x) * φ_j(b)`. All three localization conditions are
  Mathlib's fields, including zero-divisor denominators. The universal local
  algebra binder is not vacuous: the transition ring homomorphism's
  `RingHom.toAlgebra` always supplies it, with the required algebra-map equality.
  No action is required for incomparable indices.
- `moduleBaseChange` states bijectivity of the actual canonical tensor map as
  an additive equivalence, with `e (x ⊗ b) = b • m_ji(x)`. This is equivalent
  to its being a module isomorphism: this formula forces `S_j`-linearity for
  the usual right-factor action, since pure tensors generate. No arbitrary
  additive equivalence or extra choice can meet a different normalization.
- `essentiallyFiniteType` is `Algebra.EssFiniteType (R_i) (S_i)` at every stage.
- `residueAlgebra` and `residueAlgebraMap` supply precisely the action on
  `k = IsLocalRing.ResidueField R` through `r_i` and the residue homomorphism.
  Every such input diagram has this canonical structure. No extra field
  extension or field embedding is an input.

Conclusion-by-conclusion correspondence:

- `residueField`, `residueTensorRing`, `residueTensorModule`, and
  `limitResidueTensorModule` abbreviate the actual Mathlib objects
  `k`, `S_i ⊗[R_i] k`, `M_i ⊗[R_i] k`, and `M ⊗[R] k`. The order of tensor
  factors is exactly that of the node.
- `stageAction_tmul` specifies `(a ⊗ c)(x ⊗ e) = ax ⊗ ce`; `limitAction_tmul`
  specifies `(a ⊗ c)(x ⊗ e) = s_i(a)x ⊗ ce`. These formulas uniquely
  determine the supplied `Module` structures and imply compatibility along
  `d_ji` by the original cocone identity.
- `d_tmul`, `p_tmul`, and `ψ_tmul` are exactly the three displayed formulas
  defining `d_ji`, `p_ji`, and `Ψ_i`. The field `ψ` is a genuine `D_i`-linear
  map for the specified actions; its kernel is the actual `LinearMap.ker`.
- `noetherian`, `finite`, and `finite_kernel` are respectively
  `IsNoetherianRing D_i`, `Module.Finite D_i P_i`, and
  `Module.Finite D_i (LinearMap.ker (ψ i))` for every index.
- `stageResidueRing` uses the quotient by
  `(maximalIdeal R_i).map (algebraMap R_i S_i)`, exactly `m_i S_i`.
  `stageResidueModule` and `limitResidueModule` use
  `maximalIdeal • (⊤ : Submodule _ _)`, exactly `m_i M_i` and `m M`.
  These are actual Mathlib quotients, not placeholder types.
- `residueFieldAlgebra_map` pins the action of `k_i` on `k` to
  `IsLocalRing.ResidueField.map r_i`. `quotientRingAlgebra_map` pins the
  action on `S_i/m_i S_i` to residue classes of `φ_i`, and
  `quotientModule_smul` pins the action on `M_i/m_i M_i` to residue classes
  of scalar multiplication. The latter is Mathlib's quotient-module action.
- `ringEquiv` with `ringEquiv_tmul` is the requested ring isomorphism
  `D_i ≃ (S_i/m_i S_i) ⊗[k_i] k`, `a ⊗ c ↦ [a] ⊗ c`.
  `moduleEquiv` with `moduleEquiv_tmul` is the requested module identification
  `P_i ≃ (M_i/m_i M_i) ⊗[k_i] k`, `x ⊗ c ↦ [x] ⊗ c`.
  `limitEquiv` and `limitEquiv_tmul` give `P ≃ M/mM`, `x ⊗ [r] ↦ [rx]`.
  The last two are bundled additively with their exact formulas; the formulas
  force linearity for the natural tensor and quotient actions, so these are
  the usual module isomorphisms, not weakened unnormalized bijections.
- `quotientComparison_tmul` is exactly `[x] ⊗ [r] ↦ [r μ_i(x)]`, and
  `comparison_square` states that it corresponds to `Ψ_i` under the two
  module identifications. Since every element of `k` has a residue
  representative, this specifies the map on all pure tensors.
- For any witness `W,g` of the original localization hypothesis, the result's
  `localization` field constructs `θ` with
  `θ(a ⊗ b) = a ⊗ residue(r_j(b))`. It asserts
  `IsLocalization (W.map θ) D_j` for the algebra map `d_ji`, and supplies
  the equivalence from `LocalizedModule (W.map θ) P_i` to `P_j`.
  Its fraction normalization is `x/w ↦ b • p_ji(x)` with
  `d_ji(w) * b = 1`, so `b` is uniquely the inverse of the indicated unit.
  This normalization also forces `D_j`-linearity over the ring localization.
  Quantifying over any witness expresses independence of a chosen witness;
  the node's specified witness is included.
- `compatible` is the comparison cocone equation. `colimit` is its full
  existence-and-uniqueness universal property for homomorphisms into every
  `AddCommGrpCat.{u}` object, exactly the stated underlying group colimit.
- `eventually_injective` says
  `∀ i₀, ∃ i₁, i₀ ≤ i₁ ∧ ∀ j, i₁ ≤ j → Function.Injective (ψ j)`.
  In particular the assertion is uniform at all later indices, for every
  starting index, including equality of the two indices.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `Cocone`,
  `IsColimit`, and `colimit.desc`; filteredness is
  `CategoryTheory.IsFiltered` from `Mathlib.CategoryTheory.Filtered.Basic`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and its pure
  tensors; the universal property and maps are the existing Mathlib API.
- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.mk`, and the existing localization predicate API.
- The main module's proof imports include
  `localization_system_kernel_stabilization` from
  `Sheaf.TraceFormula.LocalizationSystemKernelStabilization` and
  `TensorProduct.exists_unique_colimit_tensor_varying_rings` from
  `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`.
  The Mathlib proof dependencies use `TensorProduct.quotTensorEquivQuotSMul`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`, `TensorProduct.comm`,
  `IsLocalization.tensor`, `IsLocalizedModule.rTensor`,
  `IsLocalizedModule.map_lTensor`, `Algebra.FiniteType.isNoetherianRing`,
  `IsLocalization.isNoetherianRing`, and `Submodule.FG.of_le` in their recorded
  modules. No proof import is omitted for a cycle.

Edge cases checked against the statement and source: singleton index set;
non-antisymmetric directed preorders; empty index set excluded explicitly;
zero modules and empty finite generating sets; transition with zero-divisor
localization denominators; equality indices; a noninjective original local
ring map; arbitrary characteristic; residue classes with different lifts.
Local rings are nontrivial in Mathlib, agreeing with the source's convention.
No Noetherian hypothesis is placed on `R_i`, `S_i`, `R`, or `S`, and no flatness,
finite presentation or injectivity hypothesis has been inserted.

Searches made: msearch LeanFinder for eventual injectivity after tensoring in
local algebra approximation systems returned eight related split-injectivity,
localization detection and residue-map results, none this result. msearch
Loogle `TensorProduct, IsLocalRing.ResidueField, Function.Injective` returned
five fixed-ring local-module criteria, none this result. msearch grep
`eventual.*[Ii]nject|[Ii]nject.*residue|residue.*[Ii]nject` in `RingTheory`
returned 25 related local-module, field and smoothness lines, none this result.
Project `rg` searches for residue comparison/tensor and localization-system
names found the existing stabilization lemma but no copy of this statement;
the exact blueprint id was also absent from `lean/WeilConjectures`.
The new data notion's searches are recorded verbatim by query with their
actual result names in its `mathlib_searches`; LeanSearch and LeanFinder each
returned eight related generic diagram/localization results and no matching
record. Mathlib and project name greps found no approximation-system record;
`blueprint_refs.py search` found zero matching blueprint definitions. Related
approximation lemmas impose other conditions or prove existence of systems,
not this data definition. The source Tag 046Y was read in
`literature/stacks-project/algebra.tex`, lines 32769--32866.

Validation: all three delivered modules compile separately in dependency
order through `scompile.py`, with no errors or warnings. Only stage-2
statements are present; the dependency theorem is retained with its original
sorry. No mathematical statement is disputed or corrected.

## New nodes

`def-trf-local-algebra-approximation-system` defines the complete input
record used above in `Sheaf.TraceFormula.LocalAlgebraApproximationSystem`.
Its source is the first two proof paragraphs of Stacks Tag 046Y; it packages
exactly the item's approximation hypotheses, using the existing Mathlib
colimit, tensor, finite-module and essentially-finite-type notions.
The searches described above found no such record in the DAG, Mathlib, the
upstream project, or the Sheaf project. It has real structure data, no
postponed construction and no proof. The item cites it through `stmt_deps`.

## Dependency modules

`lem-trf-localization-system-kernel-stabilization`: the live source was
retrieved with `scompile.py --source`. Its recorded module begins with legacy
`import` commands, without `module`. The required module-mode consumer was
rejected by Lean with `cannot import non-module
Sheaf.TraceFormula.LocalizationSystemKernelStabilization from module`.
Under §1(B), the delivery preserves the module path, declaration name,
complete signature, proof and docstring, while adding `module`, public
statement imports, the public section, and the recorded Mathlib proof imports.
Only its node's `lean` record changes. This is a format repair of a recorded
proof prerequisite, not a second statement or withdrawal of an existing
result. The repaired module and its actual consumer both compile.
The old signature's existing let-bound localization instances are preserved
verbatim for compatibility; no new let-bound statements were introduced in
the item or new definition.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
