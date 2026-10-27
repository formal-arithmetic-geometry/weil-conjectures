## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedSectionsPushforward` states
`AlgebraicGeometry.Scheme.Modules.supportedSections_pushforward`, with its only
postponed proof `sorry`. The node is unchanged outside `lean`.

Three helper definitions construct exactly the supported subsheaves introduced
in this node, using existing canonical Mathlib constructions:

- `supportedModuleRestriction F V` is `(restrictAdjunction V.ι).unit.app F`.
- `supportedModuleKernel F V` is its categorical kernel in `X.Modules`.
- `supportedModuleInclusion F V` is its canonical kernel inclusion into `F`.

These have real data, with no postponed helper proofs, arbitrary maps or choices
from mere existence statements. They belong to the notion explicitly introduced
by this node and are recorded in `lean.declarations`; no independent missing
notion or extra node is needed. The section formula for the restriction unit is
Mathlib's `restrictAdjunction_unit_app_app`: restriction to the intersection with
`V`. Kernels of module sheaves are computed sectionwise, so its kernel is exactly
the subsheaf defined in the node by zero restriction.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
  Mathlib's quasi-compact-open criterion equals the node's affine-open criterion,
  since affine opens form a compact-open basis. `QuasiSeparated` means that the
  diagonal is quasi-compact, exactly the recorded dependency.
- Closed subset: `Z : TopologicalSpace.Closeds Y`, whose `Z.compl` is the
  complementary open. Bundling a closed set imposes precisely closedness.
- Retrocompact complement: `hZ` says that `(U : Y.Opens) ⊓ Z.compl` is compact
  for every `U : Y.affineOpens`. There is no assumption that `Y` is quasi-compact.
- Quasi-coherent coefficient module: `(F : X.Modules) [F.IsQuasicoherent]`.
  This uses the quasi-coherent clause of `pqf-def-coherent`, without imposing
  its separate finite-type or coherent conditions.
- `K_X` is `supportedModuleKernel F (f ⁻¹ᵁ Z.compl)`; the open is exactly
  `X \ f⁻¹Z`. `K_Y` is `supportedModuleKernel ((pushforward f).obj F) Z.compl`.
- Direct image: the existing `pushforward f` has section module `F(f⁻¹U)`
  and the induced scalar action, as in `pushforward_obj_obj`.
- First conclusion: the first conjunct gives compactness of the intersection of
  `f ⁻¹ᵁ Z.compl` with every affine open of `X`, precisely retrocompactness.
- Next three conjuncts give quasi-coherence of `K_X`, `f_*F` and `K_Y`, in order.
- Equality as actual submodules: the next conjunct quantifies over every open
  `U` of `Y` and equates `LinearMap.range` of the section maps of the direct
  image of the canonical inclusion `K_X ⟶ F` and of `K_Y ⟶ f_*F`.
  These are submodules of the SAME module of sections of `f_*F`, with its
  existing induced action. This retains actual equality, rather than asserting
  an unrelated isomorphism of sheaves. The inclusions are sheaf morphisms, so
  their sectionwise submodules inherit the same ambient restriction maps.
- Final assertion: for every `(H : Y.Modules) (β : H ≅ (pushforward f).obj F)`
  and every `U`, the range of `supportedModuleInclusion H Z.compl ≫ β.hom`
  equals the range of the pushed-forward inclusion of `K_X`. This says exactly
  that the given isomorphism identifies the supported submodule of `H` with
  `f_*K_X`; no quasi-coherence hypothesis on `H` is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`; its imported quasi-compact API supplies
  `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: its public Mathlib
  `SheafOfModules.IsQuasicoherent` interface is used; the finite-type conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` is not substituted for it.
- `Sheaf.CategoryTheory.RingedSiteModules`: the recorded general-site interface
  `CategoryTheory.ringedSiteModules` transparently abbreviates `SheafOfModules`.
  The statement uses the existing scheme specialization `X.Modules`, whose
  definition is `SheafOfModules.{u} X.ringCatSheaf`, not a new category.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `pushforward`, `restrictFunctor`,
  `restrictAdjunction`, `restrictAdjunction_unit_app_app`, and the sectionwise
  description of `pushforward` and its action on maps.
- Proof dependency `pqf-lem-pushforward-qcoh` is privately imported from
  `WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`, declaration
  `Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`.
  The Mathlib qcqs-permanence and open-immersion declarations are available
  through the quasi-separated and scheme-module imports. The proof dependency
  `lem-trf-supported-sections-quasi-coherent` has no recorded Lean declaration
  yet, so there is no module to import for it. It is only a proof dependency;
  its conclusion is not assumed or used to define any data here.

Source read: `literature/stacks-project/properties.tex`, the complete 07ZP
statement/proof and 07ZQ statement/proof hint. The node's final beta clause is
the naturality consequence explained in its fourth proof step. The module's
proof docstring preserves all four steps and their named dependencies.

Edge cases checked mathematically: `Z = ∅` gives zero supported subsheaves;
`Z = Y` gives the full ambient sheaves; `X = ∅` gives zero direct images.
The zero module is included. The identity morphism reduces to equality of the
same supported submodule. No nonempty or quasi-compact-base assumption is
introduced. The affine-open tests include empty opens. All universe variables
and term variables are explicit, with `autoImplicit false`; `u` is arbitrary.

Searches for an existing statement/construction (2026-10-24):

- `msearch.py leanfinder`, query “Direct image of a quasi coherent module
  commutes with subsheaves of sections vanishing outside a closed subset”:
  eight results on zero loci, ideal sheaves, restriction and qcqs localization;
  no supported-submodule pushforward theorem for arbitrary modules.
- `msearch.py loogle`, query `SheafOfModules.pushforward, Submodule.map`:
  zero results.
- `msearch.py grep`, query
  `supportedSections|sectionsSupported|supportedSubmodule`: zero results.
- `msearch.py leansearch`, query “Pushforward commutes with subsheaves of
  sections supported on a closed subset of schemes”: eight results giving
  generic direct image and its section formulas; no support comparison.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for supported-section names
  and descriptions: numerous etale/pro-etale constant-coefficient constructions
  and abelian-sheaf constructions, which have different sites or coefficients.
  `ModuleStrictTransform.lean` constructs a kernel for the specialized blowup
  setting only, not the supported module for a general scheme and open.
- Literal node-id search in `lean/WeilConjectures`: no declaration for this item.
- Mathlib inspection found `PresheafOfModules.Submodule` and categorical kernels;
  these are generic tools, not an existing theorem with the node's clauses.
- Exact new-name searches across Mathlib, project source and
  `dag/lean_names_upstream.json` found no conflicting declarations.

Validation: `scompile.py N9 lem-trf-supported-sections-pushforward` compiled
this file successfully in both the private sandbox and its library module form,
with no error or unexpected warning. Dry-run and delivery outcomes follow below.

No statement correction, disputed statement, new node or dependency repair.

The prescribed `deliver2.py --no-push` dry run returned OK: all preflight checks
and per-file compilation passed. The packet contains exactly this module, the
item's Lean-record update, and this report. Independent review is performed by
the maintainer after delivery, as specified by the dispatcher's current brief.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
