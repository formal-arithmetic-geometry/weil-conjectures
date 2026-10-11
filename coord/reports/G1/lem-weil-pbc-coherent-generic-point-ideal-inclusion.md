## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion` states the
Stacks 01YE assertion.  The binders `[IsNoetherian X]`, `[IsClosedImmersion i]`,
and `[IsIntegral Z]` render the Noetherian scheme, closed immersion, and integral
closed subscheme hypotheses.  `F : X.Modules` and `hF` render a coherent
O_X-module.  `genericPoint Z` is the unique generic point, and `i.base` gives
ξ.  `hkill` says every scalar in the maximal ideal of O_{X,ξ} acts by zero on
the
additive-group stalk of F at ξ.  The conclusion quantifies `r : ℕ` and an
ideal-sheaf datum `I : Z.IdealSheafData`; `I.toModules` is the coherent ideal
sheaf, `∐ fun _ : Fin r => I.toModules` is its r-fold direct sum (including
r = 0), and `(pushforward i).obj` is i_*.  `Mono α` is injectivity.  The open
`W` contains ξ and `IsIso ((SheafOfModules.overFunctor ... W).map α)` is the
restriction being an isomorphism.

Dependency declarations used: `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (Mathlib.AlgebraicGeometry.Scheme),
`AlgebraicGeometry.IsLocallyNoetherian`/`AlgebraicGeometry.IsNoetherian`
(Mathlib.AlgebraicGeometry.Noetherian), `AlgebraicGeometry.IsClosedImmersion`
(Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion),
`AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties),
`TopologicalSpace.IsIrreducible` and `genericPoint` (Mathlib topology),
`AlgebraicGeometry.RingedSpace.IsCoherent`
(Sheaf.AlgebraicGeometry.Coherent),
`AlgebraicGeometry.Scheme.residueField` (Mathlib.AlgebraicGeometry.ResidueField),
`SheafOfModules` (Mathlib.Algebra.Category.ModuleCat.Sheaf), and
`AlgebraicGeometry.Scheme.Modules.tensorPullback`
(Sheaf.AlgebraicGeometry.TensorPullback).  The ideal-sheaf carrier and inclusion
are Mathlib/source declaration `Scheme.IdealSheafData.toModules` and
`toModulesι` from `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`.

Edge cases checked: `r = 0` is permitted by `Fin r` and the empty coproduct;
`I = ⊥` is allowed; the generic point and maximal ideal are used without
assuming ξ is closed; no finite-type or separated hypothesis was added.

Searches made: `msearch.py leanfinder` for “coherent module killed by maximal
ideal generic point ideal sheaf” (no exact match); `msearch.py loogle` for
`genericPoint, IdealSheafData, toModules, IsCoherent` (only the Mathlib ideal
sheaf and generic-point declarations); grep of Mathlib for `genericPoint`,
`IdealSheafData.toModules`, and `IsCoherent` (no theorem matching 01YE); rg of
`WeilConjectures/` and `lean/Sheaf` for `coherent_generic_point_ideal_inclusion`
(no existing declaration).  The exact statement module compiles cleanly with
`scompile.py`; the expected `sorry` warning is suppressed by project options.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, each source hypothesis is present exactly
once: Noetherian X, closed immersion i, integral Z, coherent F, and annihilation
by the maximal ideal at `i (genericPoint Z)`.  The conclusion has precisely the
integer, coherent ideal sheaf, injective pushforward map, and neighbourhood
isomorphism clauses.  The direct sum is represented by the categorical finite
coproduct and restriction by `overFunctor`; no clause is weakened or omitted.
The module imports the recorded coherent and tensor-pullback declarations and the
recorded Mathlib ideal-sheaf bridge, with no private duplicate definitions.

## Second reading by G1

Independent reading of the sandbox node and Lean file against Stacks 01YE,
`coherent.tex`, lines 2981–3062, label `lemma-prepare-filter-irreducible`.
The repository literature checkout is absent on this machine; I read the local
Stacks checkout `/home/ubuntu/c1-stacks-review/coherent.tex`, including its
introduction, and checked `tags/tags`: 01YE is exactly this label. The lemma
introduces all its assumptions; there is no ambient base field, characteristic,
separatedness or finite-type hypothesis. No statement correction is needed.

Object/hypothesis/conclusion list, with the Lean rendering and verdict:

1. A scheme X, Noetherian (locally Noetherian and quasi-compact):
   `{X Z : Scheme.{w}} [IsNoetherian X]`. Exact: I opened Scheme and
   Noetherian; `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`.
2. An integral closed subscheme i : Z → X:
   `(i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]`. Exact: I opened
   ClosedImmersion and Properties. The former is a closed embedding with
   surjective stalk maps; the latter includes nonemptiness and domain sections
   on nonempty opens, equivalent to the node's affine-local definition.
   There is no additional Noetherian assumption on Z.
3. The generic point η of Z and its image ξ: `genericPoint Z` and
   `i.base (genericPoint Z)`. Exact: `genericPoint_spec` in Topology/Sober
   gives the closure of the singleton as the whole space; scheme sobriety and
   integrality supply its instances. Choosing the unique generic point rather
   than quantifying over it loses no case.
4. A coherent O_X-module F: `(F : X.Modules)` and
   `hF : RingedSpace.IsCoherent X.toRingedSpace F`. Exact: I opened the
   recorded `Sheaf.AlgebraicGeometry.Coherent` definition. It is finite type
   with finite-type kernels for maps from finite free modules on every open,
   exactly pqf-def-coherent. `Scheme.Modules` is the recorded `SheafOfModules`
   category, whose morphisms are O-linear.
5. The stalk F_ξ killed by m_ξ: `hkill`, quantifying over each ring-stalk
   scalar a, its membership in `IsLocalRing.maximalIdeal`, and each additive
   stalk element x, with `a • x = 0`. Exact: I opened the recorded
   ModuleCat/Stalk instance and `germ_ringCat_smul`; this is the canonical
   module-stalk action, not an arbitrary action on the additive stalk.
   The ring is the same local ring used by `Scheme.residueField`, whose
   recorded definition is its quotient by that maximal ideal.
6. An integer r ≥ 0: `∃ (r : ℕ)`. Exact, including zero.
7. A coherent ideal sheaf I contained in O_Z: `∃ (I : Z.IdealSheafData)`
   with `RingedSpace.IsCoherent Z.toRingedSpace I.toModules`. Exact on the
   Noetherian Z: coherent ideals are quasi-coherent, hence represented by
   affine-local ideal data. I opened the existing source bridge
   `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules`
   is the kernel of O_Z → (subschemeι)_* O, with `toModulesι` a monomorphism;
   `range_toModulesι_app` identifies affine sections with the specified ideals.
   Thus containment is built into the carrier, without a hollow definition or
   a private copy. No nonzero or generically unit condition is added.
8. An O_X-linear injection from i_*(I^{⊕ r}) to F:
   `∃ (α : (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⟶ F),
   Mono α`. Exact: a finite categorical coproduct is the finite direct sum;
   monomorphisms in this category are injections of sheaves. I opened the
   Mathlib `Scheme.Modules.pushforward` definition and its section formula
   `pushforward_obj_obj`: sections on U are sections on i⁻¹(U), with the
   induced O_X-action. This is the pushforward in def-pc-module-pullback;
   the lemma has no pullback term.
9. An ambient open neighbourhood W of ξ where α is an isomorphism:
   `∃ (W : X.Opens), i.base (genericPoint Z) ∈ W ∧
   IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map α)`.
   Exact: I opened `overFunctor` in Sheaf/PushforwardContinuous and
   `Scheme.Modules.overFunctorEquiv`, which identifies it with restriction
   to the open subscheme. W lives in X, not merely in Z. The existentials
   have the same order r, I, α, W as the node.

Edge cases: Fin 0 is allowed, so the empty sum is the zero module; for F = 0
one can take r = 0 and W = ⊤. The zero ideal is not excluded (the worker's
notation I = ⊥ describes zero ideals on affine opens). If F_ξ = 0 but F is
nonzero elsewhere, r = 0 is compatible with coherent local vanishing near ξ.
An empty Z is already excluded by the source's integrality; an empty X cannot
contain a nonempty integral Z via a closed immersion. No new nonemptiness
condition is imposed. The generic point need not be closed. There is no
characteristic restriction. The arbitrary bound universe w covers schemes
and their ordinary module sheaves; there is no independent test universe or
unbound variable. No hypothesis requires a base field or extra finiteness.

Independent searches (different phrasing from the first worker):

- `msearch.py leanfinder`: “Noetherian scheme coherent sheaf generic stalk
  annihilated ideal injective finite direct sum”. Eight hits concern germ
  injectivity/SpreadingOut and FunctionField, not the desired module theorem.
- `msearch.py loogle`: `IdealSheafData.toModules`. The Mathlib-only service
  reports an unknown identifier; the source declaration was opened directly
  instead, as above.
- `msearch.py leansearch`: “A coherent sheaf on a Noetherian scheme contains
  a finite direct sum of ideal sheaves supported on an integral closed
  subscheme isomorphically near its generic point”. The service returned
  Internal Server Error; its unavailability is recorded, not an absence claim.
- `msearch.py grep`: `coherent.*generic|generic.*coherent|prepare.filter.irreducible|01YE`:
  no Mathlib hits. Independent rg of the same expressions over
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found related
  generic-stalk and filtration material but no existing theorem for 01YE.
  The existing source ideal-sheaf bridge was reused, not redefined.

Mismatches repaired: H8/H9, the file lacked the standard copyright header and
module source docstring; added both. H8, the theorem's three-line proof sketch
omitted most of the node proof; replaced it with all seven steps and their
named dependencies, including the omitted injectivity argument and the ambient
neighbourhood construction. Removed the unused TensorPullback import: this
statement uses Mathlib's pushforward, not tensor pullback. No signature, node
statement, hypotheses, conclusions, or dependency records changed. There are
no new definition nodes or dependency modules in this delivery. The only proof
is the named theorem's `sorry`; no definition is hollow and nothing is proved.

Validation: scompile.py compiled the repaired module on the server in 1.9 s,
exit code 0, without warnings. All lines are at most 100 characters. I checked
that `lean.statement` is verbatim the signature from `theorem` up to `:=`.
