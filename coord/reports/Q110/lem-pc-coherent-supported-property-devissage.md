## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentSupportedPropertyDevissage` states
`AlgebraicGeometry.Scheme.Modules.coherent_supported_property_devissage` with a
single `sorry` proof. No definition, dependency record, or mathematical statement
is changed. No new nodes are needed. No STATEMENT-DISPUTED issue was found.

Source checked: `literature/stacks-project/coherent.tex`,
`lemma-property-initial` (01YG) and the supported filtration paragraphs of
`lemma-property-irreducible` (01YH). Also read the current blueprint's
`literature/blueprint/latest/blueprint/sec-picard-framework/sk-prop-picard-pic-split/lem-pc-coherent-hi.md`
and its proof: this supported criterion is a tool for the support induction in the
proper coherence theorem, not a change to that unit's statement.

Clause-by-clause statement correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A scheme X | `(X : Scheme.{u})` |
| Locally Noetherian and quasi-compact | `[IsNoetherian X]`, whose Mathlib class extends precisely `IsLocallyNoetherian X` and `CompactSpace X` |
| Any subset S, not necessarily closed | `(S : Set X)`, with no closedness binder |
| Sheaves of O_X-modules | `X.Modules`, Mathlib's specialization of `SheafOfModules` to `X.ringCatSheaf` |
| Support defined by nonzero module stalks | `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}` throughout; the underlying group of the existing module stalk is used |
| A property of coherent modules supported in S | `(P : X.Modules → Prop)`, with coherence and support guards at every use of the restricted property |
| Property of zero | `hP_zero : P (0 : X.Modules)` |
| Invariance under isomorphisms between these modules | `hP_iso`, quantifying over `F G`, an isomorphism `_e : F ≅ G`, both coherence hypotheses, both support containments, then `P F → P G`; the reverse implication follows by swapping F,G and the inverse iso |
| Every short exact sequence | `∀ T : ShortComplex X.Modules, T.ShortExact → ...` in `hP_extension` |
| All three terms coherent | The separate `RingedSpace.IsCoherent X.toRingedSpace T.X₁`, `T.X₂`, `T.X₃` premises |
| All three terms supported in S | Three separate stalk-support containment premises in `hP_extension` |
| Property of first and third implies property of middle | `P T.X₁ → P T.X₃ → P T.X₂` |
| Every closed immersion from integral W | `∀ (W : Scheme.{u}) (j : W ⟶ X), IsClosedImmersion j → IsIntegral W → ...` |
| Its image is contained in S | `Set.range j.base ⊆ S` |
| Every nonzero quasi-coherent ideal | `∀ J : W.IdealSheafData, J ≠ ⊥ → ...`; ideal data are the existing localization-compatible affine ideals encoding quasi-coherent ideals, not arbitrary module subobjects |
| Property of the module pushforward of J | `P ((pushforward j).obj J.toModules)` |
| Conclusion for every coherent F supported in S | Final `∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → {x : X ...} ⊆ S → P F` |

Extending the restricted property to the ambient module category is harmless:
only coherent supported inputs are constrained or concluded. Ideal pushforwards
in the hypothesis are coherent and supported in S by Noetherianity and the closed
immersion condition, as in the source. No extra coherence premise was added to
that hypothesis. Quasi-coherence of the ideals is part of `IdealSheafData` rather
than a stronger coherence assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`
  and `LocallyOfFiniteType.isLocallyNoetherian`. The scheme-conventions node is
  explicitly a convention record, not a missing definition requiring a new module.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent alias for Mathlib's `SheafOfModules`; `X.Modules` is its existing
  scheme specialization.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, with stalk carrier `F.presheaf.stalk x`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the node's recorded module;
  its `Scheme.Modules.IsQuasiCoherentFiniteType` is not substituted for coherence.
  The precise `RingedSpace.IsCoherent` is publicly imported directly from
  `WeilConjectures.AlgebraicGeometry.Coherent` as well: the compile snapshot did
  not yet expose that name through the freshly updated recorded module.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  module-pullback interface and its public upstream module; its pushforward is
  Mathlib's `Scheme.Modules.pushforward`, used literally here.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, the kernel construction giving the ideal
  sheaf, and the existing `W.IdealSheafData` from Mathlib.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ShortComplex.ShortExact`.

All recorded proof dependencies are imported privately when not already public:
`WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes`
(`exists_coherent_filtration_integral_subschemes`),
`WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum`
(`RingedSpace.coherent_kernel_cokernel_sum`),
`WeilConjectures.Algebra.Homology.ModuleStalkExact`
(`RingedSpace.module_stalk_exact`),
`WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk`
(`Scheme.integral_ideal_generic_stalk`),
`WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks`
(`closedImmersion_pushforward_stalks`),
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
(`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`), and
`WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
(`Scheme.Modules.finite_type_module_support_closed`). Closed immersions and
local-Noetherian permanence are already covered by public Mathlib imports.
The theorem docstring reproduces the node's four-step proof and their uses.

Edge cases checked before finalizing the statement:

- Empty X: the integral-source test can be vacuous, but `hP_zero` and
  isomorphism invariance still supply the conclusion for every zero module.
- Empty S: every allowed F has zero stalks and is zero; no existence of an
  integral subscheme is required. This explains retaining the explicit zero base.
- F = 0 and a length-zero filtration: covered directly by `hP_zero` and iso
  invariance. The theorem does not infer P(0) from extension closure alone.
- S = all of X: recovers the initial filtration criterion with its explicit
  zero and isomorphism hypotheses.
- S is only the generic point of the affine line: S need not be closed; only
  zero coherent modules have support inside S, so the integral tests can be
  vacuous without making the conclusion false.
- Nonreduced X, e.g. Spec(k[epsilon]/epsilon^2), remains allowed. The filtration
  has integral closed factors; X itself is not required to be integral or reduced.
- J is excluded exactly when it is the zero ideal (`J = ⊥`). The unit ideal is
  included. No nonempty integral-source hypothesis is separately imposed:
  `IsIntegral W` already includes it.
- All schemes and their module stalks use the standard common project universe
  `u`, explicitly bound. There are no auto-bound implicits or local aliases.

Searches (using the prescribed `msearch.py Q110 <item>` wrapper):

- LeanFinder: `Noetherian scheme coherent sheaf supported in a subset extension closed property devissage using ideals on integral closed subschemes`.
  Eight hits on ideal-data constructors/support, local Noetherianity and qcqs
  sections; none gives the stated property criterion.
- Loogle: `AlgebraicGeometry.Scheme, "coherent"`.
  One hit, `Scheme.Modules.isQuasicoherent_restrictFunctor`, only preservation
  of quasi-coherence under open restriction, not property devissage.
- Mathlib grep: `devissage|dévissage|coherent.*filtrat|filtrat.*coherent`
  in `AlgebraicGeometry`; no hits.
- LeanSearch: `An extension closed property of coherent sheaves supported in a subset of a Noetherian scheme holds if it holds for nonzero ideals on integral closed subschemes`.
  Eight ideal-data support/zero-locus hits. Read their underlying definition:
  `IdealSheafData.support` is the closed zero locus, not module support, and no
  returned declaration matches this statement. Search-service glosses identifying
  it with nonzero ideal stalks are incorrect and were not used.
- Project `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `supported.*[Pp]roperty|[Pp]roperty.*[Dd]evissage|coherent.*[Dd]evissage`.
  Read `CoherentPropertyDevissage`, `CoherentPropertyIrreducible`, and the upstream
  `CoherentPropertyDevissageIntegralSubschemes` interfaces. These require different
  two-out-of-three, summand, or generic-witness hypotheses; none is the arbitrary
  support, extension-only criterion of this node.
- `grep -rn 'lem-pc-coherent-supported-property-devissage' lean/WeilConjectures`:
  no hits. `rg -n 'coherent_supported_property_devissage'` in both project roots
  and Mathlib: no existing declaration.

## Second reading by Q110

A separate worker was not started, as the dispatcher explicitly forbids other
agents. This section records the delivering worker's second pass with the node
and module open; the maintainer supplies the independent delivery review.

Rechecked every correspondence in the table. In particular, the source's arbitrary
S is retained, both coherence and support guards restrict the isomorphism and
extension hypotheses, extension closure only uses the two end terms, and the
integral test includes every nonzero quasi-coherent ideal. The module uses the
actual coherence predicate and actual stalk support, not quasi-coherence alone
or the ideal zero locus. There is an explicit P(0) base, and no properness,
separatedness, reducedness, integrality, or closedness requirement on X or S.

The first compile revealed that the published recorded coherence module did not
publicly expose `RingedSpace.IsCoherent`, that object zero notation needs the
`ZeroObject` namespace, and that the isomorphism premise needed an explicit
binder. Added the direct public coherence import, opened `ZeroObject`, and bound
`_e : F ≅ G`; these are elaboration fixes with no mathematical change. The final
node copy changes only `lean`, with the signature read literally from the file.

Validation: the prescribed `scompile.py Q110
lem-pc-coherent-supported-property-devissage <module-file>` passed both its
sandbox compile (13.4 s) and library-path compile (8.4 s), with no errors or
unexpected warnings. All Lean lines are at most 100 characters. The theorem's
only postponed proof is the whole `by sorry` body.
