## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleStrictTransformUniversalExact` states
`AlgebraicGeometry.Scheme.Modules.moduleStrictTransform_shortExact_of_universallyShortExact`.
Its only postponed theorem has proof `sorry`. No node statement or dependency list changes.
The auxiliary definition `moduleStrictTransformMap`, recorded in `lean.declarations`, supplies
real canonical maps on the existing strict-transform objects; it introduces no second
strict-transform object and chooses no arbitrary morphism.

Source read: `literature/stacks-project/divisors.tex`, the complete statement and proof of
Tag 080W (`lemma-strict-transform-universally-injective`, lines 9037–9072), and Definition
080D with its preceding notation and warning that the centre is retained. The proof docstring
follows all seven DAG proof steps, including the corrected last element chase: the source's
last two uses of y must read z, or i(z). This source proof typo does not affect the statement.
No STATEMENT-DISPUTED or node fault was found. No repair note for this item was present.

Clause-by-clause correspondence:

- Schemes X and S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The quasi-coherent ideal I on S: `(I : S.IdealSheafData)`. This is Mathlib's compatible
  affine ideal data, whose actual ideal module is the existing `I.toModules`.
- Finite type of I: `[I.toModules.IsFiniteType]`. No flatness, finite presentation,
  Noetherian, separatedness, or regularity hypothesis is added.
- Its blowup and structure morphism: `I.blowup` and `I.blowupMap`, already used by
  `moduleStrictTransform` and by the construction of `moduleStrictTransformMap`.
- The two maps of the original sequence and their zero composite: `C : ShortComplex X.Modules`
  with `C.f`, `C.g`, and `C.zero`; its three terms are `C.X₁`, `C.X₂`, `C.X₃`.
- Quasi-coherence of every term: the three explicit `C.Xᵢ.IsQuasicoherent` instances.
- The original sequence is short exact: `(hC : C.ShortExact)`. Mathlib's `ShortExact`
  combines exactness with a mono first map and epi second map, encoding both zero endpoints.
- Every base change T -> S: `hbase : ∀ (T : Scheme.{u}) (t : T ⟶ S), ...`.
  The test schemes use the same arbitrary universe as X and S, rather than an independent
  smaller universe. There is no property imposed on t.
- The scheme X ×_S T and its map to X: `pullback f t` and `pullback.fst f t`.
- Extension-of-scalars pullback on both sequence maps: `(tensorPullback (pullback.fst f t)).map`.
  The existential `w` records that these two maps compose to zero; the following
  `(ShortComplex.mk ... w).ShortExact` gives precisely the required base-changed short exact
  sequence. The existential concerns only a proof of equality, not a choice of sequence maps.
- The strict-transform terms on X ×_S Sᵇ: the domain and codomain of each
  `moduleStrictTransformMap f I C.f` and `moduleStrictTransformMap f I C.g` are exactly the
  existing `moduleStrictTransform f I C.Xᵢ` objects, over `pullback f I.blowupMap`.
- The induced maps: `moduleStrictTransformMap` applies `kernel.map` to the naturality square
  of the open restriction adjunction unit, then `cokernel.map` to the kernel inclusions.
  Its commutativity proofs are existing `unit.naturality` and `kernel.lift_ι`, with the
  appropriate symmetry. Thus the resulting map is the map on quotients induced by the
  tensor pullback, retaining the centre I. This helper is part of the current theorem's
  induced-map interface and has its source and blueprint docstring in the same module.
- The conclusion: `∃ w : ... = 0, (ShortComplex.mk ... w).ShortExact` asserts a zero
  composite and exactness with a mono first map and epi second map for these very maps.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: its module docstring identifies
  quasi-coherence and finite type with `SheafOfModules.IsQuasicoherent` and `IsFiniteType`;
  coherent modules are not needed here. Read using `scompile.py --source` because this
  recorded module is absent in the old source checkout.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: the full signatures and bodies of
  `moduleStrictTransformOpen`, `moduleStrictTransformRestriction`, `moduleStrictTransformKernel`,
  and `moduleStrictTransform`. The existing restriction unit and quotient are used literally.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` and
  its object and map definitions. Read the current source through `scompile.py --source`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  and `pullback.snd`; scheme pullbacks are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels`: `kernel.map`, `kernel.lift_ι`, and
  `cokernel.map`, read in full; `Mathlib.Algebra.Homology.ShortComplex.ShortExact` supplies
  the existing meaning of short exactness, also read in full.

All recorded proof-dependency modules are imported non-publicly, including tensor pullback
quasi-coherence, blowup principalization, affine-open basis, tilde adjunction, quasi-coherent
kernels and cokernel/image, open base change, tilde pullback, power torsion/localization and
tilde finite-limit preservation. The fibre-product module is already publicly imported by
the strict-transform dependency. No proof-only import closes an import cycle in compilation.

Edge cases checked mathematically before writing: empty X or S; all zero modules and zero
maps; split exact sequences; unit ideal (identity blowup, empty exceptional locus, unchanged
sequence); zero and nilpotent centres (empty blowup, zero resulting sequence). On local charts,
a unit a has no a-power torsion, whereas a=0 or nilpotent a makes every element power torsion;
both cases give the required quotient exactness. The n=0 reduction is the zero quotient.
No assumption that a is regular on the chart ring or on any module occurs. As a check on the
universal hypothesis, the nonsplit sequence Z --2--> Z -> Z/2 is exact but ceases to be
left exact after tensoring with Z/2, so it is correctly excluded by `hbase`.

Searches made for existing statements and maps:

- `msearch.py`, LeanFinder: “Strict transforms of universally exact short exact sequences of
  quasi coherent modules remain short exact”. Eight hits concern exactness of localizations,
  Mayer–Vietoris or snake-lemma complexes; none concerns module strict transforms.
- `msearch.py`, Loogle: `"strictTransform"`. Zero hits.
- `msearch.py`, Mathlib grep: `strictTransform|strict_transform`. Zero hits.
- `msearch.py`, LeanSearch: “Strict transforms of universally exact sequences of quasi
  coherent modules under blowup are short exact”. Eight hits include `ShortExact.exact`,
  `IsLocalizedModule.map_exact`, `LocalizedModule.map_exact`, `IsSMulRegular.smulShortComplex_shortExact`,
  `Module.Flat.lTensor_shortComplex_exact`, `Module.Flat.rTensor_shortComplex_exact`,
  `Module.Flat.iff_rTensor_preserves_shortComplex_exact`, and `ShortExact.mk'`; no match.
- `rg` in upstream `WeilConjectures` for `strictTransform|strict_transform`: hits describe
  strict transforms of schemes in blowup/compactification modules, not module transforms.
  Searching the item id in that tree gives no hit.
- `rg` in `lean/Sheaf` for these patterns and `moduleStrictTransform`: the existing module
  defines the four object/restriction/kernel declarations but gives neither induced module
  maps nor the exactness theorem. Other strict-transform hits concern schemes or unrelated
  categorical strict transformations.
- `rg` for `moduleStrictTransformMap|moduleStrictTransform_shortExact` in upstream, side
  sources, and `dag/lean_names_upstream.json`: no pre-existing declaration.
  The upstream name index records the blowup and scheme strict-transform notions only.

Validation: the prescribed `scompile.py Q144 lem-trf-strict-transform-universal-exact`
compiled this file in both sandbox and library modes, with no errors or warnings
(11.9 s and 10.1 s respectively). All universes and variables are bound explicitly;
there are no temporary `#check` commands, file-local notation or local instances.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
