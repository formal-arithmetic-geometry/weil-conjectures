## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel` states
`moduleStrictTransform_properties` and `moduleStrictTransform_structureSheaf`.
Both proofs are `sorry`; no mathematical assertion is proved in this delivery.
Two real helper definitions name the canonical quotient and its structure-sheaf
specialization. These are constructions belonging to this node, recorded in
`lean.declarations`, rather than new independent notions.

Hypothesis and clause correspondence:

- Schemes S and X and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The closed centre Z with its quasi-coherent defining ideal: `(I : S.IdealSheafData)`.
  IdealSheafData encodes a quasi-coherent ideal and its associated closed subscheme.
  Finite type is `[I.toModules.IsFiniteType]`. No finiteness, separation, or
  quasi-compactness assumption is imposed on X, S, or f.
- The blowup b is `I.blowupMap`, with domain `I.blowup`.
- The fibre product and p are `Limits.pullback f I.blowupMap` and
  `pullback.fst f I.blowupMap`. The tensor pullback is `tensorPullback p`.
- The quasi-coherent module is `(F : X.Modules) [F.IsQuasicoherent]`.
- Its strict transform is the dependency's `moduleStrictTransform f I F`.
- The canonical quotient is `moduleStrictTransformπ`, defined as the cokernel
  projection of the existing supported-kernel inclusion, with no arbitrary map input.
  Sheaf surjectivity is `Epi (moduleStrictTransformπ f I F)`, not surjectivity on
  sections of every open (which is not the meaning of a surjective sheaf map).
- The kernel clause quantifies over every open V and pullback section s:
  `π.app V s = 0 ↔ (moduleStrictTransformRestriction f I F).app V s = 0`.
  The dependency restriction map is the actual open-restriction/direct-image unit;
  its vanishing means that s vanishes on V intersected with the complement of
  `(f ∘ p)⁻¹ Z`. Its kernel is `moduleStrictTransformKernel f I F`.
- Quasi-coherence of the kernel and quotient are the two explicit
  `.IsQuasicoherent` conjuncts.
- The isomorphism off the centre is `IsIso ((restrictFunctor j).map π)`, where
  `j = (moduleStrictTransformOpen f I).ι` is the complement inclusion.
- Absence of supported local sections quantifies over every V and strict-transform
  section s; vanishing under the same restriction/direct-image unit implies `s = 0`.
- For F = O_X, `moduleStrictTransformStructureMap` precomposes π by the inverse
  of the canonical tensor-pullback structure-sheaf map. Its `IsIso` proof is supplied
  explicitly by the existing `tensorPullbackObjUnitToUnit_isIso`, not a new assumption.
- The structure-sheaf kernel is stated on every open as membership in
  `(I.strictTransformι f).ker.idealOfOpens V`. This is the defining ideal of the
  existing scheme strict transform, with its actual closed immersion.
- The final existential is an isomorphism of module sheaves from O_X^st to
  `(pushforward (I.strictTransformι f)).obj (SheafOfModules.unit ...)`.
  The equation `moduleStrictTransformStructureMap f I ≫ e.hom =
  SheafOfModules.unitToPushforwardObjUnit ...` specifies compatibility as quotients
  of O_(X ×_S S'), not merely an unrelated isomorphism.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the closed centre is represented by its ideal,
  and the strict-transform immersion comes from the existing specialization below.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: the docstring explains that the
  quasi-coherent and finite-type predicates of pqf-def-coherent are Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`; the coherent
  predicate itself is not required here. Read through `scompile.py --source` because
  this newer upstream module is absent from the older checkout.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: all four recorded declarations,
  namely `moduleStrictTransformOpen`, `moduleStrictTransformRestriction`,
  `moduleStrictTransformKernel`, and `moduleStrictTransform`.
- `WeilConjectures.Compactification.StrictTransform`: `AlgebraicGeometry.strictTransform`
  and the existing centre-retaining specializations `I.strictTransform f`,
  `I.strictTransformι f`. The latter is the closed immersion into the fibre product.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`; the Scheme pullback instance is already imported.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit`, `tensorPullbackObjUnitToUnit_isIso`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.isQuasicoherent_unit` supplies the existing unit-sheaf instance.
- Existing proof modules are imported non-publicly: Modules.Tilde,
  Modules.QuasicoherentKernel, Modules.QuasiCoherentCokernelImage,
  QuasicoherentPushforwardQcqs, Blowup.Principalization. Their interfaces supply the
  pullback, kernel, cokernel, pushforward and principalization proof inputs in the DAG.
  Unstated proof dependencies have no module to import.

Edge cases checked before writing: I = top (empty centre) gives the original
pullback and zero supported kernel; I = bottom (centre is all S) gives an empty
blowup/fibre product and hence zero module sheaves. F = 0 and X empty are included.
No nonemptiness, Noetherianity, flatness, or qcqs restriction on f was introduced.
An arbitrary open V is used in both support tests, so the result asserts local
vanishing everywhere, not only vanishing of global sections. Universe u is explicit
and agrees with the dependency's scheme/module universes.

Source read: `literature/stacks-project/divisors.tex`, Section Strict transform,
paragraph preceding `definition-strict-transform` and clauses (1), (2), together
with the node's four-step proof and its source references. The existing scheme
transform is scheme-theoretic image, so the structure comparison preserves the
scheme structure, not just the topological closure.

Searches for an existing statement (msearch.py, group Q14 and this item):

- LeanFinder: "The strict transform of a quasi-coherent sheaf is the quotient of
  pullback by sections supported on the exceptional divisor and equals the structure
  sheaf of the scheme strict transform". Eight hits about normalization and ideals;
  no strict-transform sheaf statement.
- Loogle: `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform`. Unknown identifier;
  this dependency is a side-project definition, not a Mathlib theorem.
- Mathlib grep: `moduleStrictTransform|strict.transform.*kernel|strictTransform.*[Ss]heaf`
  in AlgebraicGeometry. No hits.
- LeanSearch: "strict transform quasi-coherent sheaf quotient supported sections kernel".
  Eight hits concerning scheme ideal kernels and quasi-coherence; no matching result.
- `rg` for the same pattern in upstream WeilConjectures and side lean/Sheaf:
  only scheme strict-transform comparisons and the existing four module definitions.
- `grep -rn` for this item id in upstream WeilConjectures: no hits.
- `rg` for each proposed declaration name in upstream, side-project Lean and
  dag/lean_names_upstream.json: no hits.

No statement correction, disputed assertion, new DAG node, or dependency repair.

## Second reading by Q14

The dispatcher explicitly forbids spawning other agents. This is the worker's
second pass over the node and module; independent review is supplied by the maintainer.
I checked each hypothesis and clause against the correspondence above. The two
support clauses quantify over every open and use the canonical restriction unit.
The kernel in the structure-sheaf clause is the actual strict-transform ideal,
and the final isomorphism commutes with the quotient maps. No extra hypotheses
or omitted conclusions were found. Compilation exposed the module-pullback name
collision with the categorical pullback, repaired by qualifying `Limits.pullback`,
and the need to pass the existing quasi-coherent unit proof explicitly. The structure
map uses explicit `Scheme.Modules.Hom.app` to select the section-map interface
through the definitionally equivalent underlying SheafOfModules Hom type.

Validation: `scompile.py Q14 lem-trf-strict-transform-sheaf-kernel
lean/Sheaf/AlgebraicGeometry/ModuleStrictTransformKernel.lean` succeeded for both
sandbox and library-path compilation with no warnings or errors (14.9 s and 8.6 s).
