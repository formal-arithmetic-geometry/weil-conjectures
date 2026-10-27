## Worker report

The new module `Sheaf.AlgebraicGeometry.FibrewiseModuleFlatnessCriterion` states
`AlgebraicGeometry.Scheme.Hom.module_flatAt_and_base_flatAt_of_fiber_module_flatAt`.
Its only theorem has proof `by sorry`; there are no new definitions. The node changes
only in `lean`. No statement correction, new node, dependency repair, or disputed
statement is needed.

Source checked: `literature/stacks-project/more-morphisms.tex`, lines 4589–4635,
Tag 039C, `theorem-criterion-flatness-fibre`. The statement is exactly its implication
(1) to (2), with the two conclusions ordered as in this DAG node. The converse and
openness assertion are outside this node. I also read the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`;
this supporting criterion lies below its proper-direct-image argument, as recorded
by the accepted stage-1 split.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes S, X, Y | `{S X Y : Scheme.{u}}`, for explicitly declared arbitrary universe `u` |
| p : X → S, q : Y → S, f : X → Y | `(p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)` |
| q ∘ f = p | `(hf : f ≫ q = p)` |
| p locally of finite presentation | `[LocallyOfFinitePresentation p]` |
| q locally of finite type | `[LocallyOfFiniteType q]`; no quasi-compactness assumed |
| F an O_X-module | `(F : X.Modules)` |
| F quasi-coherent | `[SheafOfModules.IsQuasicoherent.{u} F]` |
| F of finite presentation | `[SheafOfModules.IsFinitePresentation.{u} F]` |
| x ∈ X | `(x : X)` |
| y = f(x), s = p(x) | The actual terms `f x`, `p x` throughout |
| F_x ≠ 0 | `[Nontrivial ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)]` |
| X_s and i_s | `p.fiber (p x)` and `p.fiberι (p x)` |
| The unique fibre point above x | `p.asFiber x`; `p.fiberι_asFiber x` is its projection identity |
| Y_s | `q.fiber (p x)` |
| Induced morphism f_s | `pullback.map p (S.fromSpecResidueField (p x)) q (S.fromSpecResidueField (p x)) f (𝟙 _) (𝟙 S) ... ...`; its first compatibility proof is `(Category.comp_id p).trans hf.symm`, its second is the identity compatibility |
| F_s = i_s* F | `((Scheme.Modules.tensorPullback (p.fiberι (p x))).obj F)` |
| F_x flat over O_{S,s} | `hbase`, `Module.Flat (S.presheaf.stalk (p x))` of the stalk restricted along `(p.stalkMap x).hom` |
| (F_s) at x-tilde flat over O_{Y_s,f_s(x-tilde)} | `hfibre`: coefficient ring `(q.fiber (p x)).presheaf.stalk (f_s (p.asFiber x))`, and restriction of the pulled-back stalk along `(f_s.stalkMap (p.asFiber x)).hom`; f_s is expanded identically in both occurrences |
| F_x flat over O_{Y,y} | First conjunct: `Module.Flat (Y.presheaf.stalk (f x))` of F_x restricted along `(f.stalkMap x).hom` |
| q flat at y | Second conjunct: `(q.stalkMap (f x)).hom.Flat`; this asserts flatness at this point, rather than flatness everywhere |
| Flatness means exactness of tensoring | Mathlib `Module.Flat`, equivalent to tensor preserving injective maps and hence exact sequences; `RingHom.Flat` uses that module predicate |
| All scalar actions induced by the morphisms | Each module is obtained by `ModuleCat.restrictScalars` along the actual displayed stalk map; no arbitrary scalar structures, algebra maps, or compatibility assumptions are introduced |
| No flatness of p; no Noetherian assumption | Neither appears in the signature; hbase is flatness only of F_x |

The coefficient ring in `hfibre` is written explicitly, including f_s(x-tilde), so
there is no equality assumption identifying it with a separately chosen fibre point.
The two pullback compatibility terms are ordinary equality proofs, not postponed
mathematical results. There are no `let` binders or file-local notation/instances.
Both `autoImplicit` and `relaxedAutoImplicit` are false.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `pqf-def-coherent`: its recorded `Sheaf.AlgebraicGeometry.CoherentFiniteType`
  publicly exposes Mathlib `SheafOfModules.IsQuasicoherent`. I use that predicate,
  not the conjunction `Scheme.Modules.IsQuasiCoherentFiniteType`, because the node
  assumes quasi-coherence separately from finite presentation. No coherence or
  extra finite-type hypothesis is inserted.
- `def-weil-pbc-module-finite-type-presentation`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`,
  `SheafOfModules.IsFinitePresentation` (Generators is its public dependency).
- `def-weil-pbc-module-stalk`:
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor`/`stalkObj`, using the sheaf specialization
  `RingedSpace.moduleStalkFunctor` from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`, exactly as the dependency's
  note and the project's MODULE STALKS convention require. Both use the same
  Mathlib stalk carrier and its germ scalar action.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `Scheme.Hom.fiber`, `fiberι`, `asFiber`, and `fiberι_asFiber`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.map` (read its full two-square signature).
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly importing
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, `Scheme.Modules.tensorPullback`.
  This is the real sheafified tensor pullback, not an arbitrary adjoint.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` and its recorded `Flat.iff_flat_stalkMap` characterization;
  pointwise flatness uses `RingHom.Flat` of the stalk map.
- `ModuleCat.restrictScalars`, read in
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, fixes the action as r·m = f(r)·m.

Every recorded proof-dependency module is imported without `public`: compatible
stalk data, finite-presentation stalks, tensor-pullback stalks, quotient tensors,
finite-type local approximation, the closed-fibre criterion, flat ring maps,
Nakayama, and faithfully flat modules. The theorem's docstring contains the node's
five-step proof, retaining the module argument and listing the DAG input ids.
The final kernel cancellation is elementary, exactly as the node records it.

Edge cases checked before writing:

- Empty X has no x, so introduces no false conclusion about an arbitrary y.
- The zero sheaf/stalk is excluded precisely by `Nontrivial`; without it the two
  flatness hypotheses would hold for the zero module even over a nonflat q.
- Nonzero does not mean faithful over C; the proof only derives faithfulness over
  the approximating local ring T using its flatness and Nakayama over C.
- Residue-field bases, identity maps and identity fibre maps are included.
- Finite presentation allows zero generators or relations locally. A nonzero stalk
  is required only at the chosen x; it is not imposed globally.
- Non-Noetherian base/source/target rings are allowed; there is no finite-type
  assumption on M over B or over the approximation T, only over C in the proof.
- A module can be R-flat without C being R-flat. The signature keeps this case.
- q need only be locally of finite type, not locally finitely presented; the
  approximation step, rather than a stronger assumption, handles that distinction.
- The fibre map is evaluated at its actual image, so no extra point equality or
  choice of residue-field lift narrows the statement.
- Universes are explicit and match `Scheme.{u}`, its O_X-modules and stalks. No test
  objects are quantified in a smaller independent universe.

Searches performed using the prescribed `msearch.py Q11 <item>` wrapper:

- LeanFinder: "A finitely presented quasi coherent module with nonzero stalk flat
  over the base and flat on the fibre over the target implies target flatness and
  module flatness". Eight hits: scheme flatness via stalk maps and module faithful
  flatness/base-change descent; none states this module criterion.
- Loogle: `Module.Flat, IsLocalRing`. Eight hits: faithful flatness of flat local
  ring maps, finite flat freeness, length/base-change and formal smoothness;
  none matches the module criterion under these hypotheses.
- Mathlib grep: `criterion.*flat|flat.*fiber|flat.*fibre` in `AlgebraicGeometry`.
  One hit, `Morphisms/SmoothFiber.lean`, is the smooth-fibres criterion, not this theorem.
- LeanSearch: "Fibrewise flatness criterion for a finitely presented quasi coherent
  module nonzero at a point". Eight hits: flatness localization/equational tests
  and scheme stalk criteria; no matching theorem.
- Project `rg`: `fibrewise|flat.*[Ff]ib[er]|[Ff]ib[er].*flat|criterion.*flat`
  in `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`;
  narrowed to `039C|fibrewise_module_flatness|fibrewiseModuleFlatness|fibrewise.*flatness`
  over both full roots. Read `FibrewiseFlatnessCriterion.lean` and
  `RelativeFlatLocusBaseChange.lean`: the former handles only F = O_X, the latter
  assumes the source morphism flat. Neither states the requested module result.
  `PointwiseModuleFlatnessBaseChange.lean` is ascent/reflection under a cartesian
  square, not this criterion; its scalar-restriction encoding agrees with this file.
- `rg -n 'lem-sfb-fibrewise-module-flatness-criterion' lean/WeilConjectures` and
  searches for the proposed declaration in both roots and `dag/lean_names_upstream.json`
  returned no declaration or occurrence.

Validation: prescribed `scompile.py` passed in sandbox and library module mode,
6.4 and 7.7 seconds respectively, with no errors or unexpected warnings. Initial
elaboration failures were repaired by specifying the sheaf universes `.{u}` and
the fibre coefficient ring explicitly; no mathematical hypothesis changed.

## Second reading by Q11

I reopened the node and the final file for a separate clause-by-clause self-review.
The dispatcher explicitly prohibits starting other agents; this is not represented
as an independent worker review. The maintainer supplies the independent review
of this delivery.

The commuting triangle, local finite-presentation/type hypotheses, quasi-coherence,
finite presentation, chosen point and nonzero stalk all match their binders. In
particular `Nontrivial` is on the module stalk, not the structure ring. `hbase` is
module flatness and does not accidentally become `Flat p`. The fibre module uses
`tensorPullback (p.fiberι (p x))`, not an unpulled sheaf or an arbitrary tensor
module. Both appearances of the expanded f_s are identical, with compatibility
proofs supplied by hf. Its actual image point is also the coefficient stalk in
hfibre, so there is no hidden specialization to an assumed equality of points.
The conclusion's first conjunct restricts F_x along f's actual stalk map, and its
second conjunct is flatness only of q's stalk map at f x. The full node and source
have no further conclusion in this forward implication. No mismatch or required
statement correction remained; the only changes from the first draft were the
explicit universes and explicit fibre coefficient ring described above.
