## Worker report

The module `Sheaf.TraceFormula.ElementaryDevissageFinitePresentation` states
`AlgebraicGeometry.Scheme.Modules.elementary_devissage_finite_presentation`, with one
`sorry` and no new definitions. Its source is Stacks Project flat.tex, Tag 057T,
`lemma-devissage-finite-presentation`, read together with Tag 057S,
`lemma-elementary-devissage`. The four proof steps in the node are reproduced in the
theorem docstring. No statement correction or disputed statement is needed.

Hypothesis-by-hypothesis correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S and morphism f locally of finite type | `{X S : Scheme.{u}}`, `f : X ⟶ S`, `[LocallyOfFiniteType f]` |
| Finite-type quasi-coherent F | `F : X.Modules`, `_hF : F.IsQuasiCoherentFiniteType`; this is exactly quasi-coherence conjoined with finite type, not coherence or finite presentation |
| Point x in support of F_s, s=f(x) | `x : X`, `hx : ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x))` |
| Scheme-theoretic fibre X_s and module F_s | Mathlib `f.fiber (f x)` is the pullback along `S.fromSpecResidueField (f x)`; `f.fiberι (f x)` is the first projection, and `tensorPullback` is the recorded module pullback |
| n equals local dimension of the fibre support | `n : ℕ`, `_hn : topologicalKrullDimAt ⟨f.asFiber x, hx⟩ = (n : WithBot ℕ∞)` on the explicitly written subtype of nonzero fibre stalks |
| X', Z', Y', S' affine | Four `Scheme.{u}` binders and four `IsAffine` instances |
| Elementary etale pointed neighbourhood g | `g : X' ⟶ X`, `x' : X'`, `[Etale g]`, `_hg : g x' = x`, `[IsIso (g.residueFieldMap x')]` |
| Elementary etale pointed neighbourhood e | `e : S' ⟶ S`, `s' : S'`, `[Etale e]`, `_he : e s' = f x`, `[IsIso (e.residueFieldMap s')]` |
| f' and fg=ef' | `f' : X' ⟶ S'`, `_hfg : g ≫ f = f' ≫ e` |
| i closed immersion of finite presentation | `i : Z' ⟶ X'`, `[IsClosedImmersion i]`, `[LocallyOfFinitePresentation i]`, `[QuasiCompact i]`, `[QuasiSeparated i]` |
| π finite over S' | `π : Z' ⟶ Y'`, `[IsFinite π]`, `_hπ : i ≫ f' = π ≫ h` |
| h smooth of relative dimension n, geometrically integral fibres | `h : Y' ⟶ S'`, `[SmoothOfRelativeDimension n h]`, `[GeometricallyIntegral h]` |
| Finite-type quasi-coherent G on Z' | `G : Z'.Modules`, `_hG : G.IsQuasiCoherentFiniteType` |
| i_*G is isomorphic to g^*F | `_hiso : Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F)` |
| z' maps to x'; y'=π(z'); h(y')=s' | `z' : Z'`, `_hi : i z' = x'`, use `π z'` directly throughout, `_hs : h (π z') = s'` |
| Singleton fibre of π at y' | `_hfibre : (π ⁻¹' ({π z'} : Set Y')) = {z'}` |
| κ(y')/κ(s') purely transcendental | `_hpure : @Algebra.IsPurelyTranscendentalExtension ...` with the algebra explicitly induced by `(h.residueFieldMap (π z')).hom.toAlgebra`; `_hs` identifies its base field with κ(s') |
| Additional local finite presentation of f | `[LocallyOfFinitePresentation f]` |

Conclusion-by-conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| π of finite presentation | `LocallyOfFinitePresentation π ∧ QuasiCompact π ∧ QuasiSeparated π` |
| F finitely presented near x iff G finitely presented near z' | First `↔`, between `∃ U : X.Opens, x ∈ U ∧ (F.over U).IsFinitePresentation` and the analogous expression for G |
| G finitely presented near z' iff π_*G finitely presented near y' | Second `↔`, with `((pushforward π).obj G).over U` and `π z' ∈ U` |
| F_x finitely presented over O_X,x iff G_z' finitely presented over O_Z',z' | Third `↔`, using `Module.FinitePresentation` of the objects of `RingedSpace.moduleStalkFunctor` |
| G_z' finitely presented over O_Z',z' iff (π_*G)_y' finitely presented over O_Y',y' | Fourth `↔`, with the actual stalk of `(pushforward π).obj G` |

The adjacent pairs of iff statements express each three-way equivalence without
asserting an equivalence between neighbourhood and stalkwise finite presentation.
Restrictions use the existing `SheafOfModules.over` over the open's slice site,
which is the recorded restriction notion for module finite presentation.
All universes are bound explicitly by `universe u`, with `set_option autoImplicit false`.
The canonical module stalk functor supplies its scalar action; no arbitrary scalar
structure or extra algebra hypothesis is introduced. Its already-landed definition
node `def-pc-module-stalk-functor` is added to `stmt_deps` under the §5 permission to
add landed definition nodes. No additional modules or node definitions are needed.

Dependency declarations read and used (directly or through the public imports):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-pc-module-pullback`: `WeilConjectures.AlgebraicGeometry.TensorPullback`, `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-trf-purely-transcendental-extension`: `Sheaf.FieldTheory.PurelyTranscendentalExtension`, `Algebra.IsPurelyTranscendentalExtension`.
- `lem-trf-elementary-module-devissage`: `Sheaf.TraceFormula.ElementaryModuleDevissage`, `AlgebraicGeometry.Scheme.Modules.exists_elementary_module_devissage`.
- `def-weil-pbc-module-finite-type-presentation`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, `SheafOfModules.IsFiniteType`.
- `def-sc-finitely-presented-module`: `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation`.
- `def-pc-module-stalk-functor`: `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`, `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.

The elementary-devissage dependency was read in full. Its displayed output gives
the same fibre dimension, affine schemes, pointed etale maps, commutative triangles,
finite map, singleton fibre and canonical residue-field algebra used here. No private
copy of any construction is introduced. The latest tensor-pullback and module-stalk
sources were retrieved with `scompile.py --source` because their recorded upstream
module paths are absent in the older local source checkout.

For proof dependencies, the already-stated
`WeilConjectures.Mathlib.RingTheory.Finiteness.Descent` is imported non-publicly;
its exact theorem is
`Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`.
The other four proof-dependency nodes currently have neither a lean record nor a
mathlib match, so there is no recorded proof module to import yet:
`lem-trf-etale-module-finite-presentation-local`,
`lem-trf-finite-extension-module-finite-presentation`,
`lem-trf-finite-morphism-finite-presentation`, and
`lem-trf-finite-pushforward-module-finite-presentation`.
They are not missing notions needed to type this statement.

Edge cases checked against Tag 057T and the interfaces:

- Empty schemes and the zero fibre module admit no supplied supported point `hx`;
  the theorem is conditional on that point, exactly as the node states.
- Relative dimension zero is permitted, with no positivity assumption on n.
- The purely transcendental condition includes the empty transcendence basis,
  hence trivial residue-field extensions are allowed.
- No noetherian, globally finitely presented, separated, or flat assumption on f
  is added. Local finite presentation is explicitly the additional hypothesis.
- The singleton-fibre condition is equality of sets of points, with no assertion
  that the scheme-theoretic fibre is reduced or is a residue-field spectrum.
- Finite presentation near a point is an actual open neighbourhood property;
  it is not silently replaced by finite presentation of the stalk. Both groups
  of assertions are preserved separately.
- Identity etale neighbourhoods and identity finite maps are permitted whenever
  the rest of the elementary data hold; there is no nontriviality hypothesis.

Searches made for an existing statement:

- `msearch.py leanfinder`: "finite presentation of modules equivalent under
  elementary etale devissage finite pushforward and stalks" returned eight hits,
  including `Algebra.Etale.finitePresentation`, standard-etale presentations and
  etale-locus results, none the module-devissage equivalence.
- `msearch.py loogle`: "Module.FinitePresentation, SheafOfModules.IsFinitePresentation"
  returned zero hits.
- `msearch.py grep`: "devissage|IsFinitePresentation" in `AlgebraicGeometry`
  returned zero hits.
- `msearch.py leansearch`: "finite presentation of sheaves under elementary etale
  devissage" returned eight hits on the existing sheaf finite-presentation
  definition and presentation data, none the theorem.
- `rg` of the source project and `lean/Sheaf` for finite presentation near
  devissage and the exact node id found no matching statement. The existing
  elementary-module-devissage theorem provides the data but no finite-presentation
  transfer assertion. Checks for the new declaration name in the project,
  `dag/lean_names_upstream.json` and the side library found no duplicate.
- Mathlib source inspection confirms that `SheafOfModules.IsFinitePresentation`,
  `Module.FinitePresentation`, `SheafOfModules.over`, and the scheme properties
  already give all notions in the statement; no new definition node is required.

Validation: the first wrapper compile diagnosed that a bare abelian stalk did not
expose its canonical module instance. The statement was repaired to use the existing
`RingedSpace.moduleStalkFunctor` explicitly, as required by the project convention.
The final module is checked through `scompile.py` and `deliver2.py --no-push`.

## Second reading by N4

Independent maintainer second reading, 2026-10-18, of immutable delivery
`d98147e92779ff4ed17a836c010c933f13cfdbc2`. This reading replaces the former
placeholder; it was not performed by the author. The Lean module and node record
require no correction.

I read the packet, the snapshot item node, all nineteen statement-dependency
nodes and their records, the complete delivered Lean module and worker report,
and Stacks `flat.tex`, `lemma-elementary-devissage` (057S) and
`lemma-devissage-finite-presentation` (057T), including both proofs. The local
literature paths were unavailable, so I read the Stacks project's published TeX
at https://raw.githubusercontent.com/stacks/stacks-project/master/flat.tex and
cross-checked https://stacks.math.columbia.edu/tag/057T.

Hypothesis and conclusion audit (all match):

- `{X S : Scheme.{u}}`, `f`, and `LocallyOfFiniteType f` introduce exactly the
  original schemes and structural map. `F.IsQuasiCoherentFiniteType` unfolds to
  `F.IsQuasicoherent ∧ F.IsFiniteType`; it does not assume coherence or finite
  presentation. The same check applies to G.
- `fiber`, `fiberι`, and `asFiber` use the canonical scheme-theoretic fibre at
  f(x). `tensorPullback` is the tensor-formula module pullback. `hx` is nonzero
  fibre stalk, and `_hn` takes local topological dimension on its support
  subtype, not on the entire fibre or on the local ring. `n : ℕ` permits zero.
- The two étale maps, marked-point equalities, and `IsIso` on their canonical
  residue-field maps encode elementary pointed neighbourhoods. `_hfg` and
  `_hπ` give both commutative triangles, including that π is over S'.
- All four auxiliary schemes are affine. The closed immersion has local finite
  presentation, quasi-compactness and quasi-separatedness, exactly the recorded
  finite-presentation convention. π is finite. The given `Nonempty` is an
  isomorphism between the actual pushforward of G and tensor pullback of F;
  it is an isomorphism assertion, not a construction chosen arbitrarily.
- `SmoothOfRelativeDimension n h` and `GeometricallyIntegral h` have the stated
  fibre meanings. `_hi`, `_hs` and the set equality `_hfibre` give the specified
  three points and singleton fibre. Writing y' as `π z'` loses no data.
  `_hpure` explicitly uses the algebra of `h.residueFieldMap (π z')`; `_hs`
  identifies its base point with s'. No arbitrary algebra structure is assumed.
- `LocallyOfFinitePresentation f` is precisely the additional hypothesis.
  The first conclusion is finite presentation of π in the recorded lfp+qc+qs
  sense. The next two adjacent iff clauses express all three neighbourhood
  assertions using actual open neighbourhoods and `SheafOfModules.over`.
  The last two adjacent iff clauses express the three stalk assertions over
  their actual local rings. They use `RingedSpace.moduleStalkFunctor` and
  `Module.FinitePresentation`, including the stalk of the actual π-pushforward.
  No equivalence between neighbourhood and stalkwise finite presentation is
  inadvertently asserted.

Exact interfaces inspected: Mathlib Scheme/Spec, LocallyOfFiniteType, Etale,
IsFinite, IsClosedImmersion, LocallyOfFinitePresentation, Smooth and
SmoothOfRelativeDimension, IsIntegral and GeometricallyIntegral, residueField
and residueFieldMap, the fibre pullback, scheme module pushforward, restriction
`over`, finite generators/presentations of sheaves, and Module.FinitePresentation
(with `exists_fin'`). I read the existing CoherentFiniteType conjunction and
local-dimension definition. Using `scompile.py --source`, I read the current
ElementaryModuleDevissage, TensorPullback, ModuleStalkFunctor, and
PurelyTranscendentalExtension modules where the old local checkout lacked them.
The devissage dependency gives exactly these hypotheses. The stalk functor's
object is the abelian stalk with its canonical module action. Pure transcendence
is algebraic independence of a subset with intermediate-field adjoin equal to top.
No notion is privately copied or newly defined in this delivery.

The theorem docstring reproduces all four DAG proof steps and their named
prerequisites: finite-presentation permanence and finiteness; étale openness and
finite-presentation descent; the two finite-pushforward comparisons; faithfully
flat stalk descent and finite-extension comparison. I read the five proof-node
statements in the group clone and the exact imported descent declaration
`Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`.
The four other proof nodes have no recorded Lean declarations there. They are
future proof inputs, not absent notions needed to type this statement; no
missing-helper or universe repair is needed for this delivery.

Edge cases: empty X or zero fibre module supplies no supported point hx, as in
the node. n=0, trivial residue extensions (empty transcendence basis), and
identity neighbourhoods are allowed. The singleton fibre is a set of points,
not an assertion of reducedness. No Noetherian, characteristic, global finite
presentation, separatedness, or extra flatness condition on f is imposed.
The arbitrary bound universe u is shared by schemes and their canonical module
categories consistently with the dependency signatures; no site-universe
identification or hidden smallness assumption occurs.

Independent searches with `rg` in Mathlib, slopmaster2 WeilConjectures, and the
N4 side Lean tree for `devissage.*finite.*presentation`,
`finite.*presentation.*devissage` and the declaration name found no existing
copy of this theorem. I checked the already-existing definitions directly,
including the finite generators/relations definition of Module.FinitePresentation
and the finite local presentations definition of SheafOfModules.IsFinitePresentation.
The worker report records LeanSearch, LeanFinder, Loogle and grep searches;
no new definition is being introduced or duplicate theorem found.

Static checks: the node's `lean.statement` equals the complete signature from
`theorem` to before `:=` byte for byte. There are no lines over 100 characters,
no file-local notation/instances, no unbound variables (`autoImplicit false`),
and no definitions or local proofs. There is exactly one theorem with proof
`by sorry`. Module and theorem docstrings both carry the source and blueprint
id, and the theorem docstring includes the four proof steps. The canonical
pullback convention is followed. All nineteen statement dependencies have
records in the snapshot. No statement correction or citer audit is required.

Route-pivot check: the current shared `origin/newtargets-dag` dropped-node list
has empty intersection with the item's statement and proof dependencies. The
item-specific repair note is absent. This scheme/module statement introduces
no enhanced localization, model/infinity/dg machinery, or pro-etale substitute.

Compiler evidence: the worker report claims final wrapper compilation and a
`deliver2.py --no-push` check but supplies no raw transcript in the snapshot.
I independently reproduced the per-file compile using
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N4
lem-trf-elementary-devissage-finite-presentation
snapshot/lean/Sheaf/TraceFormula/ElementaryDevissageFinitePresentation.lean`.
The installed wrapper uses the server overlay (its current documented behaviour),
so no separate direct ssh invocation or local compiler bypass was used.
It exited 0 with no Lean errors or warnings; output reported sandbox compilation
11.5 s and library compilation 130.7 s (wrapper wall times, not a changed per-file
limit). Multiplexing diagnostics were connection messages, not Lean diagnostics.
No lake/global build or direct live Lean write was performed.

Finding and repair: H11 / reporting requirement: the original second-reading
section only said that no worker second reading occurred. This complete report
retains the Worker report and supplies the actual independent reading above.
No mathematical or Lean change is needed. Verdict: FIX, report replacement only.
