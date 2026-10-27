## Worker report

The single module `Sheaf.AlgebraicGeometry.DominantGenericDifferentialComparison`
states `AlgebraicGeometry.Scheme.Hom.dominant_generic_differential_comparison`.
Its only theorem has proof `sorry`; no definitions or auxiliary theorems are added.
The node's mathematical statement, dependencies, and proof are unchanged.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; both integral schemes are `(X Y : Scheme.{u})`
  with `[IsIntegral X] [IsIntegral Y]`. No dimension, finite type, smoothness,
  characteristic, or separability restriction is imposed.
- The target structure map is `(g : Y ⟶ Spec (.of k))`. The source structure map is
  `f ≫ g`, so `(f : X ⟶ Y)` is precisely a morphism over k. This is the standard
  dependent-binder presentation of a commutative triangle, equivalent to independently
  supplying the source map and an equality with the composite.
- Dense image is `[IsDominant f]`. The chosen points are Mathlib `genericPoint X`
  and `genericPoint Y`. `X.functionField` and `Y.functionField` are definitionally
  their structure-sheaf stalks; their field instances follow from integrality.
- `αX` and `αY` are linear equivalences over those respective function fields from
  `(RingedSpace.moduleStalkFunctor ...).obj ...relativeDifferentials` to the field
  differential modules. The latter are the existing bundled
  `CommRingCat.KaehlerDifferential` for the actual base-field ring maps:
  `(Scheme.ΓSpecIso (.of k)).inv ≫ structureMap.appTop ≫ presheaf.germ ⊤ η trivial`.
  Thus the base field acts through the given scheme structure map, not through
  arbitrary algebra instances. Bundled differentials use the same Mathlib
  `KaehlerDifferential` construction internally.
- `hαX` and `hαY` quantify over every open containing the corresponding generic point
  and every regular function there, and assert that the germ of the sheaf universal
  derivation goes to `CommRingCat.KaehlerDifferential.d` of the ring germ. In an
  irreducible scheme, the opens containing its generic point are exactly its nonempty
  opens (`genericPoint_spec` and `IsGenericPoint.mem_open_set_iff`). Thus this is
  exactly both normalization hypotheses, with no affine restriction.
- `∃ hη : f (genericPoint X) = genericPoint Y` asserts the first conclusion rather
  than assuming it. The recorded existing `f.functionFieldMap hη` is literally
  `Y.presheaf.stalkSpecializes (specializes_of_eq hη) ≫ f.stalkMap (genericPoint X)`;
  this is the specified induced function-field map phi.
- `∃ β : ... ≃ₗ[X.functionField] (ModuleCat.extendScalars
  (f.functionFieldMap hη).hom).obj (...)` is the required L-linear isomorphism from
  the generic stalk of the actual tensor pullback to L tensor_K Omega_K/k. The
  extension of scalars uses exactly phi, not any independently supplied K-action.
- The first conjunct quantifies over every target neighbourhood V and every local
  section s. `Modules.tensorPullbackSection f ... V s` is the actual sheafification
  of `1 tensor inverseImageUnit(s)`, and hence the section of the recorded normalized
  adjunction unit. The equality sends its germ at eta_X to
  `1 ⊗ₜ[Y.functionField, phi.hom] αY(germ s)`. The membership proof is transported
  along hη, making the inverse-image neighbourhood well typed.
- The last clause, for every `a : X.functionField` and `b : Y.functionField`, applies
  `αX` after the stalk of `g.relativeDifferentialsPullbackMap f` after `β.symm` to
  `a tensor db`, and gives `a • d(phi b)`. Every composed map is L-linear by its
  declared type. The pure differential tensors generate the source, so this is
  exactly the node's characterization of the L-linear map on the whole tensor
  product, not merely a statement about an unrelated map.

Declarations and source modules read and used:

- `Field`: `Mathlib.Algebra.Field.Defs` (available through the imports).
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`: `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.IsIntegral`: `Mathlib.AlgebraicGeometry.Properties`.
- `Scheme.Over`, `Scheme.Hom.IsOver`: `Mathlib.AlgebraicGeometry.Over`; the equivalent
  explicit composite presentation described above is used.
- `IsGenericPoint`, `genericPoint`, `genericPoint_spec`: `Mathlib.Topology.Sober`.
- `Scheme.functionField`: Mathlib `AlgebraicGeometry.FunctionField`, publicly imported
  by the dependency module `WeilConjectures.AlgebraicGeometry.FunctionField`.
  The component-product definition of that module is intentionally not used since
  this node uses its arbitrary integral-scheme generic-stalk clause.
- `PresheafOfModules.moduleStalkFunctor`: recorded module
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`; as the dependency's note
  directs for scheme module sheaves, the equivalent existing
  `RingedSpace.moduleStalkFunctor` is used from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`, imported by the stalk tool.
- `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`.
- `KaehlerDifferential`, `KaehlerDifferential.D`:
  `Mathlib.RingTheory.Kaehler.Basic`; its bundled ring-map versions
  `CommRingCat.KaehlerDifferential` and `.d` are defined in
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`, already publicly imported
  by the differential sheaf module.
- `Scheme.Modules.tensorPullbackSectionAdjunction`, `tensorPullbackSection`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, retaining the upstream
  `tensorPullback` construction rather than redefining it.
- `TensorProduct` and tensor universal properties: Mathlib tensor product modules;
  `ModuleCat.extendScalars` and `ChangeOfRings` pure tensors encode the specified ring
  map without a new algebra structure or arbitrary-map hypothesis.
- `Scheme.Hom.relativeDifferentialsPullbackMap`:
  `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`.
- `Scheme.Hom.functionFieldMap`:
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`; its definition applies
  to all integral schemes and has no curve hypothesis.
- Proof tools are imported directly: `exists_tensorPullback_stalk_iso` from
  `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`; scheme sobriety
  from Mathlib Properties/Sober; locally ringed morphisms from
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`.

Sources read: Stacks `morphisms.tex`, lemma-functoriality-differentials, lines 6598ff
(Tag 01UV), and `sheaves.tex`, lemma-stalk-pullback-modules, lines 3244ff (Tag 0098).
The current blueprint proof (3) in `literature/blueprint/latest/` is the unexpanded
auxiliary route recorded by the accepted split. No source-based correction is needed.
The example Sheaf CompactObject module is now withdrawn; its node points to the
upstream module, whose convention is followed.

Edge cases checked mathematically: identity maps give the usual tensor identification;
open immersions give the corresponding localization map; Spec k allows the zero
module of differentials on either side; in characteristic p a Frobenius-type map
may send db to zero, which the final formula permits. The theorem does not claim
that df is injective, nonzero, or an isomorphism. Empty schemes are excluded by the
node's own integrality assumption, and empty opens carry no generic germs. The
single explicit universe accommodates schemes and their field-sized rings together;
there is no test-object quantification in a smaller universe.

Searches made through the required wrapper on 2026-10-24:

- `leanfinder`: "For a dominant morphism of integral schemes the generic stalk of the
  pullback differential map is the scalar extension map on function field Kahler
  differentials". Eight hits, including `KaehlerDifferential.map`, `.map_D`,
  `.mapBaseChange`, `.isBaseChange`, the presheaf differential restriction formula,
  and rational-map function-field constructions. None states the normalized geometric
  stalk comparison and beta section formula.
- `loogle`: "KaehlerDifferential.map, TensorProduct, stalk". Zero hits; the service
  additionally reported unknown identifier `stalk`.
- `grep` via msearch, Mathlib AlgebraicGeometry:
  `(stalk|functionField).*(differentialsMap|mapDifferential)|[Dd]ifferential.*generic`.
  Zero hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for dominant/generic/differential
  combinations and `relativeDifferentialsPullbackMap` found the geometric primitives,
  AdelicDifferentials, and the separable-curve nonvanishing consumer, but no theorem
  with this statement. `grep -rn` for this node id in WeilConjectures found no match.
- Exact-name `rg` in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`
  found no existing `dominant_generic_differential_comparison` declaration.

Validation: prescribed `scompile.py` passed for both the sandbox module and its library
module name, with no errors or warnings. The one statement deliberately remains sorry.
No new nodes, dependency repairs, statement disputes, or statement corrections.

## Second reading by N0

Author's separate rereading with the node and final module open; no independent worker
was started, as the dispatcher explicitly prohibits starting agents. The maintainer's
independent review remains the independent reading of this delivery.

I matched the two alpha normalizations separately, checked that every local section
is quantified in the beta clause, and expanded `functionFieldMap` to verify that the
same stalk ring map defines both the tensor scalar action and phi in the final formula.
The source structure map is the composite, so no additional commutative-triangle
assumption has been silently discarded. Bundled field differentials retain precisely
the canonical k-actions. The final clause specifies the whole linear map because
the tensors of db generate; no unjustified isomorphism of df is asserted.

During elaboration I corrected only the membership transport from eta_Y in V to
eta_X in f-inverse(V): explicit `congrArg` on membership avoids Lean's cast inference
failure on the definitional inverse-image membership. No mathematical statement changed.
I also removed an unnecessary helper ring-map definition and wrote the existing ring-map
composite directly in the differential module types, avoiding a duplicate notion.
All variables and the universe are explicitly bound; both auto-implicit options are off.
