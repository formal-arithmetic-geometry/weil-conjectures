## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceTorIndependenceEtaleChart`
states the node without changing its mathematical statement. It introduces the
predicate that the node itself defines, `AlgebraicGeometry.AlgebraicSpace.IsGeometricallyTorIndependent`,
and states `torIndependent_iff_etale_chart` and `torIndependent_iff_scheme_local`.
Both theorem proofs are exactly `by sorry`. The predicate has a complete expression,
with no postponed data. There are no new nodes or dependency modules.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. The three algebraic spaces over this same
  base are `{F G H : AlgebraicSpace S}`, and the original morphisms are
  `(f : F ⟶ H) (g : G ⟶ H)`. Universes are explicitly declared; no auto-implicit
  variables occur (`set_option autoImplicit false`).
- The geometric condition quantifies over `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`,
  its structure map `(s : Spec (.of Ω) ⟶ S)`, and both natural transformations
  `x : yoneda.obj (Over.mk s) ⟶ F.obj.obj` and
  `y : yoneda.obj (Over.mk s) ⟶ G.obj.obj`. Yoneda identifies these exactly with
  the two scheme-valued geometric points. The equation
  `h : x ≫ f.hom.hom = y ≫ g.hom.hom` says that their H-valued point is the same;
  thus the field, base map, and H-valued point are shared, as in the node.
- The geometric local rings are the published `SingleComplex.stalkRing s x`,
  `SingleComplex.stalkRing s y`, and `SingleComplex.stalkRing s (x ≫ f.hom.hom)`.
  Their defining regular-function colimits on the small affine étale basis were
  read in the recorded dependency module. This is the structure-sheaf stalk,
  not an arbitrary ring or a chosen ordinary local ring.
- `SingleComplex.stalkMap f s x` supplies the first canonical scalar action.
  For the second, `eqToHom (congrArg (fun z ↦ SingleComplex.stalkRing s z) h)`
  transports the common target stalk, then `SingleComplex.stalkMap g s y` maps
  to the second stalk. `ModuleCat.restrictScalars` applies these actual maps
  to each ring regarded as a module over itself. There are no assumed actions.
- The defining quantifier `(i : ℕ), 0 < i → IsZero (...)` is exactly vanishing
  of every positive Tor. The functor is the recorded `CategoryTheory.Tor'`,
  deriving in the first module. `IsZero` is applied to a `ModuleCat` object.
- The three scheme atlases are `(U V W : Over S)`. The map to H is
  `a : yoneda.obj W ⟶ H.obj.obj`; `hae : IsEtale a` and
  `has : IsSurjective a` impose precisely the first atlas condition.
- The maps to F and G are `b` and `c`. The ordinary scheme morphisms to W
  are `p : U ⟶ W` and `q : V ⟶ W`. The equations `hb` and `hc` are exactly
  the two commuting squares. The induced map `Limits.pullback.lift b
  (yoneda.map p) hb` is U → F ×_H W, with the analogous expression for V.
  `hbe`, `hbs`, `hce`, and `hcs` impose étaleness and surjectivity on these
  two induced maps, not on an unrelated map or on U → W itself.
- The conclusion `IsGeometricallyTorIndependent f g ↔
  PullbackStalkTensor.IsTorIndependent p.left q.left` uses the existing
  ordinary-point predicate. Its full definition was read: it quantifies over
  every `x : U.left`, `t : V.left`, and equality `p.left x = q.left t`,
  takes all positive degrees, and uses the two actual ordinary stalk maps,
  with target-stalk transport along that equality. Thus its common W-point
  and its Tor groups are exactly those in the displayed formula of the node.
- All atlas data are arbitrary theorem binders, so the equivalence holds
  for every permitted choice, not merely for a selected atlas.
- The final scheme assertion is explicitly stated in
  `torIndependent_iff_scheme_local`. The presheaf isomorphisms `eF`, `eG`,
  and `eH` identify the algebraic spaces with the represented schemes U,V,W;
  the equations `hp`, `hq` identify their morphisms with `p`, `q`. This
  specifies the meaning of “for schemes F,G,H” in the existing sheaf-valued
  algebraic-space API. These are presentations, not extra geometric
  hypotheses: any scheme's represented space has such presentations.
  The conclusion is the same ordinary-point condition on those schemes.
- There is no flatness, quasi-compactness, separation, Noetherian, or
  finiteness hypothesis anywhere in these signatures.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (the scheme node's recorded declarations).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`, and `IsSurjective`.
  The latter predicates test all representable scheme base changes.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, the recorded
  Tor-module definition. The required module instances are supplied by the
  published scheme Tor module's public imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme` explain the actual
  sheaf pullbacks used for the atlas maps and their scheme presentations.
- `def-weil-size-convention` is a metatheoretic convention, with no Lean
  declaration to import; its explicit level is `u` throughout these objects.
- Added the already landed node `def-sfb-space-geometric-stalk-models` to
  `stmt_deps`, using `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.stalkRing`, `SingleComplex.stalkMap`, and their normalized
  colimit and germ specifications. No replacement stalk construction is made.
- Added the already landed node `def-pc-pullback-stalk-tensor-comparison` to
  `stmt_deps`, using `WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison`:
  `AlgebraicGeometry.PullbackStalkTensor.IsTorIndependent`. No replacement
  scheme Tor-independence predicate is made.

The public imports supply precisely these statement interfaces. Private proof
imports include all currently stated proof dependencies: strict-henselization
functoriality, faithfully flat strict henselization, representable étale scheme
tests, localization flatness and tensor formulas, algebraic closure existence,
affine fibre products, tensor pushout formulas, localization detection of
bijectivity, and affine stalk localization. Proof dependencies without a Lean
record or Mathlib match are not restated or imported; they are named in the
natural-language proof plan, with the node's seven steps expanded there.

Edge cases checked before writing:

- Empty schemes or empty algebraic spaces are allowed; there is no Nonempty
  binder. Geometric-point and ordinary-point conditions are vacuous when
  their pairs do not exist. Surjective atlases over an empty target cause
  no additional exclusion.
- Only positive Tor degrees vanish. Degree zero is intentionally excluded;
  the tensor product need not be zero. Degree one is included.
- Compatible geometric points use exactly the original same algebraically
  closed field, with equality of their H-images. No field extension is
  silently introduced as a hypothesis.
- All schemes and geometric-point fields live in the published section
  universe `u`, matching the recorded geometric-stalk interface and the
  size convention. Scheme objects and their natural-transformation sites
  retain their actual object/morphism universes; no equality of independent
  site universes is imposed.
- No affine atlas, finite covering family, or affine intersection is required.
  Identity atlases and arbitrary alternate surjective étale atlases are covered.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Tor independence of algebraic spaces is equivalent
  to vanishing of higher Tor of ordinary local rings on surjective etale scheme
  charts"`: 8 hits (formal smoothness, étale morphisms, étale loci), none the
  geometric-versus-ordinary Tor criterion.
- `msearch.py ... loogle "CategoryTheory.Tor, AlgebraicGeometry.AlgebraicSpace"`:
  0 hits; the Mathlib index does not know the project's AlgebraicSpace name.
- `msearch.py ... grep "TorIndependent|tor_independent|geometricLocalRing"`:
  0 Mathlib hits.
- `msearch.py ... leansearch "Higher Tor vanishing of geometric local rings is
  equivalent to Tor vanishing of ordinary local rings on etale atlases"`:
  8 hits on étale localization and ring-map properties, no comparison theorem.
- `rg` of TorIndependent/torIndependent/tor_independent in both
  `lean/WeilConjectures` and `lean/Sheaf` found the ordinary scheme predicate,
  flat scheme Tor independence, and derived tensor comparison theorems, but
  no algebraic-space atlas criterion. Reused the scheme predicate found there.
- `rg` of geometricLocalRing/strictLocalRing/geometricStalk in the algebraic-space
  modules found the published geometric stalk model, which is reused.
- `grep -rn` of the item id in `lean/WeilConjectures` found no occurrence.
  `rg` of the three proposed declaration names in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures`, and `lean/Sheaf` found no existing declaration.

Source checked directly: `literature/stacks-project/spaces-perfect.tex`,
Definition `definition-tor-independent` and Lemma `lemma-tor-independent`,
including the full proof and its scheme comparison (Tags 08IP and 08IQ).
No statement correction or disputed mathematical assertion was needed.
The inherited stage-1 unchanged-split failure is superseded by the explicit
stage-handoff rule in `coord/brief-stage2.md` §0; this is a stage-2 delivery.

Validation: scompile.py compiled the module both as a sandbox and at its final
library path. The first run passed (2.8 s / 2.6 s). Final proof imports were
then made explicit; the final module also passed (12.3 s / 7.0 s), with no errors
or unexpected warnings.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
