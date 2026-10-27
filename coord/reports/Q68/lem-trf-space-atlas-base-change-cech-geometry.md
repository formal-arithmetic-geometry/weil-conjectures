## Worker report

Item: `lem-trf-space-atlas-base-change-cech-geometry`, Q68, 2026-10-24 UTC.
Module: `Sheaf.AlgebraicGeometry.SpaceAtlasBaseChangeCechGeometry`.
Declarations: `AlgebraicGeometry.AlgebraicSpace.space_atlas_base_change_cech_geometry`
and `AlgebraicGeometry.AlgebraicSpace.space_atlas_base_change_cech_naturality`.
Both theorem proofs are `sorry`; no definition, axiom, instance, or proved helper is added.
The node changes only in `lean`. No statement correction or additional node is needed.

Read the whole node, all five statement-dependency nodes and their recorded declarations,
the two other proof-dependency nodes, Stacks `spaces-morphisms.tex` lines 1837–1874,
and the current blueprint's `sk-i-curve-zero` section and local-term-locality statement
and proof. The atlas calculation belongs to the node's recorded historical ancestry;
it does not replace the current blueprint's contracting-correspondence argument.
The source's printed overlap subscript `X` is already corrected to `W` in this node.

### Hypotheses and construction conventions

The only geometric hypotheses are exactly those of the node:

| Node | Lean |
| --- | --- |
| Scheme S | `{S : Scheme.{u}}` |
| Algebraic spaces X and Y over S | `X Y : AlgebraicSpace S` |
| Morphism f | `f : X ⟶ Y` |
| Schemes U and V over S | `U V : Over S` |
| Schemes viewed as algebraic spaces | `schemeSpace U`, `schemeSpace V` |
| Scheme atlas p | `p : schemeSpace U ⟶ X` |
| Atlas etale | `hp : IsEtale p.hom.hom` |
| Atlas surjective in the scheme-test sense | `hps : IsSurjective p.hom.hom` |
| Etale scheme test v | `v : schemeSpace V ⟶ Y`, `hv : IsEtale v.hom.hom` |

The phrase "put R, W, Z, Q equal to the fibre products" is rendered by arbitrary
limiting cones, not by extra geometric assumptions: `r`, `w`, `z`, `q` are respectively
`IsPullback p₁.hom p₂.hom p.hom p.hom`,
`IsPullback wV.hom wX.hom v.hom f.hom`,
`IsPullback zV.hom zU.hom v.hom (p ≫ f).hom`, and
`IsPullback qV.hom qR.hom v.hom (p₁ ≫ p ≫ f).hom`.
These are precisely the universal properties of the fibre products in the dependency.
The sheaf category has its chosen fibre products; this formulation applies to those
and to any isomorphic choices. It adds no separatedness, finiteness, field or chart data.

Likewise `hcV`, `hcX` specify the unique canonical `c : Z ⟶ W` by both projections.
`hq₁V`, `hq₁U`, `hq₂V`, `hq₂U` specify the two unique induced arrows `q₁ q₂ : Q ⟶ Z`.
They are construction equations, not assumptions on otherwise arbitrary comparison maps.
For the second projection, `r.w` gives `p₂ ≫ p = p₁ ≫ p`, so its target equation
is exactly the one required for the same Q. No choice of a noncanonical map is made.

### Every conclusion clause

| Node clause | Lean |
| --- | --- |
| R, Z, Q are schemes | First three existential conjuncts: each underlying presheaf is isomorphic to `yoneda.obj T` for `T : Over S` |
| Both R → U projections etale | `IsEtale p₁.hom.hom ∧ IsEtale p₂.hom.hom` |
| Z → U etale | `IsEtale zU.hom.hom` |
| Q → R etale | `IsEtale qR.hom.hom` |
| W → X etale | `IsChartwiseEtale wX` |
| Singleton Z → W etale covering | `IsChartwiseEtale c` and `IsJointlySurjective (fun _ : Unit ↦ c.hom.hom)` |
| Objects in the actual enlarged site C_X | Existentials `Xₓ Uₓ Rₓ Wₓ Zₓ Qₓ : X.EnlargedEtaleSite`, with their `obj` equal to the specified `Over.mk` objects |
| Projection and covering arrows in C_X | Site arrows `p₁ₓ p₂ₓ zUₓ qRₓ cₓ q₁ₓ q₂ₓ wXₓ`, with `HEq` identifying their underlying algebraic-space arrows with the displayed canonical maps |
| Covering in C_X | `Presieve.ofArrows (fun _ : Unit ↦ Zₓ) (fun _ : Unit ↦ cₓ) ∈ X.enlargedEtalePrecoverage Wₓ` |
| Canonical overlap isomorphism | `∃ e : Limits.pullback c.hom c.hom ≅ Q.obj` |
| Two maps to Z induced by p₁,p₂ | `e.hom ≫ q₁.hom = pullback.fst ...` and `e.hom ≫ q₂.hom = pullback.snd ...`, together with the four defining equations for q₁,q₂ |
| Isomorphism over W | Each of those equations composed with `c.hom` identifies the structural map; the pullback condition identifies the two results |
| Test-scheme formula | The two projection equations, evaluated at any `T : Over S`, identify qV with v_T and identify the two coordinates of qR with u₁,u₂; universal properties determine `(v_T,(u₁,u₂))` uniquely |
| Naturality under every V' → V over Y | The second declaration's equation `d ≫ e.hom = e'.hom ≫ aQ.hom` |

An isomorphism in the sheaf category is precisely an algebraic-space isomorphism
between these full-subcategory objects. The conclusion retains the actual underlying
Yoneda presheaves when asserting scheme representability. Since R, Z, Q are schemes,
representable etaleness of their projections is the scheme-etaleness assertion of the node.
For W, which may be a genuine algebraic space, chartwise etaleness is the definition
used by the enlarged-site dependency.

The second theorem repeats the original atlas hypotheses (`hp`, `hps`) and both etale
test hypotheses (`hv`, `hv'`). `a : V' ⟶ V` is an actual map of schemes over S;
`ha : yoneda.map a ≫ v.hom.hom = v'.hom.hom` says it is over Y. It need not be
assumed separately etale: it is a map between objects of Y's etale site.
The primed `w'`, `z'`, `q'` are the three primed pullbacks; `R` and `r` are shared.
`hcV'`, `hcX'`, `hq₁V'`, `hq₂V'`, `hq₁U'`, `hq₂U'` specify the primed canonical maps.
`he₁`, `he₂`, `he₁'`, `he₂'` say both isomorphisms are the canonical ones of the first
theorem. `haWV`, `haWX` fix aW by its V- and X-projections; `haZV`, `haZU` fix aZ
by its V- and U-projections; `haQV`, `haQR` fix aQ by its V- and R-projections.
Finally `hd₁`, `hd₂` fix the induced map d of the two overlaps by both projections.
All these maps exist uniquely by the displayed pullback universal properties. Thus
this universal diagram formulation is naturality for the canonical maps, not naturality
for some arbitrarily selected map, and includes identity and arbitrary test-site arrows.

### Dependency declarations used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `IsSurjective`, with the exact scheme-test meanings read in that module.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `IsChartwiseEtale`, `EnlargedEtaleSite`, `enlargedEtalePrecoverage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  the statements use the very sheaf category and universal property supplied there.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: current recorded enlarged-site
  dependency module, publicly importing the existing enlarged-site interface; its
  recorded `cotangentRingMap` and docstring were read, though no ringed-topos map is
  needed in this geometric statement. No interface repair is needed.
- Proof imports: `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`
  (`chartwise_etale_permanence`) and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` (`IsJointlySurjective`).
- Mathlib `IsPullback`, `Limits.pullback`, its two projections, `Over.mk`, `yoneda`,
  and `Presieve.ofArrows` are reused directly. There are no private copies of a notion.

### Edge cases checked

Empty X is allowed: a surjective atlas then has empty U, and the pullbacks, representability
and singleton-covering assertions remain valid. Empty V gives empty W, Z, Q; a singleton
map between empty objects is a covering because there are no target field points.
For the identity atlas, R = U = X and Z = W, so the overlap assertion becomes the
diagonal identity. Neither connectedness of V nor a single component is assumed.
For X = Y = U = Spec k and V two points, Q and Z ×_W Z both have two points;
Z ×_X Z would have four. The written statement uses W, retaining the node's correction.
Nothing restricts the characteristic or imposes a field hypothesis. All schemes and
field tests use the same arbitrary universe u as the dependency's big-site convention.
Identity a, isomorphisms a, nonidentity maps a, and empty V' are all included in the
naturality declaration; no surjectivity of a is imposed.

### Searches

All msearch calls used the prescribed Q68/item invocation; raw output is in the sandbox's
`searches.jsonl` from the wrapper.

- LeanFinder: `Base change of an algebraic space atlas has Cech overlap V times_Y (U times_X U)`.
  Eight hits, all scheme pullback/open-cover constructions, including `Scheme.Pullback.v`;
  none states this node, its enlarged-site clause, or its naturality.
- Loogle: `CategoryTheory.Limits.pullback, CategoryTheory.Iso`.
  Twelve generic pullback isomorphisms, including `pullbackSymmetry`,
  `IsPullback.isoPullback`, `pullbackLeftPullbackSndIso`; none is the complete statement.
- LeanSearch: `Base change of an etale atlas of an algebraic space and the canonical isomorphism of Cech overlaps`.
  Eight hits on scheme etale stability and topologies; none matches.
- Mathlib grep: `AlgebraicSpace|atlas.*[Cc]ech|[Cc]ech.*atlas`, subdirectory AlgebraicGeometry.
  Zero hits.
- Project/upstream rg: `atlas.*[Cc]ech|[Cc]ech.*atlas|lem-trf-space-atlas-base-change-cech-geometry`
  in `lean/WeilConjectures` and `lean/Sheaf`. Only an unrelated higher-direct-image
  spectral-sequence docstring, no existing declaration of the item.
- Name rg: `atlasBaseChange|atlasOverlap|baseChangeCech` in both source trees and
  `dag/lean_names_upstream.json`. Only upstream `CategoryTheory/Sites/CechBaseChange.lean`,
  a comparison of Cech complexes, not this algebraic-space geometry.

Validation: prescribed scompile.py compiled this single module separately as sandbox
and library, cleanly, including after the final enlarged-site W → X arrow was added.
No unexpected warning, error, timeout, hidden universe equality, or auto-implicit variable.

## Second reading by Q68

Reopened the node and the entire module for a second clause-by-clause pass. The dispatcher
forbids starting another agent, so this is a second pass by the assigned worker; the
maintainer's independent reading remains the independent review of this delivery.

The original geometric hypotheses match `S`, `X`, `Y`, `U`, `V`, `f`, `p`, `v`,
`hp`, `hps`, `hv`; the four IsPullback witnesses render exactly the four specified
fibre products. The extra arrow equations specify induced maps uniquely and do not
impose another geometric hypothesis. The first three conjuncts retain actual scheme
representability. The five etaleness clauses match p₁, p₂, zU, qR and wX individually.
The covering includes both chartwise etaleness and joint surjectivity, and it is explicitly
asserted again as the actual enlarged-site singleton presieve. All five relevant objects
have their exact structure maps to X. During this pass I added the enlarged-site base
object Xₓ and its projection wXₓ so the listed W → X projection is explicitly a site
arrow too; recompiled cleanly afterwards. The p₁/p₂, zU, qR, c, q₁/q₂ site arrows have
the intended underlying maps via HEq, without using equality to transport an arbitrary
replacement. Both overlap projection equations fix exactly the tuple formula and the
map over W. The second declaration includes all primed diagrams, both isomorphisms'
projection characterizations, and every projection of every naturality arrow. In
particular neither an identity restriction on a nor an omitted V-coordinate permits
a noncanonical comparison. Source and proof docstrings cover steps 1–4 and step 5
respectively. No mathematical mismatch or statement dispute remains.
