## Worker report

Delivered module: `Sheaf.TraceFormula.LocalizedDevissageNeighborhoodTransfer`.
Main declaration:
`AlgebraicGeometry.Scheme.Modules.exists_localized_devissage_neighborhood_transfer`.
Its only proof is `sorry`. The fully defined auxiliary predicate
`localizedDevissageBaseChangeConclusions` packages exactly the base-change clauses of
this same theorem; it introduces no replacement scheme, module, flatness or finiteness
notion and has no postponed data. Both declarations are in `lean.declarations`.
The item is unchanged outside `lean`; no statement correction or new node is needed.

Source read: Stacks `flat.tex`, Tag 05I5, `proposition-finite-type-flat-at-point`,
first proof, especially the elementary-devissage diagram, localization at the marked
base point, and reduction by Tags 057T/057U. Also read Tag 057S
`lemma-elementary-devissage`, Tag 057T `lemma-devissage-finite-presentation`, and Tag
057U `lemma-devissage-flat`. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality`
and its proof were read as context; this is its supporting Stacks algebra branch,
not a restatement of that ancestor's contracting-correspondence statement.
The nominal example CompactObject module is withdrawn; its node records the existing
upstream `WeilConjectures.CategoryTheory.CompactObject` instead. The present module
follows the current module-mode header and the live ElementaryModuleDevissage module.

Clause-by-clause reading:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Affine schemes X and S | `{X S : Scheme.{u}} [IsAffine X] [IsAffine S]` |
| Locally finitely presented f | `(f : X ⟶ S) [LocallyOfFinitePresentation f]` |
| Finite-type quasi-coherent F | `(F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]` |
| x in support of fibre F_s, s=f(x) | `hx : ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x))` |
| n is dimension at x of the support | `∃ n : ℕ` with `topologicalKrullDimAt` of `⟨f.asFiber x, hx⟩` in the actual support subtype equal to `(n : WithBot ℕ∞)` |
| Affine elementary etale (S₁,s₁) over (S,s) | `S₁`, `s₁`, `e`; `IsAffine S₁`, `Etale e`, `e s₁ = f x`, `IsIso (e.residueFieldMap s₁)` |
| A is O_{S₁,s₁} | Literally `S₁.presheaf.stalk s₁`, not an arbitrary local algebra |
| X_A and F_A | `Limits.pullback f (S₁.fromSpecStalk s₁ ≫ e)` and tensor pullback of F along its first projection |
| Affine A-schemes X₁,Z,Y | `X₁`, `Z`, `B : CommRingCat.{u}` with `IsAffine X₁`, `IsAffine Z`; Y is literally `Spec B`; α gives its A-map |
| Source structure and diagram | X₁'s A-map is `g ≫ pullback.snd ...`; `i ≫ g ≫ pullback.snd ... = π ≫ Spec.map (ofHom α)` gives Z its common A-map and makes π an A-map |
| Elementary g and marked points | `Etale g`, `IsIso (g.residueFieldMap (i z))`; the marked points x₁ and y are `i z` and `π z`, so their named equations are definitional |
| x_A above x | The first projection sends `g (i z)` to x; the quantified w clause records uniqueness of that lift |
| Finitely presented closed immersion i | `IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i` |
| Finite π and singleton fibre | `IsFinite π` and `π ⁻¹' {π z} = {z}` |
| Finite-type quasi-coherent G | `G.IsFiniteType ∧ G.IsQuasicoherent` |
| y over the closed point | `(Spec.map (ofHom α)) (π z) = IsLocalRing.closedPoint (S₁.presheaf.stalk s₁)` |
| Purely transcendental marked residue extension | `Algebra.IsPurelyTranscendentalExtension` using the actual `residueFieldMap` of `Spec.map α`; the residue field of Spec A at the closed point is canonically κ(s₁) |
| Smooth Y/A, dimension n and geometrically integral fibres | `SmoothOfRelativeDimension n (Spec.map (ofHom α)) ∧ GeometricallyIntegral (...)`; the latter's definition tests integrality after every field-valued base change, including nonemptiness |
| X₁/A finitely presented | Its A-map is locally finitely presented, quasi-compact and quasi-separated |
| i_*G is g^*F_A | An actual isomorphism `E : (pushforward i).obj G ≅ (tensorPullback g).obj F_A` |
| π_*G is tilde N and N finite | `N : ModuleCat.{u} B`, `Module.Finite B N`, `Nonempty ((pushforward π).obj G ≅ tilde N)` |
| A→B flat and finitely presented | `α.Flat` and `@Algebra.FinitePresentation ... α.toAlgebra`; no unrelated algebra structure |
| F_x flat over O_{S,s} implies N_q A-flat | The antecedent restricts the actual module stalk along `f.stalkMap x`; the consequent is `Module.Flat A (LocalizedModule (π z).asIdeal.primeCompl N)` with A-action `Module.compHom _ α` |
| Further affine elementary (T,t) over closed Spec A | `∀ T [IsAffine T] t v`, `Etale v`, the closed-point image equation and `IsIso (v.residueFieldMap t)` |
| C and base change map | Literally `T.presheaf.stalk t` and `T.fromSpecStalk t ≫ v` |
| Also C=A | Separate use of `localizedDevissageBaseChangeConclusions` for `R=Spec A`, `c=𝟙 _` and its closed point |

The auxiliary predicate spells out the remaining clauses, with no opaque assumptions:

- It quantifies over all cartesian presentations of the four changed schemes, their
  projections and the three horizontal maps; `IsPullback` witnesses and the two diagram
  equations specify exactly base change. Such presentations always exist. The universal
  formulation is independent of the choice of pullbacks; it does not assume a special
  neighbourhood satisfying the conclusions.
- `c r = s` and `IsIso (c.residueFieldMap r)` preserve the base marked point and field.
  The existential `x'`, `z'` project to the old marked points, satisfy
  `g' (i' z') = x'` and `h' (π' z') = r`, and retain the singleton π'-fibre.
  The residue-field maps of each of the four projections, and of g', are isomorphisms.
- The four existential fibre morphisms k are isomorphisms and satisfy
  `k ≫ old.fiberι = new.fiberι ≫ projection`. Because fibre inclusions are monic, these
  equations fix the canonical fibre comparisons; the full marked diagram commutes.
  Thus the marked fibre diagram and residue extensions are unchanged, rather than
  merely asserting that unrelated schemes or fields admit some isomorphism.
- It asserts `Etale g'`, the four finite-presentation/closed-immersion conditions on i',
  `IsFinite π'`, `SmoothOfRelativeDimension n h'` and `GeometricallyIntegral h'`.
- It asserts `IsIso` of both existing `moduleBaseChangeMap`s, for i and π. For i it also
  provides E' with the exact equation
  `beta_i ≫ E'.hom = p₁^*(E.hom) ≫ canonicalPullbackComparison`.
  The comparison on the right is built from `tensorPullbackSectionComp`, the equality
  `sqg.w`, and `eqToIso`. This specifies the claimed canonical i-isomorphism. For π,
  invertibility is asserted directly of the canonical beta map; hence it is precisely
  `(π_*G)_C ≅ π_{C,*}G_C`, not an arbitrary map or chosen isomorphism.
- Finite presentation near x' and near π'z' is expressed using open neighbourhoods and
  the existing `SheafOfModules.IsFinitePresentation` on `.over U`, with an iff.
- Flatness near the same two points is expressed using open neighbourhoods, actual
  tensor restriction and `IsFlatOver` for the composed structure map to R, with an iff.
  Since R is Spec C this is exactly flatness over C. Both clauses use the same marked
  points and the actual pulled-back modules.

Dependency declarations used (source signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; finite presentation also includes QC and QS.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the dependency's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`; their full
  signatures and local-presentation definitions were read in Mathlib's Generators
  and Quasicoherent modules. Coherence itself is not a hypothesis here.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` / `.Quasicoherent`:
  `IsFiniteType`, `IsFinitePresentation`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Sheaf.FieldTheory.PurelyTranscendentalExtension`:
  `Algebra.IsPurelyTranscendentalExtension` (allows an empty transcendence basis).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`: `IsFlatOver`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the actual
  `tensorPullback` and its section-normalized `tensorPullbackSectionComp`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`, `IsPullback` cartesian squares.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Properties` / `.Geometrically.Integral`:
  `IsIntegral` and `GeometricallyIntegral` (nonzero integral field-valued fibres).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic` and
  `Mathlib.Algebra.Module.LocalizedModule.AtPrime`: actual prime localization,
  `LocalizedModule`, with its canonical B-action, restricted along α.
- Canonical-map infrastructure: `Scheme.fromSpecStalk` and
  `IsLocalRing.closedPoint` (Mathlib Stalk), `RingedSpace.moduleStalkFunctor`
  (WeilConjectures.Algebra.Homology.ModuleStalkFunctor), `tilde` (Mathlib Modules.Tilde),
  and `moduleBaseChangeMap` (WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction,
  publicly used by the recorded affine-pushforward base-change theorem).

All stated non-Mathlib proof dependencies' recorded modules are imported privately:
ElementaryModuleDevissage, ElementaryDevissageFinitePresentation,
ElementaryDevissageFlatness, the upstream Modules.Tilde, ModulePullbackFiniteType,
AffinePushforwardBaseChange, QuasicoherentFiniteTypeAffine,
AffineChartRelativeFlatCriterion and AffineModuleGermLocalization. Mathlib permanence
and affine presentation facts are exposed by the corresponding morphism modules.
There is no unusable dependency binding and no dependency repair.

Edge cases checked before drafting and on the completed signature:

- Empty X, empty S or F=0 cannot meet the marked support hypothesis. No blanket
  nonemptiness/Noetherian/flatness assumption is added.
- n=0 is allowed; no positivity binder appears.
- Pure transcendence includes the trivial extension (empty basis).
- No flatness of F away from x is assumed; flatness at x occurs only as an implication.
- C=A is explicit, independently of the further-neighbourhood quantifier.
- Every further affine elementary neighbourhood is quantified over, including identity
  and arbitrary choices of the representative. No finite-presentation assumption on
  its local ring extension, or equality of unrelated universes, is imposed.
- Spec B is arbitrary affine, not a chosen affine open chart or a polynomial algebra;
  smoothness, finite presentation and finite generation have their recorded meanings.
- The beta maps are actual canonical maps and the pullback-composition normalization
  fixes E'; no arbitrary comparison-map hypothesis or `Nonempty`-chosen construction.

Searches made for an existing statement:

1. msearch.py / LeanFinder, query `localized elementary devissage quasi coherent module
   finite pushforward etale neighborhood flat finite presentation`: 8 hits on general
   finite-presentation/quasi-coherent sheaf APIs; no localized devissage theorem.
2. msearch.py / Loogle, query `AlgebraicGeometry.Scheme.fromSpecStalk,
   AlgebraicGeometry.SmoothOfRelativeDimension,
   AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap`: zero hits, unknown identifier
   for the project-only moduleBaseChangeMap (which was instead read in the source).
3. msearch.py / grep Mathlib AlgebraicGeometry, regex
   `devissage|fromSpecStalk|GeometricallyIntegral`: 25 hits, the existing geometric
   integrality and local-spectrum infrastructure, no matching theorem.
4. msearch.py / LeanSearch, query `elementary devissage finite type module etale
   neighborhood finite pushforward`: 8 hits on generic pushforward, finite-presentation
   and stalk APIs, no matching theorem.
5. rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
   localized devissage, devissage localization and the exact item id: no exact match.
   The nearby complete algebra devissage/projective localization statements concern
   a different construction. rg of the chosen declaration names found no collision.
6. Read the three existing elementary-devissage modules. The existence theorem gives
   the pre-localized diagram; the other two give its separate transfer properties.
   None includes this localized existence result together with arbitrary further
   elementary changes, canonical comparisons and the finite coordinate module.

Validation: scompile.py compiled the sandbox and named library module cleanly, each
in about 7 seconds, against the live published build. Earlier probes identified and
fixed the namespace ambiguity between scheme and module pullbacks, added the required
public module-stalk import, and explicitly set the category on the point-type
pullback. All cartesian-square binders are explicit (unused proof names use `_`).
The signature uses `autoImplicit false` and `relaxedAutoImplicit false` and no `let`.
All lines are at most 100 characters.

## Second reading by Q21

This is a second pass by the dispatched worker, not a claim of a separate reader:
the task explicitly prohibits starting other agents and assigns the independent
review to the maintainer. I reopened both the node and the finished module.

I checked the support and dimension subtype against the fibre of f at f(x), the
basepoint and residue-field maps of e, the actual local ring A, every arrow of the
commutative diagram, the singleton π-fibre, and the use of the canonical α-action on
N_q. The marking equations for x₁ and y are retained by writing them as i z and π z.
The A-flatness of N_q is conditional, whereas flatness of the smooth algebra B is
unconditional, exactly as in the node.

I then unfolded the complete helper predicate and checked the A and C applications.
The predicate includes both directions of each neighbourhood equivalence, all four
closed-fibre isomorphisms and all marked residue-field comparisons. During this pass
I added the explicit base `IsIso (c.residueFieldMap r)` clause so the unchanged-base-
residue-field assertion was also present. I checked the equation pinning E' to the
existing beta_i and the normalized composition maps, and the direct IsIso assertion
on beta_π. The seven cartesian squares are constraints on the presentations of
base change, not assumptions replacing the mathematical conclusions. Identity
presentations supply the C=A equivalences. There are no discarded cases, changed
statements, new independent notions, or outstanding statement disputes.
