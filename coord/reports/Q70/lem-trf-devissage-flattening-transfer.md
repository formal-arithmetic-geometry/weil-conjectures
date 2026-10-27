## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.exists_devissage_flattening_transfer`
in `Sheaf.TraceFormula.DevissageFlatteningTransfer`. Its only proof is `by sorry`.
No definition is introduced, and the item's only changed JSON field is `lean`.
No source statement correction, new node, or dependency repair is needed.

I read the nine-step DAG proof, its reviewed split, and Stacks flat.tex
`lemma-elementary-devissage` (057S), `lemma-devissage-finite-presentation` (057T),
and `theorem-flatten-module` (0815), especially its second proof paragraph.
The node is an auxiliary assertion expanding that paragraph, not the blueprint unit's
own statement. The Lean declaration does not add the stronger singleton-fibre or
purely transcendental extension conclusions of 057S, nor the marked-neighbourhood
conclusions of 057T: these are retained internally in the proof described in the docstring.

Hypothesis and conclusion correspondence (all objects have explicit universe `u`):

| Node text | Lean rendering |
| --- | --- |
| Scheme base S and source X | `{S X : Scheme.{u}}` |
| S quasi-compact and quasi-separated | `[CompactSpace S] [QuasiSeparatedSpace S]`; compactness has no Hausdorff assumption |
| f quasi-compact, locally of finite presentation | `(f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]` |
| F finite-type quasi-coherent module | `(F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]` |
| Quasi-compact open U in S | `(U : S.Opens) (_hU : IsCompact (U : Set S))` |
| F finitely presented on X_U | `_hfp : ((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation` |
| F flat over U | `_hflat : ((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFlatOver (f ∣_ U)`; both scheme and module are restricted to the given open |
| x in support of F_s, s=f(x) | `(x : X)` and `hx : ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x))` |
| Fibre module and local support dimension n | Tensor pullback along `f.fiberι (f x)`; `topologicalKrullDimAt` of the canonical fibre point in the subtype of nonzero stalks; `∃ n : ℕ` with equality to `(n : WithBot ℕ∞)` records its actual finite dimension, rather than assuming finiteness as a hypothesis |
| Affine pointed neighbourhoods (X₁,x₁), (T,t) | Existential `X₁ T`, `x₁ : X₁`; distinguished base point is `t = f₁ x₁`. `IsAffine X₁`, `IsAffine T`, `Etale g`, `Etale e`, `g x₁ = x`, and `e (f₁ x₁) = f x`. No residue-field isomorphism is imposed: the item says pointed etale, not elementary etale |
| e quasi-compact | `QuasiCompact e` |
| f₁ and fg=ef₁ | `(f₁ : X₁ ⟶ T)` and `g ≫ f = f₁ ≫ e` |
| Affine T-schemes Z,Y, with i and pi T-morphisms | Existential `Z Y`, maps `i : Z ⟶ X₁`, `π : Z ⟶ Y`, `h : Y ⟶ T`; `IsAffine Z`, `IsAffine Y`, and `i ≫ f₁ = π ≫ h`. The structure map of Z is `i ≫ f₁`, so the equation expresses precisely the T-morphism condition |
| Finitely presented closed immersion i | `IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i`; this is the Stacks finite-presentation convention in the dependency node |
| Finite pi | `IsFinite π` |
| Finite-type quasi-coherent G on Z | `(G : Z.Modules)`, `G.IsQuasicoherent ∧ G.IsFiniteType` |
| i_*G isomorphic to g^*F | `Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F)` in the actual module category |
| h smooth of relative dimension n | `SmoothOfRelativeDimension n h` |
| Geometrically integral fibres | `GeometricallyIntegral h`; Mathlib quantifies over all field-valued base points and hence every residue-field extension, without choosing an algebraic closure |
| N=pi_*G and U_T=e⁻¹U | The terms `((pushforward π).obj G)` and `(e ⁻¹ᵁ U)` occur literally throughout; no arbitrary replacement module or open is an input |
| N quasi-coherent and finite type | `∃ hN : ((pushforward π).obj G).IsQuasicoherent, ((pushforward π).obj G).IsFiniteType ∧ ...`; the existential proof `hN` is subsequently supplied to strict transform, and introduces no extra data because this is a proposition |
| N restricted over U_T finitely presented and flat | Both assertions use `(restrictFunctor (h ⁻¹ᵁ (e ⁻¹ᵁ U)).ι).obj ((pushforward π).obj G)`; flatness is `IsFlatOver (h ∣_ (e ⁻¹ᵁ U))` |
| Every U_T-admissible blowup, with its centre retained | `∀ B : IsAdmissible T (e ⁻¹ᵁ U)`. The existing datum supplies `B.I`, `B.finiteType`, `B.disjoint_support`, `B.I.blowup` and `B.I.blowupMap`. It never replaces the centre by the complement of U_T |
| Strict transforms on Y×_T T^b and X₁×_T T^b | The existing `@moduleStrictTransform Y T h B.I ...` and `@moduleStrictTransform X₁ T f₁ B.I ...` have exactly these fibre-product module categories |
| N^b flat iff (g^*F)^b flat | The final `↔` uses the respective `pullback.snd h B.I.blowupMap` and `pullback.snd f₁ B.I.blowupMap` as structure maps to the same blowup base |

Admissible blowup parametrization: the dependency's recorded `IsAdmissible` is a
retained centre datum, not an unstructured assertion about a morphism. Using its
canonical blowup loses no arbitrary isomorphic presentation of a blowup: a specified
isomorphism over T induces isomorphisms of both displayed fibre products, pulls the
supported-section kernel quotient to the corresponding transform, and preserves
relative flatness. This uses the exact same centre, including identity or empty
blowups, rather than choosing a centre from the morphism. No additional helper
construction or arbitrary map is introduced.

I read the recorded statement dependencies' signatures and docstrings at their
source files. The following are used directly (the conventions node has no
additional declaration):

- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` — `AlgebraicGeometry.LocallyOfFinitePresentation`
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension` — `topologicalKrullDimAt`
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale` — `AlgebraicGeometry.Etale`
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth` — `AlgebraicGeometry.Smooth`; also `AlgebraicGeometry.SmoothOfRelativeDimension`
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite` — `AlgebraicGeometry.IsFinite`
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` — `AlgebraicGeometry.IsClosedImmersion`
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` — `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`; its public import supplies the actual `tensorPullback` and Mathlib `pushforward`
- `def-weil-pbc-scheme-conventions`: convention-only record, rendered by the actual scheme/morphism classes, including all three finite-presentation conditions
- `def-weil-quasi-separated-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` — `AlgebraicGeometry.QuasiSeparated`
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType` — `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`
- `def-weil-pbc-module-finite-type-presentation`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` — `SheafOfModules.IsFiniteType`; also `SheafOfModules.IsFinitePresentation`
- `def-pc-scheme-module-flat-over`: `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` — `AlgebraicGeometry.Scheme.Modules.IsFlatOver`
- `def-nagata-admissible-blowup`: `WeilConjectures.Blowup.AdmissibleBlowup` — `AlgebraicGeometry.IsAdmissible`
- `def-trf-module-strict-transform`: `Sheaf.AlgebraicGeometry.ModuleStrictTransform` — `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform`

Additional existing interfaces used in the signature are
`Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent` /
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorPullback` and
`WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule` /
`AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_toModules_sheaf`.
The former supplies the already-proved quasi-coherence of g^*F to the strict-transform
interface. The latter translates the retained centre's existing finite-type
predicate into its module finite-type instance. These are existing derived facts,
not new notions or stronger hypotheses. Their imports are public because the
signature uses the resulting proof terms. `GeometricallyIntegral` is the existing
Mathlib class from `Mathlib.AlgebraicGeometry.Geometrically.Integral`.
The explicit support subtype follows exactly the already landed elementary
module devissage declaration and uses no new support definition.

All recorded proof-dependency modules are imported. Mathlib leaves without Lean
records are covered by their `mathlib_match` modules: FinitePresentation, FiniteType,
Affine, QuasiSeparated and the already-public imported dependencies. The docstring
carries all nine steps, including the affine section calculations, the finite
presentation checks on the whole open (rather than only at a marked point), and
the base-compatible affine flatness comparisons after blowup.

Edge cases checked before drafting and again on the final declaration:

- Empty X or zero F: no supported x satisfies hx; the assertion is vacuous, and no arbitrary dimension of empty support is asserted.
- Empty S: the same absence of supported x handles this case.
- n=0 is allowed by `n : ℕ`; there is no positivity assumption or use of dimension minus one.
- U empty: presentation and flatness assumptions are on the empty restriction; all retained finite-type centres are allowed.
- U=S: admissibility forces unit restriction everywhere, but the universal blowup statement still includes this case; neither density nor a nonempty boundary is assumed.
- Centres zero or unit, and empty or identity blowups, are not excluded from the universal quantifier when admissible. Relative flatness over an empty blowup is vacuous on both sides.
- No flatness, surjectivity, singleton-fibre or reducedness hypothesis is added to the blowup. No support identification of F_s with the whole fibre is assumed.
- There is no Noetherian or characteristic hypothesis; all schemes share an arbitrary explicit universe u, the same as the existing fibre/module interfaces. No smaller independent test-field universe or finite affine-cover index type is imposed.

Searches for an existing statement (2026-10-24, through the prescribed msearch.py
with group Q70 and this item):

- `grep` query `devissage|strictTransform.*flat|moduleStrictTransform.*IsFlatOver`: 0 hits. No candidate states the devissage/open-presentation/strict-transform flatness transfer assertion.
- `loogle` query `AlgebraicGeometry.Scheme.Modules, Module.Flat`: 0 hits. No candidate states the devissage/open-presentation/strict-transform flatness transfer assertion.
- `leanfinder` query `Elementary devissage of a finite type quasi coherent module preserves finite presentation and relative flatness and reflects flatness of strict transforms after admissible blowup`: 8 hits. Candidates: `SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation`, `SheafOfModules.quasicoherentDataOfIsFinitePresentation`, `SheafOfModules.QuasicoherentData.IsFinitePresentation`, `Module.Flat.exists_factorization_of_isFinitelyPresented`, `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`, `SheafOfModules.IsFinitePresentation.exists_quasicoherentData`, `AlgebraicGeometry.instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget`, `SheafOfModules.isFinitePresentation`. No candidate states the devissage/open-presentation/strict-transform flatness transfer assertion.
- `leansearch` query `A finite morphism in elementary devissage preserves finite presentation and relative flatness over an open and identifies flatness of strict transforms after blowup`: 8 hits. Candidates: `AlgebraicGeometry.instLocallyOfFinitePresentationMorphismRestrict`, `AlgebraicGeometry.Flat.instMorphismRestrict`, `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme`, `AlgebraicGeometry.IsFinite.instMorphismRestrict`, `AlgebraicGeometry.IsFinite.recOn`, `AlgebraicGeometry.Flat.flat_of_affine_subset`, `AlgebraicGeometry.instLocallyOfFinitePresentationResLE`. No candidate states the devissage/open-presentation/strict-transform flatness transfer assertion.

Direct rg searches: `devissage|[Dd]evissage` and
`devissage.*flatten|devissage_flattening|flattening.*devissage` in both
`lean/WeilConjectures` and `lean/Sheaf` found the existing elementary devissage,
finite-presentation and flattening modules but no declaration of this transfer
statement. The item-id search in `lean/WeilConjectures` returned no result.
Searches for `DevissageFlatteningTransfer|exists_devissage_flattening_transfer` in
`dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf` returned no
name collision. The node's recorded searches and reviewed split also distinguish
this assertion from the marked-neighbourhood devissage-flatness lemma.

Validation: scompile.py compiled the sandbox and target library module against
the published live server build with no errors or warnings (sandbox 7.5 s,
library 13.1 s). No local or global build was run.

No STATEMENT-DISPUTED fault was found. No dependency node or target statement is changed.

## Second reading by Q70

This is the author's final clause audit, not a claim that a second agent was
started: the dispatcher brief prohibits starting other agents and provides for
independent maintainer review of the delivered packet.
I reread the node and final Lean signature together. The pointed base point can
be eliminated in favour of `f₁ x₁`, since the source diagram makes this exactly
the required point; its image is explicitly constrained. Both T-scheme structure
maps agree through `i ≫ f₁ = π ≫ h`. All four affine conditions, both etale
conditions, quasi-compactness of e, all finite-presentation conditions on i,
and finite pi are present. F's input assumptions use X_U over U and N's output
conditions use Y_{U_T} over U_T, not the unrestricted original bases.
I checked the two final `IsFlatOver` predicates use different family projections
but the same retained centre and the same blowup base. The second module is
literally the tensor pullback of the original F. The hN binder supplies precisely
the asserted quasi-coherence and is not a new assumption. The natural number n
is the local dimension of the fibre support at the canonical lift of x, not of
X itself or of the total support. The full G finite-type/quasi-coherence assertion
and the actual i_*G isomorphism are retained. The proof imports and nine-step
proof docstring agree with the node's global-over-U argument. No mismatch needed
a statement change or a dependency repair. The retired CompactObject example
module was read together with its currently recorded upstream replacement.
