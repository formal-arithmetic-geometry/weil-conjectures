## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleStrictTransformFlatPullback` states
`AlgebraicGeometry.Scheme.Modules.existsUnique_moduleStrictTransform_flatPullback`.
Its only theorem has proof `sorry`; its two helpers construct actual maps/isomorphisms.
No statement correction, new node, or dependency repair was needed.

Hypothesis and conclusion correspondence:

- Schemes X, S, Y, T: `{X S Y T : Scheme.{u}}`. The universe u is explicit and arbitrary.
- The four morphisms: `(f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)`.
- Commutativity fj = eg: `(h : j ≫ f = g ≫ e)`.
- Flatness of e and j: `[Flat e] [Flat j]`. No flatness of f or g is assumed.
- The finite-type quasi-coherent ideal: `(I : S.IdealSheafData)` and
  `[I.toModules.IsFiniteType]`. IdealSheafData already encodes quasi-coherence.
- The two blowups are `I.blowup` and `(I.comap e).blowup`, with their `.blowupMap`.
  Here `I.comap e` is precisely the extended ideal on T.
- The specified flat base-change comparison is `(I.blowupFlatBaseChangeIso e).hom`.
  The upstream pullback has factors in the order `pullback I.blowupMap e`, so its
  first projection gives the map to the old blowup and its second gives the map to T.
  This reverses only the presentation of the two factors, not the mathematical map.
- The induced map j^b is `moduleStrictTransformFlatPullbackMap f e g j h I`.
  It is the pullback lift with first component `pullback.fst ... ≫ j` and second
  component `pullback.snd ... ≫ bc_e ≫ pullback.fst I.blowupMap e`.
  Its commutativity proof uses h, the pullback condition and the existing over-T
  identity `blowupFlatBaseChangeIso_hom_snd`; there is no arbitrary map parameter.
- Every quasi-coherent module: `(F : X.Modules) [F.IsQuasicoherent]`.
- The left side of the isomorphism is `(tensorPullback j^b).obj
  (moduleStrictTransform f I F)` using exactly the recorded tensor pullback.
- The right side is `cokernel (kernel.ι (moduleStrictTransformRestriction g
  (I.comap e) ((tensorPullback j).obj F)))`. This is literally the defining body
  of `moduleStrictTransform g (I.comap e) ((tensorPullback j).obj F)`, with the
  correct centre retained. Unfolding this body removes the need to supply extra
  typeclass binders for finiteness and quasi-coherence of transported objects;
  neither a stronger hypothesis nor a replacement construction is introduced.
- The ordinary-pullback comparison is `moduleStrictTransformFlatPullbackSourceIso`.
  It is the inverse normalized composition comparison for j^b then p_X, followed
  by transport along `pullback.lift_fst`, then the normalized comparison for p_Y
  then j. It thus identifies `(j^b)^*p_X^*F` with `p_Y^*j^*F` canonically.
- Quotient compatibility is the displayed equation
  `(tensorPullback j^b).map (moduleStrictTransformπ f I F) ≫ θ.hom =
  sourceIso.hom ≫ cokernel.π (...)`.
  The last cokernel projection is the target's defining strict-transform quotient.
- Canonicity is rendered as `∃! θ : ... ≅ ..., ...` with this equation. Uniqueness
  follows from the epimorphic pulled-back quotient, as in the node's proof.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`,
  `Flat.isStableUnderBaseChange`, `flat_iff`, and `Flat.flat_appLE`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the finite-type/quasi-coherent
  notions, through `SheafOfModules.IsFiniteType` and `.IsQuasicoherent`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `.blowupMap`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, `pullback.lift`, `pullback.condition` and `pullback.lift_fst`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: `moduleStrictTransform`,
  `moduleStrictTransformRestriction`, and its actual supported-section-kernel quotient.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the upstream
  `tensorPullback` and the section-normalized `tensorPullbackSectionComp`.
- `WeilConjectures.Blowup.FlatBaseChange`: `blowupFlatBaseChange`,
  `blowupFlatBaseChangeIso`, and `blowupFlatBaseChangeIso_hom_snd`.
  The two DAG nodes have no lean record but have closed slopmaster2 audit records
  naming exactly these declarations, so they are used directly without re-recording.
  This module is absent in the older local checkout; its full live source was read
  with `scompile.py --source WeilConjectures.Blowup.FlatBaseChange`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel`: `moduleStrictTransformπ`
  and `moduleStrictTransform_properties` (proof dependency, quotient-kernel properties).
- `WeilConjectures.Blowup.Principalization`: `isInvertible_comap_blowupMap`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.isBasis_affineOpens`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`:
  `exists_map_eq_pow_smul_of_isAffineOpen` and
  `exists_pow_smul_eq_zero_of_isAffineOpen`.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSectionsBijective`:
  `tensorPullback_affine_sections_bijective`; its live source was read with
  `scompile.py --source`, including the full signature and unit normalization.
- `Mathlib.RingTheory.Flat.Basic`: `Module.Flat.lTensor_exact`, `.rTensor_exact`,
  and preservation of injectivity, used in the documented affine proof route.

The module docstring cites the source tags. The theorem docstring carries all four
proof steps: identify the base change and exceptional loci, identify the ordinary
pullbacks, compute the supported kernel by affine power torsion and flat tensor
exactness, and descend to the unique quotient isomorphism. The two map helpers are
part of the canonical comparison in this node, not independent notions.

Sources opened: divisors.tex at definition-strict-transform (080D),
lemma-flat-base-change-blowing-up (0805), and lemma-strict-transform-flat (080F);
flat.tex at lemma-flatten-module-etale-localize (0814), especially proof paragraph 1;
properties.tex at lemma-sections-supported-on-closed-subset (07ZP).

Edge cases checked mathematically before writing: empty schemes and the zero module
are allowed; I = 0 gives an empty blowup, so the comparison holds in the zero module
category; I = O_S has empty centre, so the supported kernel vanishes and the result
reduces to ordinary pullback composition. For identity e or j the same specified
construction still applies, without special choices. There is no noetherian,
quasi-compact, finite-presentation, nonempty or cartesian-square hypothesis. Only
commutativity of the square is required; j^b becomes a base change of j using the
flat blowup comparison. Flatness of j is essential: for multiplication by p over
Spec Z and reduction modulo p, power-torsion kernels need not commute with tensor.

Searches for existing statements (all through the authorized msearch wrapper):

- LeanFinder, `strict transform sheaf flat pullback`: eight results concerning
  flat morphisms, restriction and stalk maps, none giving the strict-transform theorem.
  An earlier longer query was interrupted with the provider failure and did not
  return a recoverable session; the shorter successful query supplies the result.
- Loogle, `"strictTransform"`: zero hits.
- Mathlib grep, `moduleStrictTransform|strict_transform|strict transform`: zero hits.
- Source/project rg, `moduleStrictTransform|lem-trf-module-strict-transform-flat-pullback`:
  upstream local source has no match; side source has the definition, kernel theorem,
  universal exactness, affine pushforward, Cartier-factor and flattening consumers,
  but no statement of this flat pullback comparison. Those existing definitions
  are reused. Live source inspection found the exact audited blowup comparisons.

Validation: scompile.py checked both the sandbox module and its actual library
module path cleanly, each in approximately three seconds. No errors or warnings.
The only postponed theorem is the delivered DAG item's theorem. No disputed statement.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
