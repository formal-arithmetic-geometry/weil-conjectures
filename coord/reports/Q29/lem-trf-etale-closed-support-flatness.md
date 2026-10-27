## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleClosedSupportFlatness` states
`AlgebraicGeometry.Scheme.Modules.etale_closed_support_flatness`, with its single
proof `sorry`. The statement and all other existing node fields are unchanged;
only the item's `lean` record is supplied. There are no new definitions or nodes,
no dependency repairs, and no statement disputes.

The source read was Stacks Project `flat.tex`, Tag 057U,
`lemma-devissage-flat`, both its two equivalence triples and its complete proof.
The node isolates the etale-source/base and closed-support comparisons, omitting
the separate finite-pushforward comparison in that source. The existing parent
`ElementaryDevissageFlatness` was read as a consumer example; its additional
finite-type, affine, finite-presentation and residue-field hypotheses are not
introduced here.

Hypothesis and conclusion correspondence:

- All five schemes are explicitly bound as `{X S U T Z : Scheme.{u}}`, for an
  arbitrary explicitly declared universe `u`. The four morphisms are
  `(f : X ⟶ S) (a : U ⟶ T) (g : U ⟶ X) (e : T ⟶ S)`.
- The commutative diagram `fg = ea` is `_hcomm : g ≫ f = a ≫ e`, in Lean's
  order of composition. Etaleness is exactly `[Etale g] [Etale e]`.
- The closed immersion is `(i : Z ⟶ U) [IsClosedImmersion i]`.
- The modules are `(F : X.Modules) (G : Z.Modules)` with precisely the two
  hypotheses `[F.IsQuasicoherent] [G.IsQuasicoherent]`; neither finite type nor
  coherence is assumed. The dependency's broader finite-type conjunction is not
  used in place of quasi-coherence.
- The fixed O_U-linear isomorphism is `_hiso : (tensorPullback g).obj F ≅
  (pushforward i).obj G`. Thus H is always the actual canonical tensor pullback,
  not an additional arbitrary sheaf or a newly chosen object.
- The point is `(z : Z)`. The other points are written explicitly as `i z`,
  `g (i z)`, `a (i z)` and `f (g (i z))`. The last equals `e (a (i z))` by
  `_hcomm`; there is no extra point or point-equality hypothesis.
- The first conclusion conjunct is the equivalence of the F and H neighbourhood
  conditions. Each condition is `∃ V : <scheme>.Opens, <point> ∈ V ∧ ...`;
  its last clause is `((tensorPullback V.ι).obj <module>).IsFlatOver
  (V.ι ≫ <structure map>)`, with structure maps f and a respectively.
- The second conjunct repeats the H neighbourhood condition and equates it with
  the G condition on an open neighbourhood in Z. Its structure map is explicitly
  `V.ι ≫ (i ≫ a)`. Restriction to an open is the same recorded tensor pullback
  along its canonical inclusion, and flatness is the dependency's `IsFlatOver`.
- The third conjunct equates the F stalk at `g (i z)` over
  `S.presheaf.stalk (f (g (i z)))` with the H stalk at `i z` over
  `T.presheaf.stalk (a (i z))`. Each module stalk is the object of
  `RingedSpace.moduleStalkFunctor` and its base action is explicitly supplied
  by `ModuleCat.restrictScalars` along the respective scheme stalk map of f or a.
- The fourth conjunct equates that same H stalk condition with the G stalk at z,
  restricted along `((i ≫ a).stalkMap z).hom`. Its base ring is
  `T.presheaf.stalk ((i ≫ a) z)`, definitionally the stipulated local ring at t.
  Both conditions use Mathlib's `Module.Flat`, not flatness over the ambient
  scheme's own stalk ring. Two adjacent equivalences in each triple give exactly
  the requested three-way equivalence. There is no implication between the two
  separate triples.
- No cartesian-square, affine, finite-type, finite-presentation, residue-field
  isomorphism, or Noetherian assumption occurs. Every universe and variable is
  bound explicitly, with `set_option autoImplicit false` in the module.

Dependency declarations read and reused (all statement dependency modules are
public imports; modules needed only by the proof are ordinary imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `SheafOfModules.IsQuasicoherent`, the clause of `pqf-def-coherent` needed here;
  its `IsQuasiCoherentFiniteType` conjunction is not assumed.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the normalized
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
  publicly imported explicit `tensorPullback`; the corresponding Mathlib
  `AlgebraicGeometry.Scheme.Modules.pushforward` has the source's section formula.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`, the affine-section predicate.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`:
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`.
- `Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover`:
  `AlgebraicGeometry.relative_flatness_source_cover`.
- `Sheaf.TraceFormula.EtaleLocalRingFlatness`:
  `AlgebraicGeometry.etale_local_ring_flatness`.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`:
  `AlgebraicGeometry.Scheme.Hom.isOpenMap`, specializing using etaleness.
- `WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks`:
  `AlgebraicGeometry.closedImmersion_pushforward_stalks`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and `Module.Flat`.

Edge cases checked mathematically before writing:

- If Z is empty, no z can be supplied, so the point-indexed assertion is vacuous;
  there is no hidden nonemptiness hypothesis on a scheme.
- For zero F and G, all stalks are zero and both triples hold, with whole-scheme
  open neighbourhoods. No nonzero module condition was inserted.
- When the etale maps or the support immersion are identities the relevant
  comparisons specialize to restriction/identity comparisons.
- The nonflat closed immersion Spec(F_2) → Spec(Z) is allowed. The comparison
  uses the same base local ring on both sides; it never claims that the support
  immersion itself is flat. For the identity base map over Spec(Z), F = Z/2
  and G = F_2 make the two corresponding flatness conditions both fail.
- Etale maps with nontrivial residue-field extensions remain allowed; no stalk
  or residue-field isomorphism is assumed for g or e.
- Stalk flatness need not be open for an arbitrary quasi-coherent module.
  The conclusion therefore contains two distinct triples; the documented proof
  uses open images and the closed-subspace topology, not openness of a flat locus.
- Opens are arbitrary and are not required affine or quasi-compact; no
  finiteness assumption is used to shrink the neighbourhoods.

Searches (the msearch calls were fresh, logged under Q29 and this item):

- `leanfinder`: "Relative flatness through an etale source and base diagram
  agrees with flatness on a closed support, on neighborhoods and at stalks".
  Eight hits, including `AlgebraicGeometry.Flat.iff_flat_stalkMap`,
  `Flat.of_stalkMap`, `Flat.stalkMap`, `flat_iff` and `RingHom.Etale.propertyIsLocal`.
  These concern flat morphisms or algebraic local properties, not this theorem.
- `loogle`: `Module.Flat, AlgebraicGeometry.Etale`. Zero hits.
- `grep` of Mathlib/AlgebraicGeometry through msearch:
  `flat.*(pushforward|closedImmersion|etale)|((pushforward|closedImmersion|etale).*flat)`.
  Eleven hits in WeaklyEtale, Etale and LocalFlatDescent, none the desired module
  neighbourhood/stalk comparison.
- `leansearch`: "Relative flatness of a quasi coherent module on an etale diagram
  and a closed support, both on neighborhoods and on stalks". Eight hits,
  including `Module.Flat.of_isLocalizedModule`, `Module.flat_of_isLocalized_span`,
  scheme-flatness characterizations and faithfully flat modules; no exact match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for
  `etale.*closed.*flat|flat.*closed.*support|etale_closed_support_flatness`:
  only unrelated etale coefficient-flatness or smooth-neighbourhood results.
  `grep -rn` for this node id in `lean/WeilConjectures` returned no result.
  Further neighbourhood/IsFlatAt searches found the existing, stricter parent
  `Sheaf.TraceFormula.ElementaryDevissageFlatness`, whose neighbourhood notation
  and explicit stalk scalar restrictions this statement follows. No full match.

Validation: the delivered module compiles on the server through `scompile.py`
against the live published build, with no errors or warnings. Its sole postponed
proof has the complete five-step source-based proof in its declaration docstring.
The node's Lean signature is extracted verbatim from the file. Dry-run and final
preflight/compile are performed through the prescribed `deliver2.py` wrapper.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
