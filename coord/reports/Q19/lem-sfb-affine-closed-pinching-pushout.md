## Worker report

The module `Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout` states
`AlgebraicGeometry.isPushout_spec_pullbackCone_of_surjective`, with its sole proof
`sorry`. No new definitions, helper theorems, dependency modules, or node corrections
are needed. The item node is changed only in `lean`.

The previous worker's stale-assignment conclusion confused the completed stage-1
split with a completed stage-2 statement: the current item has a seven-step proof,
reviewed by L for group NO, but no `lean` record. This delivery preserves that split
and supplies its missing statement.

Clause-by-clause correspondence:

- Commutative rings with identity A, D, T: `{A D T : CommRingCat.{u}}`.
  These bundled rings do not carry a `Nontrivial` requirement.
- The ring maps α and β: `(α : A ⟶ D) (β : T ⟶ D)`; these are unital
  commutative ring homomorphisms.
- Surjectivity of α: `(hα : Function.Surjective α.hom)`. There is no
  restriction on β.
- The displayed matching-pairs ring P with componentwise operations: Mathlib's
  `(CommRingCat.pullbackCone α β).pt`, not a newly defined notion or a chosen
  abstract pullback. Reading Constructions.lean:450–460 shows that it is exactly
  `RingHom.eqLocus (α.hom.comp (RingHom.fst A T))
  (β.hom.comp (RingHom.snd A T))`, equipped with its subring commutative-ring
  instance. Its elements are the pairs (a,t) satisfying α(a) = β(t).
- E = Spec D, Y = Spec A, W = Spec T: the source and targets of `Spec.map α`
  and `Spec.map β`. Q = Spec P is the common target of the other two displayed
  arrows, inferred from the concrete cone point.
- The canonical arrows E → Y and E → W: `Spec.map α` and `Spec.map β`.
  The arrows Y → Q and W → Q are respectively
  `Spec.map (CommRingCat.pullbackCone α β).fst` and the analogous `.snd`.
  The cone implementation shows these ring maps really are the coordinate
  projections restricted to the matching-pairs subring.
- These four arrows form a pushout square: precisely the conclusion `IsPushout`
  on those arrows, in `AlgebraicGeometry.Scheme.{u}`.
- For EVERY scheme Z and compatible maps Y → Z, W → Z there is a unique
  compatible Q → Z: this is the universal property built into `IsPushout`,
  not an affine-target assertion. Its definition extends `CommSq` and asserts
  `Nonempty (IsColimit (PushoutCocone.mk ...))`. The `IsColimit` fields are
  the factorization, its compatibility, and its uniqueness for every cocone
  in the category of schemes.
- No finiteness, Noetherianity or nonzero-ring assumption: no corresponding
  binder is present. The universe `u` and every object and variable are explicit;
  `set_option autoImplicit false` prevents accidental implicit assumptions.

Dependencies used:

- `def-weil-affine-spectrum`: recorded module `Mathlib.AlgebraicGeometry.Scheme`,
  declarations `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
  Their complete definitions/docstrings were read at Scheme.lean:469–480.
- `def-weil-pbc-category-colimit`: recorded module
  `Mathlib.CategoryTheory.Limits.HasLimits`, with `Cocone`, `IsColimit`, and
  `colimit`; `IsPushout` uses this same `IsColimit`, specialized to a span.
  Read HasLimits.lean:173–193, IsLimit.lean:62 onward, and
  Shapes/Pullback/IsPullback/Defs.lean:64–81. The filtered-colimit part of this
  general dependency is irrelevant to this finite pushout.
- Additional existing construction: `CommRingCat.pullbackCone`, from
  `Mathlib.Algebra.Category.Ring.Constructions`, full definition and docstring
  read at lines 447–460. This is the concrete matching ring the node specifies,
  so no extra definition node or private ring construction is necessary.
- Proof dependencies already stated in Mathlib are imported without `public`:
  `Mathlib.Algebra.Module.LocalizedModule.Exact`,
  `Mathlib.AlgebraicGeometry.AffineScheme`,
  `Mathlib.RingTheory.Spectrum.Prime.Topology`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, and
  `Mathlib.AlgebraicGeometry.Gluing`. They correspond, respectively, to exact
  localization, the affine-open basis, the principal-open basis, localization
  open immersions and the definition of open immersions, and scheme-morphism
  gluing. `lem-sfb-fibre-product-spectrum-topology` has no recorded Lean module
  at the time of this delivery, so there is no such proof import yet. Its place
  in the proof is documented explicitly in the theorem's docstring.

Source and edge cases:

Read `literature/stacks-project/more-morphisms.tex`,
`lemma-basic-example-pushout` (Tag 0ET0), beginning at line 4101. Its A′, A, B,
B′ correspond to this node's A, D, T, P (with the two factors interchanged in
Stacks' notation). It assumes precisely a surjection A′ → A and any B → A.
The seven proof steps in the theorem docstring preserve the node's localized
matching-ring and principal-chart scheme-morphism gluing argument.

- D = 0: every pair matches, P = A × T; the square gives the disjoint union of
  the two spectra, with empty E. Both the construction and conclusion include it.
- α an isomorphism: P is canonically T, and the pushout reduces to W.
- A = 0: a unital surjection forces D = 0, and P is canonically T; again valid.
- T = 0: its unital map to D forces D = 0, and P is canonically A; valid.
- Both A and T zero: P is zero, so every scheme in the square is empty and the
  empty-source universal property is included.
- Arbitrary target Z: `IsPushout` is in Scheme, with no affine, separated or
  quasi-separated target hypothesis. Affine intersections are not assumed
  affine in the proof plan; a smaller affine neighbourhood is chosen instead.
- Nilpotent localizing element: the docstring's localization step explicitly
  includes this case, as does the ring construction with zero rings allowed.

Searches performed for this delivery:

1. `msearch.py ... leanfinder` with query “The spectrum of a fibre product of
   commutative rings over a surjective map is a pushout of schemes”: 8 hits,
   headed by `AlgebraicGeometry.isPullback_Spec_map_isPushout`,
   `isPullback_SpecMap_pushout`, `isPullback_Spec_map_pushout`, and
   `isPullback_SpecMap_of_isPushout`. These go from a RING pushout to a SCHEME
   pullback; none supplies this closed-pinching scheme pushout.
2. `msearch.py ... loogle` query `AlgebraicGeometry, "pushout"`: 0 hits,
   diagnostic `unknown identifier 'AlgebraicGeometry'`; this malformed broad
   query is not evidence of absence.
3. `msearch.py ... grep` query `fiberProduct|fibreProduct|pinching|IsPushout`
   under `AlgebraicGeometry`: 25 hits, concerning scheme pullbacks from ring
   pushouts, flat base-change sections, and gluing. No matching theorem.
4. `msearch.py ... loogle` query `"CommRingCat.pullbackCone"`: exactly 2 hits,
   `CommRingCat.pullbackCone` and `CommRingCat.pullbackConeIsLimit`. This found
   the explicit matching ring and its canonical projections used here.
5. `rg` in project `lean/WeilConjectures` and `lean/Sheaf` for
   `fiberProduct|fibreProduct|pinching|Pinching|spec.*[Pp]ushout|[Pp]ushout.*spec|[Pp]ushout.*Spec`:
   specialized affine-transition matching subalgebras, formal-gluing pullback
   cones, curve contractions, and ring pushout/Spec pullback results, but no
   theorem stating the unrestricted affine closed-pinching pushout.
6. Exact item-id search in both source roots found no declaration. A further
   search for the new theorem name and `isPushout.*[Ss]pec|[Ss]pec.*isPushout`
   in Mathlib AlgebraicGeometry and both project roots found no collision or
   matching theorem. Existing similarly named results assert the opposite
   categorical direction, or concern global sections of a flat square.

No statement dispute or mathematical node fault was found. All definitions used
have actual data in Mathlib. This delivery adds only the single postponed
statement matching the existing DAG node.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
