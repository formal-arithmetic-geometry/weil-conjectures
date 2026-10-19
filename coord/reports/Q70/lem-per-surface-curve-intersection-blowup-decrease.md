## Worker report

The module `Sheaf.AlgebraicGeometry.CurveIntersectionBlowupDecrease` states
`AlgebraicGeometry.Scheme.IdealSheafData.curve_intersection_blowup_decrease`, with
one postponed proof, and defines its local intersection multiplicity by an actual
quotient and `Module.length`. Source read: Stacks `resolve.tex`, the paragraph
`equation-multiplicity` and the complete lemma and proof of Tag 0BI7, locally at
lines 4110–4175. No statement correction, new DAG node, or dependency repair is needed.
The stage-1 review PASS does not provide a stage-2 statement: the live item has no
`lean` record. This delivery changes only that record.

Hypotheses and objects, matched in order:

- Locally Noetherian scheme: `{X : Scheme.{u}} [IsLocallyNoetherian X]`.
- Closed subschemes: `Y Z : X.IdealSheafData`, with their canonical closed
  immersions `Y.subschemeι` and `Z.subschemeι`. Quasi-coherent ideals encode all
  closed subschemes; there is no reducedness assumption on Z.
- Integral curve: `[IsIntegral Y.subscheme]` and
  `hDim : topologicalKrullDim Y.subscheme = 1`. This is the scheme dimension,
  rather than dimension of just a chosen stalk or global section ring.
- The point belongs to Y: `p : Y.subscheme`; its ambient point is `Y.subschemeι p`.
  Closedness is `hp : IsClosed ({Y.subschemeι p} : Set X)`.
- The point belongs to Z: `hpZ : Y.subschemeι p ∈ Z.support`.
- Regularity at the point: `[IsRegularLocalRing (Y.subscheme.presheaf.stalk p)]`.
  Regularity of the whole curve or ambient scheme is not assumed.
- Generic point missing Z: `η : Y.subscheme`, `hη : IsGenericPoint η Set.univ`,
  and `hηZ : Y.subschemeι η ∉ Z.support`. An integral scheme has a unique generic
  point, so binding it with its defining property adds no mathematical restriction.
- Blow up the reduced point: `C : X.IdealSheafData` and
  `hC : C = vanishingIdeal ⟨{Y.subschemeι p}, hp⟩` explicitly fix C to the
  canonical reduced closed-point ideal. Universal quantification over this C with
  its defining equality is exactly the assertion about that ideal, not an extra
  geometric hypothesis. No arbitrary ideal with merely the same support is allowed.

Definition and conclusions, matched clause by clause:

- `localIntersectionMultiplicity I J x` is `Module.length (X.presheaf.stalk x)`
  of its quotient by the supremum of the germ images of `(I ⊔ J).ideal U`, over
  all affine neighbourhoods U of x. These images form the stalk ideal of I+J:
  affine opens are a neighbourhood basis, and every ideal stalk section is locally
  a germ of an ideal section. Thus the quotient is precisely O_(Y∩Z,x), with its
  ambient local-ring module structure, rather than a tensor or derived intersection.
  Sum of the ideals occurs explicitly before taking germs. The construction uses
  no choice from a postponed existence theorem, and contains no postponed data.
  This helper belongs to the multiplicity notion explicitly introduced in this item;
  it is listed in `lean.declarations` and has the item's source/blueprint docstring.
- Positive finite integer: the first two conjuncts are `0 < ...` and `... < ⊤`.
  The value is in `ℕ∞`, so these are exactly positivity and finite integer length.
- Blowup: `C.blowup` and `C.blowupMap` are the recorded glued blowup.
- Strict transforms: use the recorded `strictTransform` construction and its maps.
  The kernel of `strictTransformMap ...` represents its actual closed subscheme
  of the blowup; a closed immersion has exactly this scheme-theoretic image.
  These are not topological closures substituted for scheme-theoretic closures.
- The map Y′ → Y is an isomorphism: `IsIso (strictTransformToSource
  Y.subschemeι C.blowupMap C.support.compl)` is the third conjunct.
- Exceptional divisor: the total-transform centre ideal `C.comap C.blowupMap`.
- Single intersection point: existential `q : C.blowup` with the equality of
  the intersection of the two closed supports to `{q}`. This says both existence
  and uniqueness; it does not incorrectly require the full intersection scheme
  to have a one-point underlying type definitionally.
- Exceptional multiplicity one: the next conjunct applies the same local
  multiplicity definition to the strict-transform ideal and exceptional ideal.
- Conditional strict decrease: membership of q in the Z′ ideal's support implies
  its multiplicity with Y′ is strictly smaller than the original multiplicity.
  The nonintersection case is not restricted or asserted to be an intersection.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, supplied by the canonical subscheme immersions.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`; the scheme's global
  dimension is the corresponding `topologicalKrullDim` from
  `Mathlib.Topology.KrullDimension`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  read with its imported ring clause `IsRegularLocalRing` from
  `Mathlib.RingTheory.RegularLocalRing.Defs`. Only that local ring clause is needed
  here; the regular-scheme predicate is not imposed on X or Y.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, with its `blowupMap`.
- `WeilConjectures.Compactification.StrictTransform`:
  `AlgebraicGeometry.strictTransform`, `strictTransformMap`,
  `strictTransformToSource`.
- `Mathlib.RingTheory.Length`: `Module.length`. This dependency has a precise
  `mathlib_match`; it needs no artificial `lean` record repair.

The remaining imports follow the node's stated proof dependencies: invertible-centre
blowup, affine chart algebra and principalization, global principalization,
strict-transform/blowup comparison, the affine extended-ideal calculation, regular
local dimension-one normality, DVRs, and finite length of a principal quotient.
Transitive imports already supply the gluing, affine chart definitions, invertible
ideal, scheme-theoretic image and regular-scheme modules. Their modules are not
redefined. The theorem's docstring records the complete eight-step proof plan,
including the uniformizer chart map, the equation f/t in the strict-transform
ideal, and the submodule-chain argument establishing the strict inequality.

Edge cases checked mathematically:

- Empty ambient scheme or empty Y cannot supply the stated integral curve and point.
  No separate nonemptiness or Noetherian/quasi-compactness hypothesis is introduced.
- The theorem is local-Noetherian, not just Noetherian; no global compactness used.
- If original length is one, the strict transforms cannot meet at q. The final
  clause is conditional, so correctly permits this transverse case.
- In the plane, Y=(y), Z=(y-x^r) at the origin has original length r and transformed
  length r-1 when r>1. For r=1 the strict transforms separate. Z=(y,x^r) gives the
  same test with a nonreduced closed subscheme; no integrality of Z was imposed.
- X=Y, a regular integral curve: blowing up its reduced point is the identity;
  the exceptional centre still has intersection length one, and a point-supported
  Z has empty strict transform. The statement covers this case.
- Infinite original length is excluded by a conclusion, not smuggled into a
  hypothesis. The multiplicity definition itself allows both zero and infinite length.
- The generic point cannot be the closed point of this dimension-one integral curve.
- The only universe is explicitly declared u; there are no auto-bound variables.

Searches made before writing:

- `msearch.py` LeanFinder: “Blowing up a closed point on a regular curve lowers
  local intersection multiplicity and meets the exceptional divisor transversely”.
  Returned unrelated dimension/curve facts, no matching geometric assertion.
- `msearch.py` Loogle: `"blowup"`: zero hits.
- `msearch.py` Mathlib grep in AlgebraicGeometry:
  `intersection.?multiplicity|strictTransform|exceptionalDivisor`: zero hits.
- `msearch.py` LeanSearch: “The length of the scheme theoretic intersection of
  two closed subschemes at a point is the length of the local ring modulo the sum
  of their ideals”. Eight hits included `IdealSheafData.subscheme`, zero-locus
  identities, and stalk local homs; none defined this local multiplicity.
- `msearch.py` LeanFinder: “Ideal of a reduced closed point on a scheme and local
  intersection multiplicity of closed subschemes”. Eight hits included vanishing
  ideals, generic-point and residue-field facts; none was the item or its multiplicity.
- `rg` over project `lean/Sheaf` and upstream `WeilConjectures` for
  `intersectionMultiplicity|intersection_multiplicity|lem-per-surface-curve-intersection-blowup-decrease`:
  only the parent embedded-resolution docstring mentions this item; no declaration.
- `rg` over those same source trees for point vanishing ideals found the existing
  `vanishingIdeal ⟨{p}, hp⟩` usage in curve/divisor modules, reused here without
  defining another point ideal. Searches for a local-intersection multiplicity
  definition and the proposed full declaration names in the upstream name index
  found no competing notion or declaration.
- Read the existing strict-transform, gluing, regular-scheme, ideal-sheaf and
  Mathlib declaration signatures/docstrings. Ideal-stalk calculations in
  `IdealModuleProductExactCalculus` are private lemmas, not an existing global
  multiplicity definition; no private lemma is imported as an interface.

Validation: the delivered module compiled cleanly through `scompile.py`, both as
sandbox module and with its proposed library module name (3.1 s and 2.8 s).
No warning, error, disputed statement, or dependency interface fault was found.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
