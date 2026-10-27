## Worker report

The module `Sheaf.AlgebraicGeometry.NeronDvrPointCriterion` states
`AlgebraicGeometry.neron_mappingProperty_iff_dvr_points`, with its proof `sorry`.
It adds no definitions, helper theorems, or nodes and changes only the item's `lean` record.
The module docstring explains the canonical identification used for points. The theorem
has a nine-step natural-language proof following all nine steps of the DAG node.

Source checked directly: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §10.1,
Proposition 2 and proof, printed p.290, scan page index 296:
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf#page=297
The source defines “essentially smooth” by being a local ring of a smooth scheme.
The proposition tests surjectivity of points over precisely those local DVR extensions.
The existing node additionally specifies a commutative group and a finite-type generic fibre;
these are retained. No statement correction or disputed statement is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The DVR R is `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  Mathlib's class is exactly the local PID, not a field, in the dependency definition.
- The fraction field is `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`.
  This allows any chosen fraction-field realization, rather than requiring a particular
  construction. The base is `Spec (CommRingCat.of R)`.
- N as an S-scheme is `N : Over (Spec (CommRingCat.of R))`; N.hom is its structure map.
  `[CommGrpObj N]` supplies multiplication, inverse, identity, and commutative group laws
  in this over category. Products there are fibre products over S.
- Smoothness is `[Smooth N.hom]`; separation is `[IsSeparated N.hom]`, whose field is
  closed immersion of the diagonal, not an absolute separatedness condition.
  `[LocallyOfFiniteType N.hom]` retains the stated locally finite type hypothesis.
- G is the actual generic fibre
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N`.
  Its finite type hypothesis is rendered by `[QuasiCompact (...).hom]`, together with
  the locally finite type property inherited by base change from N (also implied by its
  smoothness). Mathlib defines finite type as locally finite type plus quasi-compact.
  There is no `[QuasiCompact N.hom]` assumption.
- Clause (i) quantifies over every `X : Over (Spec (CommRingCat.of R))` and every proof
  `Smooth X.hom`. Its displayed `Function.Bijective` is applied to
  `fun f : X ⟶ N ↦ (Over.pullback ...).map f`.
  Thus its domain is Hom_S(X,N), its codomain is Hom_K(X_K,G), and its function is
  exactly restriction/base change, not an arbitrary bijection of these sets.
- Clause (ii) quantifies over `A : Type u`, with commutative-ring, domain and DVR instances,
  and `φ : R →+* A`, with both `IsLocalHom φ` and `Function.Injective φ`.
  Neither extension condition was dropped or inferred from an unrelated property.
- The “local ring at a point of a smooth R-scheme” condition is the existential
  `∃ (Y : Over (Spec ...)) (_ : Smooth Y.hom) (y : Y.left)
  (e : Y.left.presheaf.stalk y ≃+* A), ...`.
  The following equality
  `Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.left.fromSpecStalk y ≫ Y.hom =
  Spec.map (CommRingCat.ofHom φ)`
  requires compatibility with the actual R-algebra structure φ. Consequently an abstract
  ring isomorphism with a stalk for a different R-action does not qualify.
- The surjectivity in (ii) is `Function.Surjective` on precomposition by the canonical
  `Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))`, bundled in the over
  category using `Over.homMk ... rfl`. The domain is precisely
  `Hom_R(Spec A,N)`; its codomain is
  `Hom_R(Spec (FractionRing A),N)` for the composite structure map R → A → Frac A.
  This is canonically `G(Frac A)`: injectivity of φ gives the unique extension
  K → Frac A, and the pullback universal property identifies a morphism into N with
  that morphism into G over K. This is exactly the source's G(R') → G(K') presentation
  (where source G denotes the whole model); it is not a stronger or weaker point test.
- The conclusion uses `↔`, hence includes both directions. Saying that (i) is the
  Néron lft mapping property is terminology for this very bijectivity assertion.
  No separate arbitrary “Néron” predicate has been introduced.
- The final negative hypotheses clause is respected: there are no excellence,
  completeness, residue perfection, connectedness, properness, or quasi-compactness
  assumptions on N. In particular there is no finite type assumption on N itself.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec`, and `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, through the diagonal field of
  `AlgebraicGeometry.IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded scheme
  base-change interface explicitly uses `CategoryTheory.Over.pullback` and its map;
  that same existing construction is used here. Its primary module declaration is
  for module base change, and is not mistaken here for the scheme base change.
- Additional existing Mathlib notions: `CategoryTheory.CommGrpObj` from
  `Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_`; products in `Over` from
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`;
  `AlgebraicGeometry.Scheme.fromSpecStalk` from `Mathlib.AlgebraicGeometry.Stalk`;
  `IsLocalHom`; `FractionRing` and `IsFractionRing` from the localization API.
  These are reused directly, with no copied group, fraction-field or stalk definitions.

All recorded, stated proof-dependency modules are imported privately: DVR TFAE,
IsRegularScheme, RegularRingNormal, RegularRingSmoothAscent, Noetherian,
NormalTopologicallyNoetherianComponents, AffineScheme, FinitePresentation, Regular,
Gluing, KrullsHeightTheorem and FibreStalkQuotient. Smooth-flat and separated-dominant
extension are already in the public smooth/separated imports. The two proof nodes
`lem-trf-smooth-reduced-dense-pullback` and `lem-sfb-relative-group-weil-extension`
have no recorded Lean declaration; they are named in the proof docstring and need
no invented import. Their statements are not prerequisites for typing this statement.

Edge cases checked before writing:

- Empty smooth X: the clause still quantifies over it; both Hom sets are singleton.
- Identity extension A=R: φ=id is both local and injective, and the stalk of Spec R at
  its closed point is canonically R, so it belongs to the test class.
- A field cannot accidentally count as a DVR: `IsDiscreteValuationRing` excludes it.
- An R-map with wrong stalk algebra action is excluded by the structural equality.
- A DVR mapping into the generic fibre alone is not mistakenly included: locality
  requires the base uniformizer to remain a nonunit.
- Non-quasi-compact N and smooth X remain allowed. Only the generic fibre of N has
  the explicitly stated finite type condition.
- Equal or mixed characteristic and arbitrary residue fields are allowed.
- All objects, test rings and fraction fields live in the common explicit universe u;
  there is no independent smaller test universe that could make a condition vacuous.
  No implicit variables or universe equalities are silently auto-bound.

Searches for an existing statement (all msearch calls use group Q122 and this item):

- LeanFinder: `Neron model mapping property equivalent to surjectivity of points over
  essentially smooth discrete valuation rings` returned eight general valuative-criterion,
  stalk-surjectivity and related results; none states the Néron mapping criterion.
- LeanSearch: `A smooth separated group scheme is a Neron lft model if and only if its
  points extend over every essentially smooth discrete valuation ring` returned eight
  smoothness/separatedness results; no exact theorem.
- Loogle: `"CommGrpObj"` returned the existing class and five related declarations.
  Its signature and docstring were read, so the existing group-object class is reused.
- msearch grep: `Neron|Néron|CommGrpObj|IsGroupScheme` returned the CommGrpObj class
  and the affine Hopf-algebra instance, no Néron criterion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `Neron|Néron|CommGrpObj|IsGroupScheme|lem-sfb-neron-dvr-point-criterion` found
  existing uses of CommGrpObj, no Néron model definition or statement. A later narrowed
  search for `Neron|Néron|neron_mappingProperty|dvr_points` found no declaration.
- The required upstream node-id grep found no occurrence of this item's id.
- Direct Mathlib source searches located and inspected full signatures/docstrings for
  all basic dependency declarations, Over.pullback, fromSpecStalk and the fraction-ring
  construction. No existing declaration states this equivalence.

Validation: the prescribed `scompile.py` compiled this file against the live server,
first as its sandbox module (9.8 s) and then as the library module (2.0 s), with no errors
or warnings. The file uses module mode, public statement imports, private proof imports,
explicit universes, `autoImplicit false`, and lines of at most 100 characters.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
