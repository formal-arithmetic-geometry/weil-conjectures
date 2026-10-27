## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPlaneHypersurfaceGeometricGenus` states
`AlgebraicGeometry.PlaneHypersurface.geometric_genus_of_smooth`. Its only postponed
proof is this named theorem, with the complete six-step DAG proof in its docstring.
There are no new Lean definitions, helper axioms, or dependency modules. One new
existing:true definition node records the already published hypersurface constructions.
The natural-language statement is unchanged.

The geometric object is exactly the existing `PlaneHypersurface.scheme d F hF`:
its definition is the zero scheme of the actual homogeneous section F of O(d),
with standard charts of Proj(k[A,B,C]/(F)), without taking a radical. The defining
closed immersion is the existing `ι`, and its structure morphism is the existing
`π`. All four definitions and their docstrings were read in
`Sheaf.AlgebraicGeometry.PlaneHypersurfaceCohomology`.

Hypotheses and conclusions, clause by clause:

- A field k is `{k : Type u} [Field k]`. The three variables A,B,C are indexed
  by `ULift.{u} (Fin 3)`, the same three-element coordinate type as in the
  recorded cohomology dependency. This lift accommodates all scheme universes.
- The positive integer degree is `(d : ℕ) (hd : 1 ≤ d)`; positivity makes this
  equivalent to the positive integer d in the node. The equation is
  `(F : MvPolynomial (ULift.{u} (Fin 3)) k)` with
  `(hF : F.IsHomogeneous d)` and `(hF0 : F ≠ 0)`.
- Z is the dependency's actual `scheme d F hF`, and the smoothness hypothesis
  is `(hsmooth : SmoothOfRelativeDimension 1 (π d F hF))`. This uses the
  recorded smooth-relative-dimension predicate, not formal smoothness alone.
- Every extension L/k is quantified by `∀ (L : Type u) [Field L] [Algebra k L]`.
  Both fields and all schemes use one arbitrary common universe, as in the
  recorded geometric-integrality and base-change conventions. A larger
  extension is represented by choosing a common larger ambient universe;
  there is no cardinality, algebraicity, separability, closure, or rational-point
  restriction.
- The coefficient image is exactly `MvPolynomial.map (algebraMap k L) F`;
  `hF.map (algebraMap k L)` is Mathlib's proof of its degree-d homogeneity.
- The base change is the actual categorical
  `pullback (π d F hF) (Spec.map (CommRingCat.ofHom (algebraMap k L)))`.
  The existential isomorphism `e` identifies it with the coefficient-image
  hypersurface `scheme d (MvPolynomial.map ... F) (hF.map ...)`. The displayed
  equation `e.hom ≫ π ... = pullback.snd ...` makes this an identification
  over Spec L, rather than merely an isomorphism of underlying spaces.
  `IsClosedImmersion (ι ...)` retains its specified closed plane hypersurface
  structure. The following clauses are stated on this explicit model of Z_L.
- The scalar-map conclusion is `Function.Bijective (scalarMap ...)`, for the
  actual ring homomorphism induced by `π` on global sections, as in the
  recorded cohomology lemma. A bijective unital ring map is a ring isomorphism;
  with the algebra structure induced by that same map it is an L-algebra
  isomorphism. No arbitrary isomorphism replaces the scalar map.
- `ConnectedSpace (scheme ...)` includes nonemptiness by its `toNonempty`
  field, so it renders both nonempty and connected, including exclusion of
  the empty scheme. There is no omitted nonemptiness hypothesis.
- `GeometricallyIntegral (π d F hF)` is the initial conjunct for Z/k.
  The extension conclusion additionally contains `GeometricallyIntegral (π ...)`
  over L. The class means integrality after every field base change.
- Every local ring of every extension model appears in the universal point
  binder `∀ x : scheme ..., IsDomain (...presheaf.stalk x) ∧
  IsIntegrallyClosed (...presheaf.stalk x)`. Both parts of “integrally closed
  domain” are explicit, and the local rings are the scheme's actual stalks.
- The smooth H-projective geometrically integral curve conclusion is rendered
  by `SmoothOfRelativeDimension 1 (π ...)`, `IsHProjective (π ...)`,
  `GeometricallyIntegral (π ...)`, and `IsSmoothProjectiveCurve (π ...)`.
  The last recorded class includes integrality, separated finite type,
  dimension exactly one, smoothness and projectivity. Properness and
  quasi-compactness follow in the proof from H-projectivity, so no extra
  assumptions were added to state this class.
- The genus is the dependency's `@Scheme.arithmeticGenus L _ (scheme ...) ⟨π ...⟩`.
  Its explicit Over argument fixes the structure morphism used for scalars.
  The two equalities assert its cardinal cast equals `Module.rank L
  (cohomology ... 1)`, and that rank equals the cardinal cast of
  `((d - 1) * (d - 2) / 2 : ℕ)`. Hence g equals dim H¹ equals the indicated
  natural number. Cardinal rank asserts finiteness as well; it does not use
  the zero junk value of finrank for an infinite-dimensional space.
- `cohomology ... 1` is the dependency's restriction of scalars of the recorded
  `RingedSpace.moduleCohomology` applied to the structure module. Thus the H¹
  really is the node's structure-sheaf module cohomology, not an unspecified
  invariant. Its comparison with the upstream cohomological arithmetic genus
  is an explicit conclusion, not an unproved definitional identification.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`:
  `Algebra` and `algebraMap` (field extensions).
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `C`,
  `aeval`, `algHom_ext`; `Mathlib.RingTheory.MvPolynomial.Homogeneous`:
  `MvPolynomial.IsHomogeneous.map` (exact coefficient image).
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `AlgebraicGeometry.Proj`
  and `projIsoSpec`, read with their full signatures; these underlie the
  imported hypersurface construction. `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `Proj.projectiveSpaceOverAffine`, `Proj.projectiveSpaceOverAffineToSpec`,
  and `ProjectiveSpace`, with the homogeneous-coordinate index convention.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`
  and `Smooth`; `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`
  and its geometrically-reduced/irreducible interpretation.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`
  and `IsProjective` (also read directly); the recorded
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `IsSmoothProjectiveCurve`, `IsIntegralCurve`, `IsVariety`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `Scheme.arithmeticGenus`; `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology` and `globalSectionsFunctor`.
- `Sheaf.AlgebraicGeometry.PlaneHypersurfaceCohomology`: `scheme`, `ι`, `π`,
  `scalarMap`, `cohomology`, `cohomology_of_nonzero_homogeneous`.
- Proof imports are the recorded relative-Proj base-change module
  (`GradedAlgebraData.PullbackData.relProjIsoPullback`, `isPullback`),
  `BaseChangeConventions` (`baseChange_iterated`),
  `SmoothConnectedGenericGeometryCore` (`Scheme.smooth_connected_generic_geometry_core`),
  `ProjectiveImpliesProper` (`hProjective_properness`), and Mathlib's `Etale`
  module (recorded permanence declarations). The structure-sequence proof
  dependency has no Lean record, so no speculative module is imported for it.

The added statement dependencies are `def-pc-smooth-projective-curve` and the
new `def-sfb-plane-hypersurface-scheme`. The latter records the existing plain
definitions ideal/scheme/ι/π/scalarMap/cohomology. The cohomology theorem remains
in proof_deps only; none of its theorem content is used to define this signature.
`def-pc-base-change` remains a proof dependency for iterated base change, but is
not added to stmt_deps: the signature uses Mathlib's categorical pullback.

Edge cases checked: d=1 and d=2 give zero in the natural-number formula, d=3
and d=4 give one and three; integer division is not division in the field.
All characteristics, including 2 and those dividing d, are allowed whenever
the actual smoothness hypothesis holds. A nonzero homogeneous polynomial of
positive degree cannot define the empty projective hypersurface; nonemptiness
is a conclusion of the scalar-map calculation. The zero polynomial and degree
zero are excluded exactly as in the node. Nonsmooth repeated equations are
excluded only by the stated smoothness hypothesis. A smooth anisotropic conic
needs no rational point; the scalar map and genus-zero conclusion still apply.
The identity extension is included. No assumptions that k or L be algebraically
closed or perfect occur. No statement dispute or source correction is needed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "A smooth positive degree plane hypersurface is
  geometrically integral and has genus (d-1)(d-2)/2"`: eight hits concerning
  Weierstrass models and unrelated norm/degree statements; none states this
  theorem for arbitrary plane equations.
- `msearch.py ... loogle '"genus"'`: OK, zero hits.
- `msearch.py ... grep 'plane.*[Gg]enus|[Gg]enus.*plane|hypersurface'
  AlgebraicGeometry`: OK, zero hits.
- `rg -n 'lem-sfb-smooth-plane-hypersurface-geometric-genus|PlaneHypersurface|
  plane.*[Gg]enus|[Gg]enus.*plane' lean/WeilConjectures lean/Sheaf`: no theorem
  for this node; the relevant existing construction and cohomology theorem
  are in `PlaneHypersurfaceCohomology`. Other matches cite Stacks 0BYD in
  proof plans. They do not assert the present smooth geometric conclusions.
- Direct source searches for genus, geometric integrality, homogeneous
  coefficient maps and field base change located the declarations above.
  The arithmetic-genus definition and module-cohomology definition differ
  in implementation, so the theorem explicitly states their dimension agreement.

Source read: `literature/stacks-project/curves.tex`, section-plane-curves
(Tag 0BYA), lemma-genus-plane-curve and its complete proof (Tag 0BYD).
The six inherited proof steps supply the smooth connected-to-normal-integral
argument for arbitrary extensions. All public statement imports and all
recorded available proof imports were compiled together in module mode.

Validation: scompile.py compiled both its sandbox probe and the delivery's
library module successfully, with no errors or unexpected warnings. The theorem
has precisely one `sorry` proof; there are no diagnostic commands left.

## New nodes

`def-sfb-plane-hypersurface-scheme` is an existing:true definition node for the
already published declarations `AlgebraicGeometry.PlaneHypersurface.ideal`,
`scheme`, `ι`, `π`, `scalarMap`, and `cohomology` in
`Sheaf.AlgebraicGeometry.PlaneHypersurfaceCohomology`. Its source is Stacks 0BYA
and 0BYD, with module cohomology as in 01DZ. It records the actual ideal sheaf,
closed hypersurface, closed immersion, coefficient structure morphism, pullback
of constants, and module cohomology with canonical restriction of scalars.
There is no copied module or second construction, and the theorem node's record
is untouched. The definition allows F=0 and d=0, as the existing declarations do:
zero F gives the whole plane, while a nonzero constant gives the empty scheme.
It asserts no nonemptiness or cohomology formula in those cases.

New-node searches: LeanSearch for “Define the projective plane hypersurface cut
out by a homogeneous polynomial, its closed immersion and scalar map on structure
sheaf cohomology” found eight general Proj/sheaf facts, no exact construction.
LeanFinder for “The scheme Proj(k[A,B,C]/(F)) with its scalar map and structure
sheaf cohomology” found general Proj declarations, not this package. Mathlib grep
`PlaneHypersurface|plane.*hypersurface|hypersurface.*plane` returned zero hits.
DAG searches found these declarations only on the cohomology theorem's record,
with no owning definition node. Project grep located all six existing real
definitions; upstream grep found no competing construction. The blueprint
search `plane hypersurface` returned zero matching blueprint nodes. The full
raw search outputs are recorded in the new node's mathlib_searches.

## Returned delivery repair

H2 from immutable head 87d82e2066bf is repaired. Added the requested existing:true
definition-node attachment, replaced the added statement dependency on
`lem-sfb-plane-hypersurface-cohomology` with this new definition node, and dropped
the unused added statement dependency `def-pc-base-change`. Both existing nodes
remain in proof_deps. Neither the cohomology theorem's node/record nor any
published Lean file is edited. The delivery's Lean module and signature are
byte-for-byte unchanged from the returned version. The current main item differs
from the returned sandbox only in lean and stmt_deps; the repaired node was
rebased by applying just these owned fields to the current main node.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
