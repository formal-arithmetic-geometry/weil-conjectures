## Worker report

Item: lem-trf-nodal-polynomial-free-flat. The module
`Sheaf.TraceFormula.NodalPolynomialFreeFlat` states the affine and global clauses
as two theorems with `sorry` proofs. It constructs no new mathematical objects.
The node's mathematical statement and proof are unchanged. Its `stmt_deps` gains
two already landed definition nodes, def-trf-strict-semistable-curve and
def-trf-universal-nodal-model, to cite the actual constructions used.

Clause-by-clause correspondence:

- “Let A be a commutative ring” is `(A : CommRingCat.{u})`. This includes the
  zero ring, and u is arbitrary. “Let a in A” is `(a : A)` without conditions.
- “B=A[u,v]/(uv-a)” is the existing `strictNodalRing A a`, defined as the
  quotient of `MvPolynomial (Fin 2) A` by the ideal spanned by
  `MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a`.
  `StrictSemistableModel.nodal a` chooses precisely this model.
- “Spec B → Spec A” is
  `StrictSemistableModel.baseMap (StrictSemistableModel.nodal a)`.
  Reading its match branch shows that it is `Spec.map` of the composite
  `MvPolynomial.C` followed by `Ideal.Quotient.mk`, so its base structure
  is the coefficient map, not an arbitrary morphism.
- The affine conclusion “flat and locally of finite presentation” is the
  conjunction `Flat (...) ∧ LocallyOfFinitePresentation (...)` in
  `nodalPolynomial_flat_locallyOfFinitePresentation`.
- “For any scheme V” is `(V : Scheme.{u})`, and “h in Γ(V,O_V)” is
  `(h : Γ(V, ⊤))`, without an affineness or separation assumption on V.
- The glued scheme W is the canonical
  `pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)`.
  The existing universal nodal model has coefficient ring
  `(ULift ℤ)[a]` and equation uv-a. The existing `nodalBaseMap h` evaluates
  a at h and integer coefficients by casting, after the map to the spectrum
  of global sections. On each affine open Spec A of V its base change is
  Spec(A[u,v]/(uv-h|Spec A)); on smaller opens the transition maps restrict
  coefficients and fix u,v. This is the canonical gluing described in the
  node, expressed by the existing universal base change, with no choice of
  arbitrary maps or gluing datum.
- “projection W → V” is the second projection
  `pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)`.
- Its conclusion is again the conjunction of `Flat` and
  `LocallyOfFinitePresentation`, in
  `nodalModelProjection_flat_locallyOfFinitePresentation`.
- No Noetherian, reducedness, domain, nontriviality, nonzerodivisor, or
  nonempty-scheme assumption is present. Both declarations bind u explicitly
  and both auto-implicit options are false.

Dependency declarations read and used:

- def-weil-pbc-mv-polynomial-ring:
  `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`; evaluation and its
  uniqueness are `MvPolynomial.aeval` in `.Eval` and
  `MvPolynomial.algHom_ext` in `.Basic`. The existing model uses this ring.
- def-weil-affine-spectrum and def-pc-scheme:
  `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`, `Scheme`,
  `Scheme.Hom`.
- def-weil-flat-morphism:
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat` and
  `Flat.iff_flat_stalkMap`; the affine-local class agrees with stalk flatness.
- def-sbc-locally-finite-presentation:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `LocallyOfFinitePresentation` (affine-local finite-presentation condition).
- def-weil-pbc-algebra-hom-quotient: its Mathlib match is usable without a
  lean record. `AlgHom` is in `Mathlib.Algebra.Algebra.Hom`;
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ` are in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`.
- def-trf-strict-semistable-curve:
  `Sheaf.TraceFormula.StrictSemistableCurve`, `strictNodalRing`,
  `StrictSemistableModel.nodal`, `.scheme`, `.baseMap`. Read full definitions;
  no assumption of semistability is required to form their nodal branch.
- def-trf-universal-nodal-model:
  `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel`,
  `nodalInteger`, `nodalBaseRing`, `nodalPolynomialRing`, `nodalRelation`,
  `nodalModelRing`, `nodalBase`, `nodalModel`, `nodalModelBaseMap`,
  `nodalIntegerMap`, `nodalPolynomialMap`, `nodalBaseMap`. Their data is the
  explicit universal model and evaluation described above. The local-model
  existence theorem from that module is not a hypothesis of either statement.
- Proof dependency lem-sfb-binomial-laurent-normal-form:
  `Sheaf.RingTheory.BinomialLaurentNormalForm`,
  `strictNodalRing_basis_exists`. Its signature supplies a basis indexed by
  integers over every commutative ring, without the domain assumptions of
  the separate Laurent embedding theorem.
- Proof dependency lem-weil-pbc-projective-module-flat:
  `Mathlib.RingTheory.Flat.Basic`, `Module.Flat.of_projective` and `.of_free`.
- Proof dependency def-weil-pbc-flat-ring-map:
  `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat` and
  `RingHom.flat_algebraMap_iff`.
- Proof dependency lem-weil-pbc-flat-ring-map-iff-flat-affine:
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat.SpecMap_iff`.
  Proof imports are plain imports; statement constructions are public imports.

Edge cases checked mathematically before writing:

- A=0: the quotient is 0 and both spectra are empty. The assertions hold;
  there is no `Nontrivial A` binder.
- a=0 over a field: the crossing is singular but its ring has basis
  1,u^i,v^j, so it is flat. No use of smooth-implies-flat is made.
- A=Z/4, a=2: a is a nonzero zero divisor; monomial reduction remains valid
  and finite presentation still has exactly two generators and one relation.
- a a unit: the same quotient is the Laurent model and satisfies both claims.
- V empty, h=0, or V nonreduced or nonseparated: the canonical base change
  exists in each case; the chart argument is local and requires none of the
  excluded assumptions. Intersections of affine opens need not be affine.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`, query: “The morphism Spec(A[x,y]/(xy-a)) to
  Spec A is flat and locally of finite presentation and the same holds after
  gluing over a scheme”. Eight hits: AffineSpace local finite presentation,
  Flat, UniversallyOpen.of_flat, flat_iff and general flatness APIs; none is
  this singular binomial model theorem.
- `msearch.py ... loogle`, query: `"Flat", "MvPolynomial"`: zero hits.
- `msearch.py ... grep`, query: `(nodal|strictNodal|binomial)`, subdirectory
  AlgebraicGeometry: zero Mathlib hits.
- `msearch.py ... leansearch`, query: “The morphism Spec(A[u,v]/(uv-a)) to
  Spec A is flat and finitely presented for arbitrary commutative rings”:
  eight hits, general Flat and faithfully-flat criteria, plus smooth implies
  local finite presentation; no exact theorem.
- `rg` in the project's `lean/Sheaf` and `lean/WeilConjectures` for
  strictNodalRing, nodal model, and binomial names found the existing ring,
  standard projection, normal-form basis and universal model reused here.
  The scan pairing flat/presentation with those model names found no such
  theorem. Searching the item id in `lean/WeilConjectures` had no hits;
  in `lean/Sheaf` it occurs only as a future proof input in
  NodalChartBoundaryShrinking. Exact proposed declaration-name searches of
  both trees and `dag/lean_names_upstream.json` had no hits.

Source checks: read curves.tex, universal model immediately preceding Tag
0CBY, and the current blueprint's sk-i-curve-zero unit and
lem-trf-local-term-locality statement/proof. As the accepted split records,
this item is a historical auxiliary nodal-model input; the latest unit now
uses contracting correspondences. No unit or item statement is corrected.
The two theorem docstrings carry the accepted proof's steps 1--4, including
all named proof inputs. No statement dispute or node fault was found.

Validation: prescribed scompile.py compiled this module in both sandbox and
library modes against the live published build, exit 0, with no errors or
warnings (7.1 s and 6.0 s respectively). No local/global build was run.

## Second reading by Q17

The dispatcher explicitly prohibits starting other agents. This is a separate
self-check of the completed module against the node, not a claim of independent
review; the maintainer's independent reader receives this delivery.

Reopened the node and module and checked every binder and conclusion: A is an
arbitrary bundled commutative ring, a is unrestricted, and the selected nodal
model's baseMap is exactly the quotient coefficient projection. The first
conjunction gives precisely flatness and local finite presentation. V and h
are unrestricted, and the second conjunction uses the second projection of
the universal model base change, which is the gluing specified in the node.
The global base map is evaluation at h, including the integer coefficient map,
not an arbitrary map. No assumption about fibres, smoothness, a being nonzero,
or affineness of V has slipped in. The arbitrary universe includes the empty
scheme and zero ring. Added the two landed owning definition nodes to
stmt_deps; no new definition or dependency replacement was needed. Direct
public imports of the polynomial, scheme and quotient dependency modules were
added before the clean compile. Both postponed proofs are named and have
complete natural-language proof docstrings matching the accepted split.
