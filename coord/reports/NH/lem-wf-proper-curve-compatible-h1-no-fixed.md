## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ProperCurveCompatibleH1NoFixed` states
`AlgebraicGeometry.properCurve_compatibleH1_fixed_eq_zero`. Its only theorem has proof
`sorry`; no new definitions or other postponed statements are introduced.

Clause-by-clause rendering:

- The finite field F_Q and a fixed algebraic closure are `D : FiniteFieldDatum.{u}`:
  `D.k₀` is a finite field of cardinality `D.q`, and `D.k` is its chosen algebraic closure.
  This uses the same datum as the recorded Frobenius definition, with arbitrary closure.
- `C₀ : Over (Spec (.of D.k₀))` is the curve over the finite field.
  `[SmoothOfRelativeDimension 1 C₀.hom]` renders smoothness and dimension one;
  `[IsProjective C₀.hom]` renders projectivity, and
  `[GeometricallyConnected C₀.hom]` renders geometric connectedness. Projectivity supplies
  properness, finite type and quasi-compactness; no additional finite-type assumption is made.
- The geometric curve C is exactly `(D.geometricFiber C₀).left`, the chosen fibre product
  of the model with `Spec D.k`. No arbitrary geometric curve or comparison map is assumed.
- `ℓ : ℕ` and `[Fact ℓ.Prime]` give the prime, and `hℓ : ¬ ℓ ∣ D.q` is precisely ℓ not dividing Q.
- The coefficient at n is `ULift.{u + 1} (ZMod (ℓ ^ n))`, viewed as an additive group in
  the constant étale sheaf. ULift only places the group in the site coefficient universe.
- `x : ↥(limit (curveH1CoefficientSystem (D.geometricFiber C₀).left ℓ))` is an element of
  the ordinary inverse limit. The existing diagram is made by `Functor.ofOpSequence`,
  with `Sheaf.H.map` of the constant-sheaf image of the actual `ZMod.castHom` reduction
  from level n+1 to level n. It does not use pro-étale or derived inverse-limit cohomology.
- `D.geometricFrobenius C₀` is exactly id × Spec(γ_Q), where γ_Q is the inverse of
  arithmetic z ↦ z^Q. It is used as a scheme automorphism, without requiring k-linearity.
- The expression inside `hfix` first applies `Etale.cohomologyMap` along this map, then
  `Sheaf.H.map` of the component of `Scheme.upperStarConstantSheafIso`. Thus it includes
  precisely the canonical identification of the pullback of the constant coefficient
  sheaf with that same sheaf. `∀ n` says every coordinate of x is Frobenius fixed.
- The conclusion `x = 0` for every such x says the fixed part of the inverse limit is zero.
  Coordinatewise fixedness expresses the displayed fixed-space condition, because limit
  projections distinguish elements and reduction is natural for the canonical pullback.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, with its actual construction from
  `galoisMap`; its projection and inverse declarations were read too.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`. These are the
  recorded finite-level cohomology definition. As explicitly permitted by its lean.note,
  the source curve modules and the landed dual-Tate comparison use the equivalent Ext
  model `CategoryTheory.Sheaf.H`. No additional cohomology definition is introduced.
- `Sheaf.AlgebraicGeometry.Curve.H1DualTateModule`:
  `AlgebraicGeometry.curveH1CoefficientSystem`. Added the already-landed owning node
  `lem-wf-curve-h1-dual-tate-module` to stmt_deps to cite this actual diagram, rather than
  copy it. Its full comparison signature and proof docstring were read.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsProjective`,
  read with `scompile.py --source`; it is the canonical projectivity definition, including
  its properness API. `SmoothOfRelativeDimension` is the Mathlib smooth curve condition.
- Proof imports include the recorded geometric-Jacobian module, the abelian Tate module
  and the additive-group Tate module. The already-stated dual-Tate module is a public
  import because its coefficient-system declaration is used in this signature. The
  recorded geometric-Frobenius module also serves the proof.
- `lem-wf-finite-field-tate-no-fixed` has no recorded module on the read base, so there is
  no corresponding proof-only import yet. It is named in the proof plan docstring.

Edge cases checked: level n=0 has ZMod 1 = 0 and does not change the inverse limit over
positive levels; all levels remain included. Genus zero is allowed and then H¹ is zero.
No positive-genus assumption is added. Geometric connectedness excludes the empty curve
as the source requires; dimension one excludes a point. The coefficient prime dividing Q
is explicitly excluded, including the characteristic prime. Every finite field of the
stated cardinality and every fixed algebraic closure is covered by D. The scheme, base
field and closure share the standard scheme universe u; coefficient groups lie in u+1,
matching the small étale cohomology interface. No extra site-universe equality is imposed.

Searches for an existing statement (msearch.py, all logged in searches.jsonl):

- LeanFinder: “Geometric Frobenius has no fixed compatible first etale cohomology classes
  on a smooth projective curve over a finite field”. Eight hits about arithmetic Frobenius,
  Hilbert 90 and isocrystals; no exact match.
- Loogle: `Etale.cohomology, frobenius`. No hits (unknown identifier Etale.cohomology in
  Mathlib); the source declaration is project-specific.
- Mathlib grep: `frobenius.*cohomology|cohomology.*frobenius|TateModule`, under
  AlgebraicGeometry. No hits.
- LeanSearch: “Frobenius invariant compatible first etale cohomology classes on a smooth
  projective curve over a finite field vanish”. Eight hits, including group cohomology,
  cotangent H1 vanishing and finite-field Frobenius; no étale inverse-limit statement.
- rg over WeilConjectures and lean/Sheaf for cohomology/Frobenius, compatible H1 and
  curveH1 found the existing coefficient diagram and canonical pullback APIs, reused here.
- grep of the item id in WeilConjectures found
  `Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso_of_isProper` in
  `AlgebraicGeometry/FundamentalGroup/Frobenius.lean:297`. Read its complete signature and
  docstring: it states a torsor triviality result using a geometric base point,
  a fundamental group, and monodromy compatibility; it does not state the cohomology
  inverse-limit result with the recorded arbitrary-closure Frobenius. It is not an exact
  existing attachment. The stage-1 review independently records the same distinction.
- rg for `properCurve_compatibleH1_fixed_eq_zero` in Mathlib, WeilConjectures, lean/Sheaf
  and dag/lean_names_upstream.json found no collision.

No statement correction, new node, unusable statement dependency or STATEMENT-DISPUTED
fault was found. Source checked: current main-20261015 statement and proof of the item,
as well as the DAG's expanded three-step proof (used in the theorem docstring).

## Second reading by NH

Author self-check for direct delivery; the maintainer supplies the independent review.
Reopened the node and the final file and compared the finite-field/closure datum, smooth
projective geometrically connected curve, prime and nondivisibility, actual geometric
base change, ordinary coefficient-reduction limit, inverse-arithmetic scheme Frobenius,
canonical constant-sheaf pullback comparison, and zero fixed-part conclusion. Each is
rendered as detailed above; there is no assumption of finite-level fixed-group vanishing,
no rationalization, and no Tate twist. The reused diagram has n=0 as a zero term, which
preserves all positive-level compatible systems. No mathematical mismatch was found.
The initial compile identified a nonexistent Mathlib projectivity module; its import was
corrected to the existing upstream WeilConjectures projectivity module. The actual theorem
has only `sorry` as proof and explicitly bound variables and universe.

Validation: `scompile.py NH lem-wf-proper-curve-compatible-h1-no-fixed` compiled this
single module cleanly in both sandbox and library contexts; the library invocation took
43.9 seconds with the default 60-second per-file limit. There were no errors or warnings.
The sandbox wrapper also waited for compilation capacity. Local text checks verified the
verbatim signature, 100-column line widths, the sole theorem proof `sorry`, and the exact
node delta (`lean` and addition of the existing coefficient-diagram owner to `stmt_deps`).
