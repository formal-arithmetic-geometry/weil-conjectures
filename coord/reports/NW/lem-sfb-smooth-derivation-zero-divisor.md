## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothDerivationZeroDivisor` states the complete node in
four named theorems. All four proofs are `sorry`. Four helper definitions have real data:
`smoothCurveTangentSection`, `smoothCurveSectionGenericGerm`,
`smoothCurveLocalCoefficientOrder`, and `smoothCurveTangentZeroDivisor`. They package the
canonical constructions already supplied by the recorded dependencies. No existing source,
node statement, dependency list, or library file was changed.

Hypotheses and clauses, checked against the node:

- The arbitrary algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  The scheme and its structure map are `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`.
  `[IsConnectedCurve f]` includes finite type, separatedness, nonemptiness, connectedness,
  and dimension exactly one. `[Smooth f] [IsProper f]` supply smoothness and properness.
  The explicit structure map is needed by the recorded genus, Picard degree, and rational
  section declarations; it does not add mathematical data beyond being a k-scheme.
- The node's Omega is exactly `f.relativeDifferentials`, with
  `f.relativeDifferentialsDerivation`. Its tangent module T is
  `Scheme.Modules.dual f.relativeDifferentials`, definitionally the existing
  `SheafOfModules.homObj` into the structure sheaf `Scheme.Modules.unit X`.
- `smooth_curve_tangent_invertible` states `T.IsInvertible`, in the scheme-module sense
  required by the brief. It is registered as a global instance so that the real
  rational-section-divisor construction can consume this proof. The postponed theorem
  determines only a proposition, never chosen module data.
- The first clause of `smooth_curve_tangent_dictionary` states
  `f.picDegree [T] = 2 - 2 * (f.genus : ℤ)`. The explicit existing
  `Scheme.Modules.IsInvertible.sheafOfModules_isInvertible` conversion supplies the proof
  needed by `Scheme.Pic.mk`; it constructs no new invertibility notion. The recorded genus
  definition uses H0(Omega), whose source docstring identifies it, on these smooth proper
  connected curves, with H1(O) by `Scheme.genus_eq_arithmeticGenus`. Thus `f.genus` is the
  node's g, not a new genus convention.
- The rest of that theorem supplies an equivalence e from `Γ(T, ⊤)` to the existing type
  `(Scheme.Modules.unit X).val.Derivation' f.pullbackPresheafToPresheaf`. This type consists
  of additive maps on every open, with Leibniz, restriction compatibility, and vanishing
  on base sections. Over Spec(k) it is precisely sheaf k-derivations. The equality
  `e (smoothCurveTangentSection f θ) = f.relativeDifferentialsHomEquiv ... θ`
  pins it to the universal derivation, hence to D = theta composed with d. Internal-Hom
  `homObjSectionsEquiv` and evaluation at top define the canonical section itself.
  The final equality of additive maps on every open expresses additivity, even though
  Mathlib does not install an additive-group instance on presheaf `Derivation'`.
  Its equivalent orientation H0(T) -> Der is the inverse of the node's displayed map.
- `smooth_curve_derivation_fixes_iff` first says that the structural map k -> kappa(q)
  is bijective, with its actual formula through ΓSpecIso, f.appTop, germ, and residue.
  For every closed q and every theta, membership in
  `curveVectorFieldsFixingPoints f {q.val}` is equivalent to the tangent-section germ
  belonging to `maximalIdeal • ⊤` in its stalk module. This is exactly vanishing in the
  fibre T_q / m_q T_q, not vanishing of the entire stalk germ. Membership uses the
  dependency's point-ideal preservation predicate, including its all-neighbourhood tests.
- `smooth_derivation_zero_divisor` uses a nonzero theta (`hθ : θ ≠ 0`) in the dependency's
  representation of derivations by Hom(Omega,O). The existing universal equivalence sends
  zero to the zero sheaf derivation, so this is precisely D != 0. It asserts that the actual
  generic germ of its canonical section is nonzero, through the existential proof `hη`.
  No integral hypothesis was added: `smoothCurveSectionGenericGerm` uses the integral
  structure furnished by `smooth_connected_curve_local_rings`, exactly as the recorded
  `rationalSection` does.
- `smoothCurveTangentZeroDivisor ... hη` is definitionally
  `Scheme.Modules.rationalSectionDivisor` of that germ. Its first two properties are
  nonnegative coefficients at every closed point and finite nonzero coefficient support.
  Its underlying `X.Divisor` is the recorded finitely supported integer sum of closed points.
- `Nonempty (T ≅ Scheme.Divisor.moduleOfSmoothConnectedCurve ... Z)` states the required
  isomorphism T ≅ O_X(Z), using the recorded explicit divisor module, with the correct sign.
- The two degree equalities state degree Z = sum of all its coefficients = 2-2g over ℤ.
  Rationality of every closed residue field justifies the unweighted sum from `Divisor.degree`.
- For EVERY singleton local basis b of T_q, the theorem supplies a nonzero local coefficient
  a expressing the section germ as `a • b PUnit.unit`, and identifies Z(q) with
  `smoothCurveLocalCoefficientOrder ... a`. This helper is the existing `X.ord` of the
  image of a in X.functionField. At these codimension-one regular points it is exactly the
  normalized DVR valuation. Quantification over every basis gives the stated independence.
- The last clauses say Z(q)>0 iff theta fixes q; each such coefficient is at least one;
  and any finite set of distinct fixed closed points has cardinality at most 2-2g.
  Finset of `closedPoints X` counts distinct points without repetitions.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`,
  `Scheme.Hom.genus`, `Scheme.Hom.picDegree`, `Scheme.Hom.picZero`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`,
  `relativeDifferentialsHomEquiv`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`; `WeilConjectures.AlgebraicGeometry.Modules.Dual`:
  `Scheme.Modules.dual`, the existing `homObj` abbreviation and dual-invertibility API.
- `Sheaf.AlgebraicGeometry.DivisorModule`:
  `Scheme.Divisor.moduleOfSmoothConnectedCurve`; its existing upstream divisor declarations
  `Scheme.Divisor`, `Scheme.Divisor.degree` in `WeilConjectures.AlgebraicGeometry.Curve.Divisor`.
- `Sheaf.AlgebraicGeometry.RationalSectionDivisor`: `Scheme.Modules.rationalSection`,
  `rationalSectionOrder`, `rationalSectionDivisor`. The generic-stalk definition and the
  local generator/valuation formula were read in full.
- `Sheaf.AlgebraicGeometry.CurveVectorFieldsFixingPoints`: `curveVectorFieldApply`,
  `curveVectorFieldEvaluation`, `curveVectorFieldsFixingPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Hom.residueFieldMap`; `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.Algebra.Field.Defs`: `Field`.
- Existing internal Hom from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObjSectionsEquiv`, consumed through the public dual import.
- Proof imports include the recorded uniformizer basis, canonical degree and rational-section
  line-bundle statements, diagonal-conormal comparison, and Kähler localization. The
  recorded local-ring and rational-order modules are already public transitive imports.
  `lem-sfb-relative-differentials-sheaf-universal-property` and
  `lem-trf-affine-chart-stalk-differentials` have no recorded modules to import; their
  mathematical steps remain explicitly named in the proof docstrings. The universal map
  itself is already constructed by the recorded differential-sheaf dependency.

Edge cases checked before drafting: no characteristic restriction, including characteristic
2 and positive-characteristic derivations; genus zero gives total order 2; genus one gives
an empty zero divisor for a nonzero derivation; genus at least two forces absence of nonzero
derivations. The zero derivation belongs to the canonical dictionary and satisfies the fibre
criterion, while the divisor clauses correctly exclude it. Empty and dimension-zero schemes
are excluded by the node's connected-curve definition itself. Empty finite sets of fixed
points are allowed. Fibre zero is weaker than stalk zero, as required. Universes and all
variables are bound explicitly (`set_option autoImplicit false`).

Searches made (2026-10-24):

- `msearch.py ... leansearch "The zero divisor of a nonzero vector field on a smooth proper
  algebraic curve has degree 2-2g"`: eight hits, including analytic `MeromorphicOn.divisor`
  and manifold `VectorField.mpullback_zero`; none states the algebraic-curve result.
- `msearch.py ... leanfinder "On a smooth proper algebraic curve derivations are tangent
  sections with effective zero divisor of degree 2 minus twice the genus"`: eight hits,
  including Weierstrass affine function fields and the different ideal; no exact match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme, Derivation"`: zero hits.
- `msearch.py ... grep "derivation|vector.?field|tangent" AlgebraicGeometry`: nine Mathlib
  hits (elliptic tangent formulae and formally unramified cotangent arguments), no match.
- `rg -n` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, proposed theorem names,
  tangent/divisor/section and derivation/divisor/degree combinations: no existing statement.
  Existing `Modules.dual`, internal Hom and universal derivation were reused, not redeclared.

Source read: local `literature/stacks-project/curves.tex`, section Vector fields, the definition
of fixes preceding `lemma-smooth-vector-fields`, its full proof (Tag 0E67), and
`lemma-uniformizer-works` (Tag 0C1E). The node's six proof steps are retained in the four theorem
docstrings. No mathematical dispute or node correction was needed.

Validation: `scompile.py` compiled both the sandbox and the final library module cleanly
(2.6 and 2.7 seconds respectively), with no errors or warnings. The first
`deliver2.py ... --no-push` passed server preflight and compilation, producing dry-run
commit `41d72908f29`. The exact recorded main signature was checked against the module;
all lines are at most 100 characters and the four theorem bodies are solely `sorry`.

## Second reading by NW

This is the author's second reading under the dispatcher brief (which prohibits starting
other agents); the maintainer supplies the independent review. I reopened the node, the
helper definitions, and each theorem signature. Invertibility uses the scheme-module class;
Picard degree requires an explicit conversion to the existing sheaf-module class, which was
added after the first compile diagnosed the missing instance. The local multiplicity clause
quantifies over every basis, not a chosen or unspecified one. The zero divisor is the actual
recorded rational-section divisor of the actual generic germ. The section/derivation
identification is characterized by the existing universal derivation, with additivity on
every open. The fixed-point equivalence applies to all theta, including zero. Neither
integrality, a characteristic bound, a trivialization nor a nonzero section was added as an
independent geometric hypothesis. The nonzero-germ proof and the invertibility proof are the
only inputs to divisor construction, and both are explicitly asserted by this node. Every
hypothesis and clause is matched above; no other mismatch was found.
