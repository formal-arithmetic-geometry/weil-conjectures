## Worker report

The module `Sheaf.AlgebraicGeometry.SeparableNodeQuadraticCompletion` states
`AlgebraicGeometry.separable_node_quadratic_completion`, with its sole proof `by sorry`.
There are no new definitions, additional nodes, dependency repairs, or statement corrections.
The item's JSON copy changes only `lean`. The declaration docstring carries all nine
steps of the node's proof, with the affine-open base-change identification included.

Source read: `literature/stacks-project/curves.tex`, lemma-nodal (Tag 0C4D), especially
its arbitrary-field descent argument, and lemma-nodal-algebraic (Tag 0C49), condition
(3) and the coefficient-field construction in the proof of (2) implies (3).
These are the specified source, and support the statement without correction.
No repair note for this item exists in `coord/repair-notes`.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Ground field k | `{k : Type u} [Field k]` |
| Scheme C over k, locally of finite type | `{C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]` |
| Equidimensional of dimension one | `hdim : C.IsPureDimension 1`; the recorded definition quantifies over every irreducible component with its subspace topology and uses `topologicalKrullDim` |
| Closed point x | `(x : C) (hx : x ∈ closedPoints C)` |
| Actual residue field kappa(x) | `C.residueField x`, definitionally the stalk modulo its maximal ideal |
| Finite residue extension | `hfinite : @FiniteDimensional k (C.residueField x) ... (f.residueFieldAlgebraMap x).toAlgebra.toModule` |
| Separable residue extension | `hsep : @Algebra.IsSeparable k (C.residueField x) ... (f.residueFieldAlgebraMap x).toAlgebra` |
| An algebraic closure K/k | `(K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]` |
| Point xbar of C base changed to K lying over x | `xbar : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, with `hxbar` identifying its first projection with x |
| Geometric completed local ring isomorphic as a ring to K[[u,v]]/(uv) | `hgeom : Nonempty (AdicCompletion ... ≃+* (MvPowerSeries (Fin 2) K ⧸ Ideal.span {X 0 * X 1}))`; the completion uses the maximal ideal of the actual base-changed stalk, and this is a ring equivalence without a K-linearity assumption |
| A is the local ring at x, and m its maximal ideal | Every occurrence uses `C.presheaf.stalk x` and `IsLocalRing.maximalIdeal (C.presheaf.stalk x)` directly |
| A is reduced | `IsReduced (C.presheaf.stalk x)` |
| A is Noetherian | `IsNoetherianRing (C.presheaf.stalk x)` |
| A is essentially of finite type over k | `.EssFiniteType` on `((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.Γgerm x).hom`, the canonical structural map from k to the stalk |
| A has Krull dimension one | `ringKrullDim (C.presheaf.stalk x) = (1 : WithBot ℕ∞)` |
| Completion Ahat = inverse limit A/m^n | `AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x)` throughout; its algebra map is the canonical map from A |
| Existence of a k-algebra section from kappa to Ahat | `∃ σ : C.residueField x →+* AdicCompletion ...`, with the first equation fixing the image of every `t : k` through the structural maps |
| Section of the actual residue map | `∀ t : C.residueField x, AdicCompletion.evalOneₐ ... (σ t) = t`; this projection is to A/m, definitionally `C.residueField x` |
| a,b,c belong to kappa, with nonzero discriminant | `∃ a b c : C.residueField x, b ^ 2 - 4 * a * c ≠ 0 ∧ ...` |
| Kappa-algebra isomorphism to the specified quadratic quotient | `∃ e : @AlgEquiv (C.residueField x) (AdicCompletion ...) (MvPowerSeries (Fin 2) (C.residueField x) ⧸ Ideal.span {C a * X 0 ^ 2 + C b * (X 0 * X 1) + C c * X 1 ^ 2}) ... σ.toAlgebra inferInstance, ...` |
| Continuous for the stated adic and quotient topologies | Explicit `@Continuous` with source the adic topology of m extended to Ahat and target `TopologicalSpace.coinduced (Ideal.Quotient.mk _)` of the variable-ideal-adic topology on kappa[[X,Y]] |
| Variable ideal powers form neighbourhoods of zero | `(Ideal.span (Set.range (fun i : Fin 2 ↦ MvPowerSeries.X i))).adicTopology`; `Ideal.adicTopology` is precisely the topology whose neighbourhood basis at zero consists of ideal powers |
| Induced residue-field map is the identity | For every power series h, `AdicCompletion.evalOneₐ ... (e.invFun (Ideal.Quotient.mk _ h)) = MvPowerSeries.constantCoeff h`; constant coefficient is the residue map on the quadratic quotient |

The section is a genuine ring homomorphism; ground-field compatibility makes it exactly a
k-algebra map, rather than an arbitrary field embedding. The explicit `σ.toAlgebra` in
the equivalence binds its coefficient action to that very section. The residue identity
is expressed on all representatives, avoiding an extra choice of quotient-to-residue map.
The equation has zero constant term, so constant coefficient descends to the quotient.
The extended-maximal-ideal topology on the completion is the usual completed local topology
since A is Noetherian; the target topology is precisely the quotient topology stipulated
by the power-series construction. A ring isomorphism between these local rings preserves
the maximal ideal and all powers, so its inverse is continuous too.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (finite-type morphism node).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, through
  `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`;
  `WeilConjectures.ZetaSeries`: `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`
  supplies its canonical ground-field action.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`;
  finite degree is expressed by the existing `FiniteDimensional` notion.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`; no particular construction
  of the algebraic closure is fixed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.fst`, with scheme pullbacks from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.EssentialFiniteness`: `RingHom.EssFiniteType`, which uses
  `Algebra.EssFiniteType` for the ring homomorphism's `toAlgebra` structure.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, its ring
  and algebra structures, canonical `algebraMap`, and `AdicCompletion.evalOneₐ`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`, `constantCoeff`.
- `Mathlib.Algebra.Algebra.Hom`, `.Equiv`, and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `AlgHom`/`AlgEquiv`,
  `Ideal.Quotient.mk`, and the canonical quotient algebra structure. The section's
  k-algebra property is written as its ring-homomorphism compatibility equation.
- `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`: `Ideal.adicTopology`, with
  the quotient topology given by the existing `TopologicalSpace.coinduced`.

The stated proof dependencies are imported privately, including the finite-type affine
criterion, affine-open stalk localization, open and affine fibre products, geometric-field
stalk descent, separable-closed-point formal presentation, both dimension comparisons,
Kahler localization and base change, presentation Fitting ideals, formal Jacobian criterion,
completion faithful flatness and ideal contraction, depth and its flat local formula,
and power-series field regularity. Public imports expose the statement's constructions.
No recorded dependency required repair or a private replacement.

Edge cases checked before writing and again against the source:

- Characteristic two is included: the discriminant condition becomes b nonzero, without
  dividing by two or demanding characteristic different from two. The split model has
  a=c=0, b=1 and discriminant one in every characteristic.
- Nonsplit quadratic nodes, such as the real model X^2+Y^2, are allowed. Coefficients
  live in the original residue field, not in its algebraic closure, and no splitting
  or rational-branch assumption is added.
- Nonrational closed points with finite separable residue field are included. No
  bijectivity of k to kappa, or identification k=kappa, is assumed. The case kappa=k
  specializes to the rational-node situation.
- Imperfect ground fields are allowed. Only the given residue extension is assumed
  separable, and `IsAlgClosure` allows the full algebraic closure.
- Empty C has pure dimension one vacuously, but has no x, so this statement has no
  invalid empty-scheme case. No global quasi-compactness or finite-type assumption
  beyond local finite type is imposed.
- The zero local ring cannot occur at a scheme point. Smooth points, cusps, and
  degenerate quadratics do not satisfy the given geometric-node condition or the
  nonzero-discriminant conclusion.
- The geometric isomorphism is an abstract ring isomorphism, as stipulated. It is
  not silently strengthened to a K-algebra isomorphism.
- All variables and the universe u are explicitly bound, with `autoImplicit false`.
  No local notation or local algebra instance is needed to read the signature.

Searches actually run (2026-10-22):

- `msearch.py ... leansearch "completed local ring at a geometric node is a nondegenerate binary quadratic power series quotient over a finite separable residue field"`:
  eight hits on residue fields, a one-variable power-series residue field, and separability
  of residue quotients; no theorem matching this node.
- `msearch.py ... leanfinder "Completed local ring of a curve at a finite separable closed geometric node is a nondegenerate binary quadratic power series quotient"`:
  eight hits on Weierstrass division/preparation and elliptic-curve good reduction;
  no geometric-node classification.
- `msearch.py ... loogle "AdicCompletion, MvPowerSeries, Algebra.EssFiniteType"`:
  successful query, zero hits.
- `msearch.py ... grep "nodal|quadratic.*completion|completion.*quadratic" RingTheory`:
  successful query, zero hits in Mathlib RingTheory.
- `rg` of nodal/quadratic/completion names in the project's `lean/Sheaf` and
  `lean/WeilConjectures`: located `RationalNodeQuadraticCompletion.lean`,
  `FormalJacobianQuadraticCriterion.lean`, `NodalPointLocalCriterion.lean`, and the
  coefficient-section/formal-presentation modules. Their full signatures were read.
  The rational completion theorem assumes a rational point, and does not state this
  node's extra local-ring, section, topology, and residue assertions. The formal Jacobian
  criterion concerns a chosen formal presentation. The nodal criterion gives the Fitting
  characterization. None already states this theorem.
- `rg` for the exact item id in `lean/WeilConjectures`, and for
  `separable_node_quadratic_completion` in both Lean trees and
  `dag/lean_names_upstream.json`: no existing declaration or attachment.

Validation: `scompile.py O2 lem-sfb-separable-node-quadratic-completion` compiled the
module successfully in both sandbox and library modes. The first compilation exposed
an elaboration issue with `e.symm` trying to infer the deliberately explicit coefficient
algebra; using the equivalence's `invFun` field expresses the identical inverse map and
compiled cleanly. No mathematical hypothesis, conclusion, or dependency was changed.
There is one postponed theorem and no postponed definition or auxiliary assertion.

## Second reading by O2

This is the author's final self-check; independent mathematical review belongs to the
maintainer under the dispatcher's direct-delivery brief. I reopened the node statement
and the final Lean signature and checked every row of the correspondence above.

The ground-field map used for finite/separable residue data is the recorded canonical
`f.residueFieldAlgebraMap x`, and the essential-finite-type assertion uses the structural
global-sections-to-stalk map. The section commutes with those ground-field maps and
splits `evalOneₐ`, rather than a freely chosen residue comparison. The algebra equivalence
uses exactly this section. The geometric completion is the stalk at the supplied xbar
in the literal scheme pullback, and its hypothesis uses a ring equivalence only.

The conclusion has all four local-ring assertions, the three coefficients and discriminant,
the algebra isomorphism, its specified topology, and its residue identity on every power
series representative. Pure dimension is the dependency's irreducible-component definition,
not merely a global-dimension equality. Continuity does not use a product topology with
unspecified coefficient topology: it explicitly uses powers of the variable ideal and
then the quotient topology. No mismatch was found on this reading. The only code adjustment
was the elaboration repair to the inverse-field projection described above.
