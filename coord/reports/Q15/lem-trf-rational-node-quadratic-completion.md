## Worker report

This repairs both points of return L at immutable head f49a0e946458. That returned
packet was a stage-1 split rather than a stage-2 statement delivery. The retained
sandbox had only launcher markers, so this packet starts from the current item
node and adds a real module and complete `lean` record. It does not reuse the
stage-1 report or the returned change to `proof[0].text`.

The module `Sheaf.AlgebraicGeometry.RationalNodeQuadraticCompletion` states
`AlgebraicGeometry.rational_node_quadratic_completion`. Its only theorem proof is
`sorry`. It introduces no definitions, axioms, helper theorems, or extra nodes.
The docstring gives all six proof steps, including their DAG citations and the
second application of the formal-presentation lemma responsible for the facts
about the completion of B.

H1 is repaired by the module, exact signature record, this Worker report, the
second-reading section below, and clean per-file compilation through scompile.py.
H2 is repaired by copying the current base node and changing only `lean`.
In particular `proof[0].text` retains Q82's C4 correction verbatim: the first
application supplies A, B and the completion of A; the Noetherianity, maximal ideal
and residue field of the completion of B are credited to the second application
in step 3. No statement, statement dependency, proof, or proof dependency changes.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node text | Lean rendering |
| --- | --- |
| F is a field | `{F : Type u} [Field F]` |
| X is a scheme over F | `{X : Scheme.{u}} (f : X ⟶ Spec (.of F))`; an explicit structure map is used because the statement base-changes this map. |
| Locally of finite type | `[LocallyOfFiniteType f]`; no quasi-compactness, separatedness, or finite-presentation hypothesis is added. |
| Topological Krull dimension one | `hdim : topologicalKrullDim X = (1 : WithBot ℕ∞)`; this is total dimension, not a purity assumption. |
| z is a closed point | `(z : X) (hz : z ∈ closedPoints X)` |
| The structural F to κ(z) is an isomorphism | `hrat : Function.Bijective (f.residueFieldAlgebraMap z)`; bijectivity of this ring homomorphism is precisely being a field isomorphism, rather than an abstract identification with another copy of F. |
| A chosen algebraic closure of F | `(Ω : Type u) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]`; any algebraic closure with its chosen F-embedding, not only Mathlib's chosen closure. |
| Base change X over that closure | `pullback f (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))` |
| The induced Ω-rational point above z | `zbar` in that pullback, with `hzbar : pullback.fst ... zbar = z`. Since κ(z) = F through the structural map, the fibre of this projection over z is Spec Ω. Thus there is exactly one such point, and it is the induced Ω-rational point. This presentation adds no choice of a different geometric lift and no further rationality assumption. The uniqueness is also recorded upstream in `Scheme.Hom.baseChangeFieldPoint_eq_of_fst_eq` in `WeilConjectures.AlgebraicGeometry.DensePoints`. |
| The geometric completed local ring is ring-isomorphic to Ω[[u,v]]/(uv) | `hgeom : Nonempty (AdicCompletion (IsLocalRing.maximalIdeal ...) ... ≃+* (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}))`. In particular this is `RingEquiv`, not an Ω-algebra equivalence. |
| There exist a,b,c in F | `∃ (a b c : F)` |
| Nonzero discriminant | `b ^ 2 - 4 * a * c ≠ 0`, with multiplication in F and no characteristic restriction. |
| An F-algebra isomorphism of the completion with the quadratic quotient | `Nonempty (@AlgEquiv F ... ...)` with source the maximal-ideal completion of `X.presheaf.stalk z` and target the quotient by the span of `C a * (X 0)^2 + C b * (X 0 * X 1) + C c * (X 1)^2`. |
| The original F-algebra structure | The explicit source algebra passed to `AlgEquiv` is `RingHom.toAlgebra` of the composite of `(Scheme.ΓSpecIso (.of F)).inv`, `f.appTop`, `X.presheaf.Γgerm z`, and the canonical map of the local ring into its completion. The target has the standard F-algebra structure on the power-series quotient. No arbitrary coefficient section is quantified over. |
| Maximal-ideal-adic completions | Both occurrences use `AdicCompletion (IsLocalRing.maximalIdeal R) R`. |
| Two-variable formal power series | Both occurrences use the dependency's `MvPowerSeries (Fin 2)` with the appropriate coefficient field. |

All eight recorded statement dependencies were read, including their full
statements and Lean records (or Mathlib match for the two leaves without a record).
Their declarations are used as follows:

| DAG dependency | Imported module and declaration |
| --- | --- |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType` |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`, `topologicalKrullDim` |
| def-weil-closed-points | `Mathlib.Topology.JacobsonSpace`, `closedPoints` (the recorded Mathlib match) |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`; the structural field homomorphism is the existing `Scheme.Hom.residueFieldAlgebraMap` in the additionally imported `WeilConjectures.ZetaSeries`. |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosure`, explicitly allowed by the recorded match for a chosen closure. |
| def-pc-base-change | `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; the recorded convention uses `Limits.pullback`, with `pullback.fst` the projection to X. The live source was read through `scompile.py --source` because the older local source checkout lacks this current module. `moduleBaseChange` is the node's module-sheaf clause and is not incorrectly used as a scheme base change. |
| def-weil-pbc-adic-completion | `Mathlib.RingTheory.AdicCompletion.Algebra` imports the recorded `Basic`; `AdicCompletion` with its commutative ring and canonical algebra structure. |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, `MvPowerSeries.C`, `MvPowerSeries.X`. |

The proof imports include the recorded Fitting presentation and formal Jacobian
modules, flat local depth formula, and Mathlib's differential localization/base
change and faithfully flat completion/ideal contraction APIs. The direct proof
prerequisite `lem-trf-separable-closed-point-formal-presentation` currently has
neither a Lean record nor a Mathlib match, so there is no module to import for it;
it remains explicitly named in the proof docstring. No import cycle is introduced.

Source check: read Stacks `curves.tex`, `lemma-nodal` (Tag 0C4D), including the
arbitrary-field descent paragraph, and `lemma-nodal-algebraic` (Tag 0C49),
condition (3), with the nondegeneracy definition immediately before it. In two
variables that determinant is `4ac - b²`, equivalent to the displayed nonzero
discriminant. The rational-residue-field case has the structural F-algebra
isomorphism in the conclusion and only the geometric ring isomorphism as input.
No source-based correction is necessary.

Edge cases checked before writing:

- `q = uv` over any field has `(a,b,c) = (0,1,0)` and discriminant one.
- In characteristic two, `q = u² + uv + v²` over F₂ has discriminant one;
  the statement keeps this case and never divides by two or assumes `a ≠ 0`.
- Over the reals, `u² + v²` is a nonsplit rational node with discriminant `-4`;
  the conclusion allows this and does not require an F-split `uv` equation.
- A cusp or double line has no geometric ring isomorphism to the `uv` model.
- The empty scheme cannot supply z (and has dimension minus infinity); a dimension
  zero scheme fails `hdim`. Neither exclusion is a hidden hypothesis.
- A locally finite-type scheme need not be quasi-compact or equidimensional; no
  such assumptions were inserted. Only its given total dimension is used.
- The geometric equivalence has no linearity condition, while the conclusion
  preserves the particular structural embedding of F, not an unrelated field
  isomorphism. All variables and the common ambient universe are explicitly bound.

Searches for an existing statement, all through msearch.py where applicable:

- LeanSearch: `A rational geometric node has completed local ring isomorphic as a
  ground field algebra to two variable power series modulo a nondegenerate binary
  quadratic form`. Eight hits: Weierstrass preparation/division and Laurent-series
  algebra equivalences, none giving the nodal descent statement.
- LeanFinder: `A rational geometric ordinary double point has completed local F
  algebra isomorphic to F power series in two variables modulo a binary quadratic
  form with nonzero discriminant`. Eight hits about one-variable Weierstrass
  preparation and elliptic-curve reduction; no match.
- Loogle: `"MvPowerSeries", "AdicCompletion"`. Ten hits including
  `MvPowerSeries.toAdicCompletionAlgEquiv`, which completes a polynomial ring
  rather than producing a nodal quotient or descending its equation; no match.
- msearch grep in Mathlib/RingTheory: `nodal|ordinary.double|quadratic.*completion`.
  Zero hits.
- Direct rg in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `rational_node_quadratic_completion|lem-trf-rational-node-quadratic-completion|geometric.*node|quadratic.*complet`.
  No declaration of this item. The nodal finite-separable-splitting module cites
  this item in its proof, and FormalJacobianQuadraticCriterion concerns formal
  presentations, not rational geometric descent. Neither duplicates this theorem.
- Additional direct rg for `topologicalKrullDim`, `closedPoints`, `AlgebraicClosure`,
  `MvPowerSeries`, `residueField`, and `AdicCompletion` located and confirmed the
  recorded dependency interfaces and sibling conventions.

There is no STATEMENT-DISPUTED flag, new definition node, or dependency repair.

## Second reading by Q15

The dispatcher explicitly requires this worker to deliver directly and prohibits
starting another agent; the maintainer's independent review is the independent
reading. This section records my separate second pass, without claiming a second
person or agent reviewed it.

With the node and final file open, I checked the field, structure morphism, locally
finite type instance, exact total dimension one, closed point, bijective STRUCTURAL
residue map, arbitrary chosen algebraic closure, base-change projection specifying
the induced point, geometric RingEquiv, all three ground-field coefficients,
nonzero discriminant, and ground-field AlgEquiv. Both completions are at the
maximal ideal; both power-series rings use exactly two variables. The explicit
source algebra is the structural global-sections/germ/completion composite. This
avoids accidentally accepting an isomorphism over a different residue subfield.

I also checked the characteristic-two and nonsplit real examples, and the reason
that the point-over-z presentation is precisely the induced rational point. The
full node's proof is byte-for-byte the current base proof, including the Q82 C4
sentence crediting the completed B facts to the second application in step 3.
The Lean docstring preserves that same attribution. No mathematical mismatch was
found on this second pass and no statement change was made.
