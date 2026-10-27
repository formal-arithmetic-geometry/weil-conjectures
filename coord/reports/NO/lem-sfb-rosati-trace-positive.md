## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.RosatiTracePositive` states
`AlgebraicGeometry.IsAbelianVariety.exists_rosati_trace_positive`, with a single
`sorry` and the seven-step DAG proof in its docstring. No new definition, dependency
repair, or statement correction is needed. The only node changes are `lean` and
three added, already landed statement dependencies owning the constructions used:
`def-sfb-abelian-rational-hom`, `def-sfb-abelian-dual-poincare-datum`, and
`def-sfb-abelian-rational-tate-action`.

Source read: Milne, `literature/milne-abelian-varieties_AV.pdf`, printed pp.61–62
(PDF pp.67–68), section 14 and Theorem 14.3, including the formula for the Rosati
involution, trace positivity, and the application Tr(1)=2g in Proposition 14.4.
Also read the current `literature/blueprint/latest` direct-image preservation proof
(3), the ancestor route recorded in the node. This node is auxiliary, not a unit
statement. The existing DAG proof supplies the explicit nonzero effective-pullback
argument and separates dimension zero, as needed for the source's positivity proof.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| Abelian variety A/k, with group-scheme endomorphisms | `A : Over (Spec (.of k))`, `[GrpObj A] [IsAbelianVariety A]`; `abelianHom` bundles group-object homomorphisms, not arbitrary scheme maps |
| Dimension g=dim A | `IsAbelianVariety.dim A`; the upstream `topologicalKrullDim_eq` identifies this natural number with topological Krull dimension |
| E=End(A) tensor_Z Q | `abelianRationalHom A A = ℚ ⊗[ℤ] abelianHom A A`, canonically identified with the displayed factor order by tensor symmetry; its existing ℚ-module structure is used |
| Multiplication is composition | The existential bilinear `c B C F` is fixed on **all** pure tensors by `(r*s) ⊗ abelianHomComp f g`; it therefore is the unique scalar extension of integral composition. `c f g` means g after f, so conventional uv means `c v u`. No unconstrained multiplication is assumed |
| A-dual is Pic^0 with rigidification | The existential `D : AbelianDualPoincareDatum A` includes an abelian variety, normalized invertible Poincare family, geometric algebraic triviality, tensor group law, and the representing property for all parameter schemes and rigidifications |
| L ample and invertible | `(L : A.left.Modules) [L.IsInvertible] (hL : IsAmple A.hom L)`; upstream ampleness is the required positive-power very-ample condition on this proper scheme |
| lambda(x) is translated difference | `lambda : abelianHom A D.dual` and `ClassifiesAbelianDifference D L (abelianHomMap lambda)`. This uses the existing normalized translated-difference family, including the identity-line normalization. Its fibres give t_x^*L tensor L^{-1}; a constant line over the algebraically closed field does not change its line class |
| lambda has two-sided rational inverse mu | `mu : abelianRationalHom D.dual A` and the two `c A D.dual A lambda mu = id_A` and `c D.dual A D.dual mu lambda = id_dual` equations, with integral maps inserted by `abelianHomToRational` |
| Dual is pullback on invertible sheaves | `d : abelianHom A A →+ abelianHom D.dual D.dual`, pinned by the iff between the Poincare-pullback isomorphism and `g = d f` for every integral f and g. It is not an arbitrary additive map |
| Extend duality Q-linearly | `dQ : abelianRationalHom A A →ₗ[ℚ] abelianRationalHom D.dual D.dual`, with `dQ (r ⊗ f) = r ⊗ d f` for every r and f |
| u dagger = mu u-dual lambda | The equation for `dagger v` composes lambda, `dQ v`, then mu in categorical order |
| Dagger Q-linear, involutive and reverses multiplication | Its `→ₗ[ℚ]` type, `Function.Involutive dagger`, and `dagger (c v w) = c (dagger w) (dagger v)` |
| Rational linear trace | `tr : abelianRationalHom A A →ₗ[ℚ] ℚ` |
| Every prime ell distinct from char k | `∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ ringChar k → ...`; this includes characteristic zero and ell=2 whenever allowable |
| Trace embeds to actual Tate trace | `algebraMap ℚ ℚ_[ℓ] (tr v) = LinearMap.trace ℚ_[ℓ] (rationalTateModule ℓ A) (rationalHomTateMap ℓ v)`; the action is the landed componentwise Tate action extended on pure tensors, not an arbitrary realization |
| Tr(1)=2g | `tr (abelianHomToRational (abelianHomId A)) = (2 * IsAbelianVariety.dim A : ℕ)`, with the natural number coerced into ℚ |
| B_lambda(u,v)=Tr(u dagger v) | The equation `B v w = tr (c A A A w (dagger v))`; categorical order means exactly dagger(v) after w |
| Q-bilinear and symmetric | `B : E →ₗ[ℚ] E →ₗ[ℚ] ℚ` and `∀ v w, B v w = B w v` |
| Strict positivity for every nonzero rational endomorphism | `∀ v : abelianRationalHom A A, v ≠ 0 → 0 < B v v` in the ordered field ℚ |

All non-input objects are existentially supplied in the conclusion and fixed by
representing or pure-tensor identities. Thus there is no additional assumption of
a chosen dual, rational inverse, involution, trace or positive form. Their binder
order is only to make the dependent types readable. No proof assertion that the
node omits (e.g. an intersection formula) is added to the conclusion.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`, `IsAbelianVariety.dim`,
  `IsAbelianVariety.topologicalKrullDim_eq`.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`:
  `AlgebraicGeometry.IsAmple`; `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, `IsMonHom`;
  the specialization to schemes over Spec k is documented in the read upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`:
  `AlgebraicGeometry.IsAbelianVariety.tateModule`, `rationalTateModule` and
  `rationalTateModuleMap`; the audit-closed `sk-def-av-tate` has no `lean` record,
  and its audit declaration and module are used directly, as required.
- Mathlib leaves: `Field` (`Mathlib.Algebra.Field.Defs`), `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`, the applicable component of the closure
  node's match), `TensorProduct` (`Mathlib.LinearAlgebra.TensorProduct.Defs`),
  `LinearMap.trace` (`Mathlib.LinearAlgebra.Trace`), `topologicalKrullDim`
  (`Mathlib.Topology.KrullDimension`). Their full signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.AbelianVariety.RationalHom`:
  `abelianHom`, `abelianHomMap`, `abelianRationalHom`, `abelianHomToRational`,
  `abelianHomComp`, `abelianHomId` (namespace `AlgebraicGeometry`).
- `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`:
  `AlgebraicGeometry.AbelianDualPoincareDatum`, `abelianNormalizedDifference`,
  `ClassifiesAbelianDifference`, including the full universal property and normalizations.
- `Sheaf.AlgebraicGeometry.AbelianVariety.RationalHomTateAction`:
  `AlgebraicGeometry.IsAbelianVariety.rationalHomTateMap`, together with its
  precomposition/postcomposition and integral Tate-action definitions.

The public imports expose all statement objects through their owning modules.
Every stated proof dependency has its recorded module imported plainly, including
`PolarizationCalculus.exists_dual_polarization_calculus`,
`WeilPairing.exists_functorial_weilPairing`, `TateActionSaturation.tate_action_saturation`,
`RationalTateCharpoly.existsUnique_rational_tate_charpoly`,
`TraceIntersection.trace_adjoint_product_eq_intersection`, the integral Cartier
section theorem, ample degree positivity, the intersection-number definition,
rational-point density, the Cartier intersection theorem, and Snapper's polynomial
theorem. Their namespaces are those of the recorded declarations (principally
`AlgebraicGeometry` and `AlgebraicGeometry.IsAbelianVariety`). The proof-only node
`lem-sfb-simple-isogeny-decomposition` currently has no Lean record; no import is
invented for it. This is not a missing object needed to type this statement.

Edge cases checked before writing:

- Dimension zero: the trivial abelian variety has zero rational endomorphism space,
  identity=zero and trace=0=2g. Involutivity, both inverse identities and symmetry
  hold; strict positivity has no nonzero input. No positive-dimension binder,
  negative exponent or nontriviality hypothesis excludes it.
- Zero endomorphism: linearity gives trace zero and B(0,0)=0; positivity explicitly
  requires nonzero input.
- Multiplication by a rational scalar a: dagger fixes this scalar identity;
  the trace is 2ga and the diagonal trace form is 2ga², positive for nonzero a
  when g>0. This also checks composition order and normalization.
- No principal-polarization condition is imposed: mu is rational, so polarizations
  of arbitrary degree, including characteristic-divisible degree, are covered.
- Characteristic 2 and ell=2 are not silently excluded: the only prime condition
  is ell distinct from characteristic; characteristic zero admits every prime.
- Non-isogeny endomorphisms remain allowed in the positivity clause. In the DAG
  proof their nonzero pullbacks are obtained from a separating hyperplane, rather
  than by incorrectly requiring every effective divisor to have nonzero pullback.
- Universe u is explicitly bound and shared with k and its schemes. All binder
  variables and universes are explicit; both auto-implicit options are false.
  No universe equality on an independent site is introduced.

Searches actually run (logged in the sandbox's `searches.jsonl`):

- `msearch.py ... leanfinder "Rosati trace pairing of rational endomorphisms of a polarized abelian variety is positive definite"`:
  8 hits, root-system positive forms only; no abelian-variety Rosati theorem.
- `msearch.py ... loogle '"Rosati"'`: 0 hits.
- `msearch.py ... grep 'Rosati|rosati|abelian.variety'`: 0 hits in Mathlib.
- `msearch.py ... leansearch "Rosati involution rational trace form positive definite abelian variety"`:
  8 hits, including `Algebra.traceForm`, `Matrix.PosDef.trace_pos` and
  `LieModule.traceForm`; these do not state geometric Rosati positivity.
- `rg` over project `lean/WeilConjectures` and `lean/Sheaf` for
  `rosati|Rosati|RationalHom|rationalHom|dualAbelian|DualAbelian`, and the exact item
  id: found the reusable rational Hom/duality/Tate modules, the existing
  polarization-calculus theorem giving an involution without trace positivity,
  and a consumer discussing Rosati positivity; no declaration of this statement.
- `rg` for `rosati|Rosati` in `dag/lean_names_upstream.json`: no match.
  The exact-item-id search in `lean/WeilConjectures` also gave no match.

Validation: the prescribed `scompile.py NO lem-sfb-rosati-trace-positive` compiled
both sandbox and final module modes in 2.4 seconds each, without errors or warnings.
The signature in `lean.statement` is extracted verbatim from the delivered module.

## Second reading by NO

Author's second pass with the node, module and Milne pp.61–62 open; independent
review is supplied by the maintainer, as specified in the dispatch brief. Checked
all rows above again. In particular, `c f g` is g after f, the dagger formula is
mu after dual after lambda, and `B v w` composes w then dagger v. The two inverse
equations have the correct distinct identities. The normalized family pins lambda;
the Poincare pullback iff pins duality; rational extension and composition are
pinned on pure tensors. All-prime Tate compatibility is a conclusion, not an
assumption. The form is bundled bilinear, explicitly symmetric and strictly
positive exactly on nonzero inputs. `IsAbelianVariety.dim` agrees with the node's
topological dimension. No field-characteristic, dimension, polarization-degree or
endomorphism-invertibility restriction was added. No mismatch found, and no node
statement or dependency interface was changed.
