## Worker report

Item: `lem-trf-valuation-reduced-fibre-normalization`, Q30, stage 2.
Module: `Sheaf.TraceFormula.ValuationReducedFibreNormalization`.
Declaration: `WeilConjectures.valuation_reduced_fibre_normalization`.
The only new declaration is the item's theorem, with proof `by sorry`.
No new definition, dependency module, or statement correction is needed. The node copy
changes only `lean`. The module docstring names the source, and the declaration docstring
preserves all eleven proof steps and their dependency IDs.

Source checked: Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
[primary PDF](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf),
Theorem 3.5.5, Steps 2–5, printed pp. 22–24; also Lemma 3.5.1 and Proposition 3.5.2.
The statement is the affine separably closed valuation-field case extracted in the node,
with its explicitly permitted zero algebra. No repair note exists for this item.

Clause-by-clause correspondence:

| Node hypothesis/object/clause | Lean rendering and interpretation |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| V is a subring of K satisfying the inverse alternative | `(V : ValuationSubring K)`; Mathlib's structure extends `Subring K` and has `mem_or_inv_mem' : ∀ x, x ∈ V ∨ x⁻¹ ∈ V`. The x=0 case adds nothing since 0 belongs to every subring. |
| Its fraction field is K | The canonical `Algebra V K` and `IsFractionRing V K` instance of `ValuationSubring` (ValuationSubring.lean:153); no extra hypothesis is imposed. |
| Commutative V-algebra A | `(A : Type v) [CommRing A] [Algebra V A]` |
| A flat over V | `[Module.Flat V A]`, the recorded dependency's flat-module declaration; this is equivalent to `(algebraMap V A).Flat` by `RingHom.flat_algebraMap_iff`. |
| A finitely presented over V | `[Algebra.FinitePresentation V A]` |
| A_K = A tensor_V K | `A ⊗[V] K`, with the commutative tensor-product ring structure |
| Generic fibre geometrically reduced | `hgeom : @Algebra.IsGeometricallyReduced K (A ⊗[V] K) _ _ (Algebra.TensorProduct.rightAlgebra (R := V) (A := A) (B := K))`. The explicit instance is the canonical K-action on the second factor, not an arbitrary algebra structure. Over a field this is equivalently reducedness after every field extension: Mathlib tests an algebraic closure (`Algebra.isGeometricallyReduced_field_iff`); the usual algebraic-closure criterion gives arbitrary extensions, including transcendental extensions. No algebraicity restriction is placed on the node's hypothesis. |
| Regard A as a subring of A_K | The A-algebra structure is Mathlib's default `Algebra.TensorProduct.leftAlgebra`; its algebra map is a ↦ a tensor 1. Flatness gives its injectivity by tensoring V ↪ K. The statement does not replace that canonical map by a chosen injection or impose injectivity as an additional hypothesis. |
| B consists of roots of monic polynomials over A | `integralClosure A (A ⊗[V] K)`. Its carrier is `{b | IsIntegral A b}` and `IsIntegral` means a monic polynomial evaluates to zero. Its A-action and V-action are the canonical induced ones. |
| B is a finite A-module | First conjunct `Module.Finite A (integralClosure A (A ⊗[V] K))` |
| B is flat over V | Second conjunct `Module.Flat V (integralClosure A (A ⊗[V] K))` |
| B is finitely presented over V | Third conjunct `Algebra.FinitePresentation V (integralClosure A (A ⊗[V] K))` |
| The canonical B tensor_V K → A_K is an isomorphism | Fourth conjunct `Function.Bijective (Algebra.TensorProduct.lift ((integralClosure A (A ⊗[V] K)).val.restrictScalars V) (Algebra.TensorProduct.includeRight : K →ₐ[V] A ⊗[V] K) (fun _ _ ↦ Commute.all _ _))`. This is a specific algebra homomorphism; on b tensor k it sends to b·(1 tensor k). A bijective algebra homomorphism is exactly an isomorphism. No unrelated abstract isomorphism is substituted. |
| Reduced B tensor_V Ω for every homomorphism to an algebraically closed field | Final conjunct `∀ (Ω : Type (max u v w)) [Field Ω] [IsAlgClosed Ω] [Algebra V Ω], IsReduced ((integralClosure A (A ⊗[V] K)) ⊗[V] Ω)`. A commutative-ring algebra structure encodes an arbitrary unital homomorphism V → Ω; every such homomorphism has this algebra structure. There is no assumption Ω extends K, so closed and intermediate fibres are included. |
| Arbitrary valuation height | No Krull-dimension, rank, finite-height, discrete, complete, or Noetherian assumption appears. |
| Zero algebra allowed | There is no `[Nontrivial A]`, `[IsDomain A]`, faithful-flatness assumption, or nonempty-spectrum condition. `IsReduced` permits the zero ring. |

The universes `u v w` are explicitly declared; K and A may have independent sizes.
The target field has universe `max u v w`, at least as large as both inputs. Since `w`
is arbitrary, this covers arbitrarily large targets and avoids an accidentally vacuous
field-valued quantifier. No `let` binder, file-local notation/instance, private copy of
a construction, or auto-bound variable occurs.

Dependency declarations used (their full signatures/docstrings were read):

- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed` (listed
  alongside `IsSepClosure` in its record). We need its first notion, not a choice of closure.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat` and
  `Module.Flat`, related by `RingHom.flat_algebraMap_iff`.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation` (finite polynomial generators and finitely generated kernel).
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (`fg_top`, exactly finite generation).
- Other standard constructions are used directly: `ValuationSubring`, `integralClosure`,
  `Algebra.IsGeometricallyReduced`, `Algebra.TensorProduct.rightAlgebra`,
  `Algebra.TensorProduct.lift`, `Algebra.TensorProduct.includeRight`, `IsReduced`.

The module imports the recorded, already stated proof prerequisites, including
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`,
`Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal`,
`Sheaf.FieldTheory.ValueGroupDivisible`, and
`Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation`, as non-public imports.
The Mathlib proof imports cover finite morphisms, properness, flatness, finite presentation,
affine tensor-product fibres, completion modulo powers, localization of integral closure,
integral transitivity and torsion-free flatness. Six proof-only nodes currently have no
Lean record or Mathlib match: `lem-trf-geometric-reducedness-algebraic-closure-test`,
`lem-trf-sepclosed-valuation-geometric-components`, `lem-trf-valuation-arbitrary-height-limit`,
`lem-trf-valuation-finite-height-composition`, `lem-trf-valuation-grauert-remmert-powerbounded`,
and `lem-trf-valuation-rank-one-formal-comparison`. These are not needed to
state this theorem; their full proof plans remain in the docstring. No proof import was
omitted for an import cycle.

Edge cases checked before and after writing:

- A=0: its tensor products and relative integral closure are zero, their modules are
  finitely generated and flat, and the canonical map between zero rings is bijective.
- V=K (height zero): A_K is canonically A and its relative integral closure is A;
  the result gives the assumed finite presentation/flatness and geometric reducedness.
- Generic-fibre-empty case: the zero algebra is included. More generally flatness over
  the domain V makes A → A_K injective, so A_K=0 forces A=0; no hidden exclusion occurs.
- Arbitrary positive or infinite valuation height: the statement has no size-of-spectrum
  or finite-height binder. All characteristics, including mixed characteristic V, remain.
- Algebraically closed Ω need not contain K; its V-algebra structure may have a nonzero
  kernel. Thus the conclusion is about all geometric fibres, not just the generic fibre.
- A may have components on which a nonzero scalar becomes a unit. Neither completion
  injectivity nor locality of A is assumed.

Searches made for an existing theorem (all three services were called through msearch.py):

1. LeanFinder: `relative integral closure of a flat finitely presented algebra over a
   separably closed valuation field is finite and has reduced geometric fibres` — eight
   hits, including `IsIntegralClosure.finite`, `Ring.instFiniteNormalClosure`,
   `Algebra.IsGeometricallyReduced`, and field-extension localization results; none states
   this theorem. `IsIntegralClosure.finite` assumes an integrally closed Noetherian base
   and a finite separable extension of fields, not this relative algebraic situation.
2. Loogle: `"integralClosure", "finite"` — four hits: two fraction-field results,
   integral closedness for finite field extensions, and `IsIntegralClosure.finite`;
   no match for the item.
3. msearch grep, RingTheory: `integralClosure.*finite|valuation.*reduced|IsGeometricallyReduced`
   — eighteen hits, identifying integral-closure finiteness and geometric-reducedness
   definitions, with no matching theorem.
4. LeanSearch: `relative integral closure of a flat finitely presented valuation algebra
   has reduced geometric fibres and is finite` — eight hits including `integralClosure`,
   valuation integrally-closedness and geometric reducedness; these provide constructions
   and individual facts, not the theorem.
5. Local rg on Mathlib, WeilConjectures and lean/Sheaf for valuation-ring,
   `ValuationSubring`, `integralClosure`, geometric reducedness, and relative normalization
   patterns. No duplicate theorem was found. The project has related valuation statements
   (finite-module presentations, value-group divisibility, semistable models), which were
   read rather than duplicated. The exact ID search in WeilConjectures gives no hits.
6. Exact proposed declaration-name search in `dag/lean_names_upstream.json`, Mathlib,
   WeilConjectures, and lean/Sheaf gives no collision.

Validation: scompile.py compiled the final single module in both sandbox and library
positions with no errors or warnings (2.6 s and 3.0 s in the final pre-report run).
The JSON signature is copied verbatim from `theorem` through its type (before `:=`).
All Lean lines have at most 100 characters. No statement dispute or node fault was found.

## Second reading by Q30

This section records the worker's second pass, not a claim that another agent reviewed it.
The dispatch brief requires self-delivery and forbids starting other agents; the maintainer
performs the independent review. I reopened the node and final file together and checked
the table above against both. The canonical K-action is explicitly rightAlgebra, while the
A-action used for integrality is leftAlgebra. The canonical map has domain B tensor_V K,
target A tensor_V K, and its two factors are the inclusion of B and the inclusion of K.
The last field quantifier uses arbitrary V-algebra structures and includes non-injective
maps V → Ω. Its universe is at least that of V and A. The flat and finite-presentation
hypotheses and both corresponding conclusions are present, and the finite-module
conclusion is over A. No finite-height, reduced-A, nonzero-A, completeness, or field-extension
hypothesis was added. The first syntax probe used RingHom.Flat as an instance binder;
this was corrected to the recorded class Module.Flat before the delivered statement was
written. No mathematical mismatch or correction of the node was needed.
