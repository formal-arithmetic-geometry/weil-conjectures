## Worker report

The delivery states `AlgebraicGeometry.exists_high_genus_equivariant_cover` in
`Sheaf.AlgebraicGeometry.HighGenusEquivariantCover`. Its sole theorem has proof `sorry`;
there are no new definitions, helper axioms, or postponed helper theorems.
The node's mathematical statement is unchanged. Only `lean` and `stmt_deps` change:
`def-weil-pure-dimension` is added for the already landed dimension predicate.
The previous worker's stage-1 stale-assignment message does not apply to this stage-2
statement task: the current node is split and reviewed, and had no Lean attachment.

Source checked: de Jong, *Families of curves and alterations* (1997), printed pp.605--608,
§§3.2--3.6, online publisher PDF https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf.
Section 3.2 gives constant extensions and fibre-product groups; §3.3 retains a field base;
§3.5 supplies the invariant radical cover and component genus bound (2.1.6); §3.6 rationalizes
the generic markings. The theorem docstring retains all thirteen DAG proof steps and their
node citations. No quotation or statement change is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| S and P are k-schemes | `S P : Scheme.{u}`, `pS`, `pP`, and `hf : f ≫ pS = pP` |
| S integral and normal | `[IsIntegral S]`, `hnormal` at every local ring |
| S projective and finite type over k | `[IsHProjective pS]`, `[LocallyOfFiniteType pS]`, `[QuasiCompact pS]` |
| P integral and finite type over k | `[IsIntegral P]`, `[LocallyOfFiniteType pP]`, `[QuasiCompact pP]` |
| f is H-projective | `[IsHProjective f]`, the finite projective-space embedding convention |
| All geometric fibres pure dimension one | `hpure`, for every algebraically closed Ω and every `Spec Ω ⟶ S` |
| Generic fibre smooth and geometrically integral | instances on `pullback.snd f S.fromSpecFunctionField` |
| M is a closed subset | `M : Closeds P` |
| Reduced generic marking finite etale | `hMfinite` and `hMetale` on the vanishing-ideal subscheme of `M.preimage` in the actual generic fibre |
| H finite, acting on k, P, S | `(H : Type v) [Group H] [Finite H]`, monoid homomorphisms `σk`, `σP`, `σS` |
| Actions compatible and preserving M | `hP`, `hS` give semilinearity; `hequiv` gives equivariance of f; `hMstable` gives set invariance |
| Normal integral S₁ | existential `S₁`, its `IsIntegral` witness, and the stalkwise normality conjunct |
| S₁ projective finite type over k | `IsHProjective (b ≫ pS)`, `LocallyOfFiniteType (b ≫ pS)`, `QuasiCompact (b ≫ pS)` |
| Finite surjective S₁ → S | `IsFinite b ∧ Surjective b` |
| Integral finite-type Q | existential `Q`, `IsIntegral Q`, and finite-type conjuncts on `c ≫ pP` |
| Finite surjection to the FULL P ×_S S₁ | `r : Q ⟶ pullback f b`, `IsFinite r ∧ Surjective r`; projection equations specify c and q |
| H₁ finite and surjecting onto H | existential `H₁`, `Group`, `Finite`, `β`, `Function.Surjective β` |
| H₁ compatible with the diagram and k | `τS`, `τQ` and three equivariance equations for b, c, q; composition with hS and hP gives semilinearity via `σk.comp β` |
| Q → S₁ H-projective with pure curve geometric fibres | `IsHProjective q` and the universal geometric-fibre `IsPureDimension 1` clause |
| Generic Q fibre smooth and geometrically integral | `Smooth` and `GeometricallyIntegral` on `pullback.snd q S₁.fromSpecFunctionField` |
| Genus ≥ 2 on every normalized geometric fibre component | quantification over Ω, s and `Z : irreducibleComponents (pullback q s)`; `2 ≤ @Scheme.arithmeticGenus ...` for the function-field normalization of the reduced component, with its canonical map to Spec Ω |
| Every Ω-morphism from P¹ to the fibre is constant | universal t satisfying its Ω-linearity equation, then factorization through an Ω-point x of the fibre |
| Generic inverse marking is finite and K₁-rational | `n : ℕ`, `p : Fin n → (Spec S₁.functionField ⟶ pullback q ...)`, and `p i ≫ pullback.snd ... = 𝟙 _` |
| Those rational points are distinct and exhaust the reduced inverse marking | `Function.Injective p` and the iff for every generic-fibre point z comparing membership of its c-image in M with membership in a point-image `Set.range (p i)` |
| Marking H₁-stable as a set | image under each `(τQ h).hom` of the union of the images of p in Q equals the same union |
| K₁/K finite separable | existential algebra on the two actual function fields, `Module.Finite`, `Algebra.IsSeparable` |
| k(Q)/F finite separable | same for P and Q function fields |
| Embeddings induced by the diagram | equalities of each `algebraMap` with the transported `b.stalkMap` / `c.stalkMap` at generic points; witnesses hb and hc fix the transport |
| Both kernel fixed fields equal the original fields | for every z in each output function field, membership in the range of this exact `algebraMap` iff every `a : β.ker` fixes z under the canonical `Scheme.functionFieldAut` |
| No flatness, semistability, nodality or extended sections asserted | the conclusion contains precisely projectivity, fibres, finite covers, generic rational points and fixed-field assertions |

The input finite-type assumptions are explicit because the node states them, even though
projectivity implies them for S. The auxiliary variables c and q merely name the two
composites of r with the canonical pullback projections; the displayed equations determine
them. No assumptions on Q beyond the node's existential conclusion are imposed.
The normalized component's `Over` structure is the composite of its normalization map,
canonical reduced closed inclusion, and fibre projection. It is not an arbitrary structure.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, generic stalk field instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`: `LocallyOfFiniteType`,
  `QuasiCompact` for finite type (the conjunction used in the recorded dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, available through projectivity;
  the conclusion requires no independent properness datum.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `.UnderlyingMap`: `IsFinite`, `Surjective`.
- `WeilConjectures.AlgebraicGeometry.FunctionField` and Mathlib's `FunctionField`:
  `Scheme.functionField`, the already recorded arbitrary-integral-scheme clause.
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`, publicly available through
  `StalkAut`: `Scheme.fromSpecFunctionField`.
- `WeilConjectures.AlgebraicGeometry.StalkAut`: `Scheme.functionFieldAut`.
- `Sheaf.FieldTheory.FieldTower`: the recorded finite separable extension convention
  `Module.Finite` and `Algebra.IsSeparable`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections;
  available scheme instances give both generic and geometric fibres.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `.Etale`: `Smooth`, `Etale`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension` (existing node added
  to stmt_deps), whose component dimensions use `topologicalKrullDim` as recorded.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalizationComponent`,
  its integrality instance, and its canonical vanishing-ideal construction.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `Scheme.fromNormalization` for those integral components.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.arithmeticGenus`,
  the dependency's dimension of H¹(O), with the explicit canonical Ω-structure.
- Mathlib `Scheme.IdealSheafData.vanishingIdeal` and `subschemeι` form the reduced generic
  marking and the canonical closed component inclusion. These are existing constructions.

The other vocabulary dependencies (flatness, finite presentation, completions, power
series) describe background notions in the node's last paragraph. No assertion involving
flatness or nodal equations is part of this auxiliary-cover theorem, so their notions
are neither redefined nor inserted as hypotheses or conclusions.

All already stated proof dependencies are imported privately: finite common Galois
extensions, tensor invariants, finite etale algebra criterion, normalization, smoothness
of normalized curves, dominant lifting, Spec surjective base change, and P¹ genus zero.
Mathlib Galois.Basic, SeparableDegree and Normal.Basic supply the recorded Mathlib leaves.
The five unstated geometric construction lemmas have no module yet and are cited by id
in the proof docstring, rather than replaced by new declarations or consumer hypotheses.

Edge cases checked before writing and during the second pass:

- Empty M, or empty generic marking: n = 0 is allowed. No Nonempty indexing restriction.
- Trivial H, or nonfaithful action, including a nontrivial kernel acting trivially on input:
  no injectivity or faithfulness assumption occurs; the output fixed sets use β.ker itself.
- Nontrivial action on k: semilinearity uses the inverse in Spec to respect left actions;
  no k-linearity is silently required.
- Dimension-zero base, finite base fields, and imperfect base fields: no positive-dimensional,
  infinitude or perfectness assumption is present. Generic fibres use actual function fields.
- All characteristics, including 2, 3, 5 and 7: no characteristic bound in the theorem;
  the proof chooses a different auxiliary tame prime internally.
- Nonreduced/singular special fibres: only their reduced components are normalized;
  the theorem imposes no reducedness, flatness or nodality on whole fibres.
- Nonclosed geometric points and arbitrary algebraically closed test fields in the scheme
  universe: Ω and s are universally quantified, not only closed points of S₁.
- Empty geometric fibre conventions: IsPureDimension is vacuous on empty schemes, but the
  generic GeometricallyIntegral input and projectivity ensure the actual family dominates;
  the no-P¹ clause is also vacuous on an empty fibre.
- Distinct rational maps in the marking are genuine distinct rational points: they are sections
  over a field. Their supports, after projection into Q, are what the action-stability clause uses.
- Constant P¹ morphisms must be Ω-linear; factorization explicitly gives an Ω-section,
  so constancy is a scheme morphism factorization, not only a pointwise equality.
- Universes u and v explicitly bound: k and schemes share the standard scheme universe;
  output finite group lives in max u v. `set_option autoImplicit false` forbids hidden binders.

Searches (no exact existing theorem):

- `msearch.py ... leanfinder` query: "A finite equivariant cover of a projective family of
  curves makes every geometric fibre component have normalization genus at least two".
  Eight hits, on projective Weierstrass base change, affine-transition limit auxiliary
  objects, Weierstrass minimality and good reduction; none state the relative cover theorem.
- `msearch.py ... loogle` query: `"AlgebraicGeometry", "genus"`: zero hits.
- `msearch.py ... grep` query: `highGenus|high_genus|equivariant.*cover|cover.*genus`
  in AlgebraicGeometry: zero hits.
- `msearch.py ... leansearch` query: "Finite equivariant cover of projective curves with all
  geometric component genera at least two": eight hits, on covering maps, general scheme
  covers, and related generic infrastructure; none match the construction.
- `rg -n 'lem-sfb-high-genus-equivariant-cover|highGenus|high_genus' lean/WeilConjectures
  lean/Sheaf`: only natural-language uses in the parent nodal-reduction docstring; no
  declaration of this theorem. A subsequent search for the proposed declaration name had
  no hit. Read the parent's complete signature as a consumer compatibility check.
- Searched existing normalization, semilinear-action, pure-dimension, and fixed-field
  interfaces in the same source directories. Found and reused all notions above.

Validation: `scompile.py Q03 lem-sfb-high-genus-equivariant-cover <module>` compiled both
sandbox and actual library module names cleanly (3.2 s and 3.1 s), under the 60-second limit.
The first passes exposed underconstrained category inference for a pullback in a component
binder, and arrow precedence in the marking family. Both were repaired explicitly:
`pullback (C := Scheme.{u})` and `Fin n → (Spec K₁ ⟶ ...)`. No raised limits.
No statement dispute, no source correction, no dependency repair, and no new node.

## Second reading by Q03

A second pass of the node and the complete final signature checked all rows above,
particularly the full pullback target, both generic-stalk algebra-map equalities, both
β.ker fixed sets, semilinear field action, genus on normalized reduced components,
and the generic-only marking. This pass corrected the marking family parentheses:
`Fin n → (Spec K₁ ⟶ ...)` must be a family of scheme morphisms. It also verified that the
explicit Over structure in arithmeticGenus uses the canonical component inclusion.
This is the worker's own second pass; no independent worker was launched, in accordance
with the dispatcher brief. The maintainer's independent delivery review remains required.
