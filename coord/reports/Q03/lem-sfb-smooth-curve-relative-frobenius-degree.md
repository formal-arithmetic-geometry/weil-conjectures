## Worker report

Item: lem-sfb-smooth-curve-relative-frobenius-degree. The delivery adds
`Sheaf.AlgebraicGeometry.Curve.RelativeFrobeniusDegree`, declaring
`AlgebraicGeometry.smooth_proper_curve_relative_frobenius_degree` with proof `sorry`.
It adds no definitions and changes only the item's `lean` record. The natural-language
statement, statement dependencies, proof, and proof dependencies are unchanged.

The earlier failure confused the merged stage-1 split with a stage-2 binding. The live
node has a stage-1 review by NE but no `lean` record. At the start of this attempt the
sandbox contained only dispatcher brief marker files, not a Lean module or node copy.
This packet supplies the missing stage-2 binding, so the item's node file changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- Characteristic p > 0 is `(p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)`.
  Over a field these are equivalent to positive characteristic p: the least positive
  characteristic is prime, and a prime vanishing in a nonzero field is its characteristic.
  This uses the existing absolute-Frobenius interface, also used by the immediate citer
  `existsUnique_purelyInseparable_curve_frobenius`; it imposes no additional restriction.
- The k-scheme is `(C : Scheme.{u}) (sC : C ⟶ Spec (.of k))`. Its curve condition is
  `[IsCurve sC]`, smoothness `[Smooth sC]`, properness `[IsProper sC]`, integrality
  `[IsIntegral C]`, and dimension one `(hCdim : topologicalKrullDim C = 1)`.
- Every integer n >= 0 is represented by `(n : ℕ)`, with no positive-n assumption.
- The base power map is `iterateFrobeniusOfPrime k hp hk n`, whose actual value at a
  is `a ^ p ^ n`. Its spectrum is `Spec.map (CommRingCat.ofHom ...)`.
- The twist is literally `pullback sC (Spec.map (CommRingCat.ofHom ...))`; its structure
  morphism is literally `pullback.snd sC (Spec.map (CommRingCat.ofHom ...))`.
  No independently chosen curve or arbitrary morphism replaces either object.
- The conclusion first provides `∃ (_ : IsIntegral (pullback ...)), ...`. This is proof
  data supplying the generic stalk's field instance; the underlying scheme is already
  the fixed pullback. It then asserts `IsCurve (pullback.snd ...)`,
  `Smooth (pullback.snd ...)`, `IsProper (pullback.snd ...)`, and
  `topologicalKrullDim (pullback ... : Scheme.{u}) = 1`, precisely all twist properties.
- `∃ hC : (p : Γ(C, ⊤)) = 0` supplies the proof needed by the recorded absolute Frobenius.
  This is a conclusion, not an added characteristic hypothesis on C.
- `∃! F : C ⟶ pullback ..., ...` together with the first two conjuncts specifies the
  canonical map uniquely: `F ≫ pullback.fst ... = C.iterateFrobenius hp hC n` and
  `F ≫ pullback.snd ... = sC`. Those equations are exactly the pair (F_C^n, sC) in
  the statement and source 0CCG. Uniqueness follows from the pullback universal property;
  this is not an unspecified existential map, a Nonempty choice, or an extra assumption.
- Nonconstancy is exactly the negation of the existence of a k-rational point y with
  `y ≫ pullback.snd ... = 𝟙 _` and `sC ≫ y = F`. It uses scheme morphisms and their
  k-structures, not merely cardinality of the image on points.
- The induced function-field embedding is the existing `F.functionFieldMap hη`, where
  `hη : F (genericPoint C) = genericPoint (pullback ... : Scheme.{u})` is supplied in
  the conclusion. `Function.Injective (F.functionFieldMap hη).hom` expresses embedding.
  There is no freely chosen ring map: this is the actual generic stalk map.
- The degree equality is `@FieldExtension.degree (pullback ...).functionField
  C.functionField _ _ (F.functionFieldMap hη).hom.toAlgebra =
  ((p ^ n : ℕ) : WithTop ℕ)`. Restricting scalars along the embedding identifies its
  source with its image, so this is precisely `[k(C):F^*k(C^(p^n))]=p^n`, including
  finiteness (an infinite extension has degree top, not zero).
- At n = 0, the ring power map is the identity and the pullback is the identity base
  change. The first projection is the canonical identification with C. The first
  projection equation reads F followed by that identification equals id_C because
  `C.iterateFrobenius hp hC 0` is id_C. Thus the required identity convention is already
  enforced by the same equations, rather than introducing a second definition at zero.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (commutative ring and division ring).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and its Basic import: `IsAlgClosed`,
  the algebraically-closed-field clause of def-weil-algebraic-closure. No chosen closure
  extension is needed because the item already starts with an algebraically closed field.
- `Mathlib.Algebra.CharP.Defs`: `CharP`, `ringChar`; equivalently positive prime p vanishes
  in k. `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`: `iterateFrobeniusOfPrime`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`; smooth and proper
  are the separate existing morphism predicates, as its docstring specifies.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded component-product
  convention; its integral-scheme clause explicitly reuses Mathlib `Scheme.functionField`,
  the generic stalk. This is the clause relevant to both curves here.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `AlgebraicGeometry.Scheme.Hom.functionFieldMap`, constructed from `stalkSpecializes`
  and `stalkMap`, provides the actual induced embedding, not a duplicate construction.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra` for the extension structure.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree`, using finrank when finite and
  top otherwise, not bare finrank with its infinite-dimensional zero convention.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded definition's
  note explicitly specifies `Limits.pullback`, `pullback.fst`, and `pullback.snd` for
  scheme base change. The primary `moduleBaseChange` declaration is only for modules;
  the scheme convention is already usable and requires no dependency repair.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`, `iterateFrobenius_apply`, and
  `iterateFrobenius_app_apply`. The characteristic proof hC is supplied in the result.

Proof dependencies with recorded modules are imported privately, including the proper
curve/function-field correspondence, smooth-differential rank, p-basis existence and
p-basis differentials. Mathlib imports provide proper/smooth base change, affine fraction
fields, differential localization, and field-degree multiplicativity. No downstream
purely-inseparable-factorization theorem is imported, avoiding the dependency cycle.
The six-step natural-language proof is included in the theorem docstring.

Edge cases checked before writing:

- n = 0: identity base change and relative identity, degree p^0 = 1, and nonconstant
  identity because the curve has dimension one.
- p = 2: all formulas and the field-degree induction remain valid.
- p = 0 or p = 1: appropriately excluded by positive characteristic, expressed by prime p.
- Empty schemes, zero-dimensional points, or disconnected schemes: the source requires
  integrality and dimension one; these are correctly excluded. No extra connectedness
  binder is imposed; it follows from integrality.
- C = P^1: its function field is k(t), with image k(t^(p^n)) and degree p^n.
- The twist's first projection is only an isomorphism of schemes, not generally a
  k-isomorphism. The statement uses its second projection for the k-structure and never
  substitutes a k-linear identification with C.
- The function-field degree uses the algebra induced by F, not a globally inferred
  algebra that could accidentally refer to another extension.
- All universes and variables are explicit (`universe u`, `set_option autoImplicit false`).
  The same universe for the field and scheme is the project's standard Scheme/Spec
  convention; a smaller field can be lifted to the scheme universe as usual.

Searches (2026-10-22):

- `msearch.py ... leanfinder "The iterated relative Frobenius of a smooth proper integral
  curve in characteristic p has degree p^n"`: eight hits, including
  `iterateFrobeniusEquiv_eq_pow`, `iterateFrobenius_eq_pow`,
  `IsPurelyInseparable.iterateFrobeniusₛₗ`, and `iterateFrobeniusEquiv_def`. They concern
  algebraic Frobenius, not the curve geometry and generic-stalk degree statement.
- `msearch.py ... loogle '"frobenius", "Scheme"'`: zero hits.
- `msearch.py ... grep 'relativeFrobenius|relative_frobenius|frobeniusTwist'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg -n 'relativeFrobenius|relative_frobenius|frobeniusTwist|FrobeniusTwist|
  lem-sfb-smooth-curve-relative-frobenius-degree'` on both project's Lean roots:
  finite-field-model endomorphisms, general relative-Frobenius finiteness and universal
  homeomorphism, site-local private comparisons, and a citation in the downstream
  `PurelyInseparableFrobenius` module. None states this degree theorem. In particular,
  `relativeFrobenius_finite` assumes positive n and proves finiteness, not degree;
  `relativeFrobenius_integral_universalHomeomorphism` concerns the first iterate and
  proves neither twist curve geometry nor degree. Their projection-equation interfaces
  confirm the existing convention used here; no general notion is defined again.
- Read the actual source paragraphs in `literature/stacks-project/varieties.tex`
  (`lemma-inseparable-deg-p-smooth`, `remark-n-fold-relative-frobenius`) and
  `curves.tex` (`lemma-inseparable-deg-p-smooth`). The former gives degree p^dimension;
  the latter gives the smooth/proper twist observation and rank-one differential argument.

No statement correction, disputed statement, dependency repair, or new node is needed.
The previous unchanged-node preflight failure is repaired by the new Lean binding.

Validation: the prescribed server compiler accepted both sandbox and library forms of
the module after adding explicit Scheme annotations to the two topological pullback
occurrences. No errors or unexpected warnings remain. Final dry-run and delivery results
are recorded below after their execution.

## Second reading by Q03

This is the worker's explicit second pass; no additional agent was started. The maintainer's
independent review remains the external review of this delivery. I reopened the node and
compared the signature clause by clause: algebraic closure; positive characteristic;
separated finite-type curve; smoothness; properness; integrality; dimension one; all n >= 0;
the actual base power map; both projections; twist geometry; nonconstancy through a
k-rational point; actual generic stalk embedding; and degree p^n are all present, with
the correspondences detailed above. In particular, the n = 0 convention follows from
the two defining equations and the identity-base-change isomorphism, and the degree
uses F's algebra rather than an unrelated field inclusion. No mathematical mismatch was
found and no source statement was changed. The only elaboration repair was to annotate
the fixed pullback as a Scheme where Lean otherwise inferred a pullback in Type.

Final validation: `deliver2.py Q03 lem-sfb-smooth-curve-relative-frobenius-degree
--no-push` returned `OK (dry run): commit 78671ff3fa3 passes the preflight and compiles;
nothing pushed`. Both sandbox and library forms compiled with the final imports.
The prescribed non-dry-run wrapper submits the packet for the maintainer's review.
