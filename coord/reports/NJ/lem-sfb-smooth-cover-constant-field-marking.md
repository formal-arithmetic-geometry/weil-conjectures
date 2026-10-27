## Worker report

The single module `Sheaf.AlgebraicGeometry.Curve.SmoothCoverConstantFieldMarking`
states `AlgebraicGeometry.smooth_cover_constant_field_marking`, with `sorry` as
its whole proof. It introduces no definitions or additional postponed theorems.
The module and theorem docstrings cite Stacks Tags 03H0, 0BUG, 0G80 and 0C4Q
and de Jong §3.5; the theorem docstring carries all seven DAG proof steps.
The source statements were read in the local Stacks files. The current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
direct-images proof was also read. This is an auxiliary alteration lemma, not a
change to the blueprint unit's statement. No statement correction is needed.

Hypothesis and object correspondence:

- `K : Type u` and `[Field K]` give the ground field.
- `C Y : Scheme.{u}`, with structure morphisms `c` and `y`, specify the two
  K-schemes. `[IsSmoothProjectiveCurve c]` and
  `[IsSmoothProjectiveCurve y]` include integrality, separatedness, finite type,
  dimension one, smoothness and projectivity, exactly as the recorded definition
  states. `[GeometricallyIntegral c]` supplies the additional condition on C.
- `C.functionField` and `Y.functionField` are F and L, their actual generic
  stalks. The two `Algebra K ...` binders are equipped with the equations
  `hK_C` and `hK_Y`, fixing both ground-field inclusions to the structural map
  on global sections followed by generic evaluation. These are explicit
  presentations of the specified inclusions, not arbitrary algebra structures
  or extra geometric hypotheses. They can always be supplied by `RingHom.toAlgebra`
  of the displayed composites. No relation between site universes is imposed.
- `ν : Y ⟶ C`, `[IsFinite ν]`, `[Surjective ν]`, and `hν : ν ≫ c = y`
  render the finite surjective K-morphism.
- The inclusion F into L used in the intersection formula is
  `@algebraMap C.functionField Y.functionField _ _ ν.dominantFunctionFieldAlgebra`.
  This is the recorded actual generic-stalk map; surjectivity supplies dominance
  by Mathlib's instance. No arbitrary field embedding is supplied as a hypothesis.
- `U : C.Opens` and `[Etale (ν ∣_ U)]` render the open and the stipulated
  étaleness of its inverse image over U.
- `M : Scheme.{u}`, `iM : M ⟶ C`, `[IsClosedImmersion iM]`, `[IsReduced M]`,
  `[IsFinite (iM ≫ c)]`, and `[Etale (iM ≫ c)]` give the reduced finite étale
  closed K-subscheme. `hM : Set.range iM ⊆ (U : Set C)` says it is contained in U.
- `E : IntermediateField K Y.functionField` and `hE : E = algebraicClosure K
  Y.functionField` spell out 'put E = ...'. Membership in this existing Mathlib
  relative algebraic closure is exactly algebraicity over K. E is the specified
  subfield of L, not an existentially chosen abstract field.

Conclusion correspondence:

- `FiniteDimensional K E ∧ Algebra.IsSeparable K E` says finite dimension and
  separable minimal polynomials, as the node explicitly requests.
- `algebraicClosure K C.functionField = ⊥` states that K is algebraically closed
  in F. The next universal biconditional says that the image of z in L belongs
  to E if and only if z is in the image of K in F. As the actual field map is
  injective, this is exactly E ∩ F = K inside L, including the reverse inclusion.
- `∃ e : Γ(Y, ⊤) ≃+* E` together with
  `(e s : Y.functionField) = Y.germToFunctionField ⊤ s` identifies global
  sections with this embedded E by generic evaluation. Injectivity of the
  subtype inclusion makes e unique. The explicitly supplied nonemptiness of
  the top open uses the generic point already provided by integrality.
- `qE : Y ⟶ Spec (CommRingCat.of E)` is fixed by
  `qE = Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)`.
  Thus it is the canonical map induced by inverse generic evaluation on
  global sections. This displayed formula and uniqueness of e give canonicity;
  an unspecified factorization map would not suffice.
- `qE ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) = y` is precisely
  the structural factorization over K.
- `Y.fromSpecFunctionField ≫ qE = Spec.map (CommRingCat.ofHom
  (algebraMap E Y.functionField))` gives the required generic-composite identity
  with the actual subtype inclusion E into L.
- `IsSmoothProjectiveCurve qE ∧ GeometricallyIntegral qE` gives the new
  smooth projective geometrically integral E-curve. It uses the same scheme Y,
  so its function field is literally the same `Y.functionField` generic stalk;
  the preceding equation specifies its E-inclusion. No second function-field
  object or abstract comparison is substituted.
- `pullback ν iM` is P. `IsReduced (pullback ν iM)` says that this
  scheme-theoretic inverse image is already reduced, which is exactly the
  'hence equals the reduced inverse image' clause. As in the recorded parent
  `tame_radical_curve_normalization`, this consequence is expressed by
  reducedness of the actual pullback; no separate reduced model is chosen.
- `IsFinite (pullback.fst ν iM ≫ qE) ∧ Etale (pullback.fst ν iM ≫ qE)`
  gives both required properties of the specified structural morphism P to Spec E.

Dependency declarations used:

- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`).
- `def-pc-smooth-projective-curve`: `AlgebraicGeometry.IsSmoothProjectiveCurve`,
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`; its complete
  inheritance chain `IsIntegralCurve` and `IsVariety` was read.
- `def-pc-integral-scheme` and `def-pc-reduced-scheme`:
  `AlgebraicGeometry.IsIntegral`, `AlgebraicGeometry.IsReduced`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIntegral`,
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`.
- `def-sc-function-field`: the recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField` explicitly documents that
  the integral-scheme clause uses Mathlib's `Scheme.functionField`.
  `Scheme.germToFunctionField` is its generic evaluation; `Scheme.fromSpecFunctionField`
  from `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField` is the corresponding
  generic morphism, literally `fromSpecStalk (genericPoint Y)`.
- `def-pc-field-extension`: Mathlib `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-relative-algebraic-closure`: Mathlib `algebraicClosure`,
  `Mathlib.FieldTheory.AlgebraicClosure`, read with `mem_algebraicClosure_iff`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; its integral companion's
  signature was also read, but only finiteness is used here.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.fst`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- The existing landed `def-sfb-dominant-function-field-map` is added to
  `stmt_deps` under the rule permitting additional landed dependencies. Its
  `Scheme.Hom.dominantFunctionFieldAlgebra` in
  `Sheaf.TraceFormula.LocalDimensionFormula` is read and used directly.
  No dependency record is repaired and no new node is introduced.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` supplies `Scheme.toSpecΓ`.
  All already recorded proof-dependency modules are imported without `public`;
  Mathlib permanence facts are available from the public finite/étale imports.
  The two proof nodes without recorded declarations,
  `lem-sfb-normal-sections-algebraic-constants` and
  `lem-trf-smooth-connected-fibre-normal-integrality`, require no extra imports
  and are not used in the statement's type.

Edge cases were checked before writing: U empty forces M empty by `hM`;
M empty is allowed for any U, and the pullback and its finite étale structure
have no nonemptiness binder. Nonempty curves are required by the original
integral dimension-one hypothesis. The identity cover gives E=K. A constant
extension of a geometrically integral curve by a finite separable field is
covered without assuming Y geometrically integral over K. Imperfect K and
inseparable test extensions in geometric integrality are retained. There is no
characteristic restriction. All fields and schemes share the standard scheme
universe u, with no independently smaller test universe. E, as a subtype of L,
is in that universe. No false or disputed clause was found.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A smooth projective integral curve over a field
  is geometrically integral over its finite separable algebraic constant field
  and finite etale markings remain etale over that field"`: eight unrelated
  Weierstrass/smooth-ring hits, no theorem matching this statement.
- `msearch.py ... loogle "algebraicClosure, Scheme.germToFunctionField,
  Scheme.Hom.dominantFunctionFieldAlgebra"`: no hits; the endpoint reported
  `unknown identifier 'Scheme.germToFunctionField'`. Local source inspection
  found the qualified declaration and the actual canonical-map interface.
- `msearch.py ... leansearch "smooth projective curve constant field global
  sections finite separable geometrically integral"`: eight hits, including
  `finite_appTop_of_universallyClosed`, `isField_of_universallyClosed`, and
  `Scheme.ΓSpecIso`; none is the assembled statement.
- `msearch.py ... grep "algebraicClosure|constantField" AlgebraicGeometry`:
  two Mathlib hits concerning algebraic closures in group scheme files,
  no assembled constant-field/marking theorem.
- `rg -n` in `lean/WeilConjectures` for the item id returned no match.
  Searches there for `dominantFunctionField`, `functionFieldAlgebra`,
  `functionFieldMap`, `germToFunctionField`, and `constant.field` located the
  existing function-field and generic-stalk interfaces, not the theorem.
- `rg -n` in `lean/Sheaf` for `constant.field`, `algebraicClosure`,
  `smooth.*cover.*constant`, and `constant.*field.*marking` found
  `NormalSteinConstantField`, `NormalAlterationConstantRegularization`, and
  `Curve/TameRadicalNormalization`. Their statements were inspected: the first
  is a general Stein theorem; the second concerns equivariant alterations;
  the parent radical-normalization statement is restricted to a particular
  Kummer normalization. None states this theorem for every finite surjective
  smooth projective curve cover.

Validation: `scompile.py NJ lem-sfb-smooth-cover-constant-field-marking` compiled
both its sandbox module and the final named module cleanly (3.2 s and 3.0 s),
after supplying the explicit generic point as a point of the top open.
Every variable and the sole universe are explicit; `autoImplicit` is false.
All lines are at most 100 characters. The only proof is `sorry`.

## Second reading by NJ

I reread the node and the complete final declaration as the dispatcher-assigned
worker; no separate agent was started. The maintainer supplies the independent
review specified by this assignment. The rereading checked each correspondence
listed above, especially the original K-structures, the actual induced F-to-L
map, the fixed subfield E, the generic-evaluation equation, the inverse-evaluation
formula for qE, and the use of `pullback.fst` for P to Y. It found no semantic
mismatch. The only elaboration repair was the explicit nonempty-top witness,
which is available from integrality and adds no hypothesis. The unchanged Y
explains why L remains its function field. Empty U and M are still admitted.
No statement, proof plan, or proof-dependency field is changed; the only
additional statement dependency is the existing canonical generic-stalk-map node.
