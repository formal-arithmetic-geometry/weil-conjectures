## Worker report

The module `Sheaf.RingTheory.PrimeLocalSmoothParameterModels` states
`IsLocalRing.exists_prime_local_smooth_parameter_models`. Its only theorem has
`sorry` as its proof; no definitions or auxiliary axioms are introduced.
The module docstring records the ten proof steps of the DAG node.
The node is unchanged except for its `lean` record.

Hypotheses and clauses, read against the complete node statement:

- Prime field: `[Field k₀]` and `hprime` express that the base field is isomorphic
  to ℚ or to `ZMod p` for a prime `p`. Transport along a ring equivalence does not
  change the assertion. No finiteness, algebraicity, or perfection condition is
  imposed on the residue field.
- Local algebra B: `[CommRing B] [Algebra k₀ B] [IsRegularLocalRing B]`.
  Mathlib's regular-local class includes localness and Noetherianity; local rings
  are nontrivial. Thus these encode every assumption on B without redundant binders.
- Completeness: `[IsAdicComplete (maximalIdeal B) B]` is precisely maximal-adic
  completeness, as in the recorded completion dependency.
- Dimension: the existential natural number `d` satisfies
  `ringKrullDim B = (d : WithBot ℕ∞)`. It is not an extra hypothesis.
- Generators: `t : Fin d → B` and
  `Ideal.span (Set.range t) = maximalIdeal B`. The equality also forces every
  `t i` to lie in that ideal. `Sequence.IsRegular B (List.ofFn t)` is the final
  requested B-regularity clause.
- Small nonempty directed poset: `I : Type u`, `PartialOrder I`,
  `IsDirected I (· ≤ ·)`, `Nonempty I`. The ring carriers and I have the same
  universe, as required by the colimit convention. PartialOrder, rather than the
  general convention's Preorder, is intentional: this node explicitly asks for
  a poset and its proof supplies a poset replacement.
- Directed system of P-algebras: `C : I ⥤ CommAlgCat k₀` and the natural
  transformation `τ : const P ⟶ C`, where `P = MvPolynomial (Fin d) k₀`.
  A k₀-algebra under P is exactly a P-algebra. Naturality of τ is precisely
  P-linearity of all transitions; using this under-object presentation avoids
  any chosen algebra structures depending on existential parameters.
- Compatible maps to B: the natural transformation β and the equality
  `(β.app a).hom.comp (τ.app a).hom = MvPolynomial.aeval t` for every stage.
  Evaluation sends each variable to the specified `t i`, so every leg is a
  P-algebra map for exactly the required parameter structure on B.
- Smooth stages: `Smooth (Spec.map (ofHom (τ.app a).hom.toRingHom))`.
- Stage regularity and nonzero condition: `Nontrivial (C.obj a)` and
  `IsRegularRing (C.obj a)`; the latter includes Noetherianity.
- Stage regular sequences: `Sequence.IsRegular (C.obj a)` on the ordered list
  of the images of `MvPolynomial.X`. Naturality of τ says transitions send each
  displayed variable image to that same image at the target stage, whose
  regularity is asserted. This is preservation of the displayed sequence;
  no flatness of transition maps is required or asserted.
- Invertible primes: for every natural prime ℓ, `IsUnit (ℓ : B)` implies
  `IsUnit (ℓ : C.obj a)` at every stage, all in the same simultaneous diagram.
- First colimit: `Nonempty (IsColimit ...)` of the underlying ring cocone with
  vertex B and exactly the legs β. By the universal property this is equivalent
  to the canonical map from the ring colimit being an isomorphism, not merely
  an unrelated abstract isomorphism.
- Quotient system: D, q, and the stage algebra equivalences e identify `D.obj a`
  with the actual ring `C.obj a ⧸ span {τ_a(T_i)}`. The equation
  `e (Ideal.Quotient.mk _ x) = (q.app a).hom x` normalizes these equivalences
  on the quotient projection. Naturality of q then forces D's transitions to
  be precisely the induced quotient transitions, because projection is surjective.
  This is an isomorphic presentation of the stated quotients, not unspecified
  rings with arbitrary quotient maps.
- Quotient regularity: `Nontrivial (D.obj a) ∧ IsRegularRing (D.obj a)`.
  Smoothness over k₀ is the recorded scheme Smooth predicate on the spectrum
  of `algebraMap k₀ (D.obj a)`.
- Immersion: `IsRegularClosedImmersionWithCodimension (Spec.map q_a) (fun _ ↦ d)`
  is the recorded definition, with constant codimension d, including its
  closed-immersion condition.
- Residue field: `ResidueField B` is definitionally `B ⧸ maximalIdeal B`.
- Second colimit: `IsColimit` with vertex `ResidueField B` and exactly the legs γ.
  The last equality `γ_a ∘ q_a = residue B ∘ β_a` ties this colimit to the first.
  This square together with the two universal properties says exactly that
  the second is the quotient of the first by the parameters. Contravariance
  of Spec then identifies the limiting immersion with Spec(residue B).
- Dimension zero is included: `Fin 0` and `List.ofFn` give the empty sequence,
  its generated ideal is zero, and quotienting by zero identifies D with C.
  We use specified algebra equivalences rather than literal type equality for
  this canonical quotient identification, also when d is zero.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (included in regular classes).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, `IsRegularRing`,
  the ring clauses of `def-weil-regular-scheme`. Its recorded scheme module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is imported; this statement uses
  the ring clauses, not the scheme-specific predicate.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` is the recorded
  scheme specialization of `IsLocalRing.ResidueField`; here the node concerns
  a local ring, so we use that underlying Mathlib definition and `residue`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `aeval`, `X`.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `.Cones`, `.IsLimit`: cocones and
  `IsColimit`; these express the recorded category-colimit universal property.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`:
  `AlgebraicGeometry.IsRegularClosedImmersionWithCodimension`.
- Supporting standard APIs: `CommAlgCat`, `Ideal.Quotient`, `Ideal.span`,
  `AlgEquiv`, natural transformations and the forgetful functor to `CommRingCat`.

All already-stated proof dependency modules are imported privately, including
Cohen coefficients, complete coordinates, origin regularity, flat-over-regular,
complete and finite-type G-rings, maximal-local regularity, Popescu smoothing,
directed reindexing, polynomial regularity, smooth regularity ascent and smooth
flatness. The proof dependency `lem-per-g-ring-local-closed-fibre-criterion` has
no recorded declaration/module in the read checkout, so there is no import to
add yet. It is needed only for the future proof, not to state this result.

Edge cases checked: d = 0 (field case, zero ideal, empty regular sequence,
identity quotient immersions up to canonical quotient isomorphism); both prime
field alternatives; arbitrary residue extensions including imperfect and infinite
ones; nonempty versus empty indexing; primes equal to the positive characteristic
(the invertibility antecedent fails); primes invertible in characteristic zero;
no flatness of transitions. No counterexample or node fault found.

Searches for an existing statement:

- msearch LeanFinder: “A complete regular local algebra over a prime field is a
  directed colimit of smooth polynomial algebras with compatible parameter
  quotients”: eight hits, including `Algebra.Smooth` and standard smoothness;
  none states the simultaneous package.
- msearch LeanSearch: “complete regular local ring directed colimit smooth
  algebras polynomial parameter regular sequence”: eight hits including
  `Ring.DirectLimit` and regular sequence flat base change; none matches.
- msearch Loogle: `MvPolynomial.aeval, Ideal.Quotient.factor,
  CommAlgCat.quotient`: no hits; no `CommAlgCat.quotient` declaration.
- msearch grep: `parameter.*[Mm]odel|smooth.*[Pp]arameter|[Pp]arameter.*smooth`:
  eight unrelated geometry/computability hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for parameterModel,
  smooth_parameter, smoothParameter, parameterQuotient, and the item id:
  no matching existing package. Direct grep of the item id in WeilConjectures:
  no hits. Further RingTheory searches for parameter/quotient combinations
  provide no duplicate of this statement. The proposed declaration name was
  also searched in both libraries and `dag/lean_names_upstream.json`: no hits.

Validation: scompile.py compiled the delivered module in sandbox and library
module modes successfully (51.3 s and 3.1 s). No compiler errors or disallowed
warnings. Only the prescribed wrappers are used for compilation/delivery.

## Second reading by NH

A second pass in this dispatcher worker reopened the node statement and compared
its clauses to the module signature above; no second agent was started. Checked
in particular that the diagrams are over the polynomial ring through τ, that
both colimits use the specified legs, that q is the actual parameter projection
up to its normalized equivalence, that the last square uses the actual residue
map, and that constant codimension is asserted using the dependency definition.
The first reading prompted the explicit normalization of quotient equivalences,
rather than a bare isomorphism of quotient objects. Rechecked d = 0, prime-field
characteristics, nontriviality and all universe/index binders. No additional
statement correction or dependency module is needed.
