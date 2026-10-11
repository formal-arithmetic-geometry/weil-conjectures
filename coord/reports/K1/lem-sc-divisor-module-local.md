## Worker report

The module `lean/Sheaf/AlgebraicGeometry/DivisorModuleLocal.lean` states
`AlgebraicGeometry.Scheme.Divisor.module_local`. Its sole theorem has proof `by sorry`.
No definition is introduced, no existing node statement is changed, and no dependency
module or new node is needed. Server compilation completed cleanly in 2.2 seconds.

Hypothesis and clause correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Smooth connected curve C over k: `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`
  with `[IsConnectedCurve f] [Smooth f]`. The recorded curve declaration's connected
  specialization supplies nonemptiness, connectedness, dimension exactly one,
  separation, and finite type; properness is not imposed.
- The Noetherian integral regular structure is derived, not assumed: the statement's
  `letI` clauses use `isNoetherian_of_locallyOfFiniteType f`, `IsRegular.of_smooth f`,
  and `(C.smooth_connected_curve_local_rings k f).choose`. The latter is exactly the
  recorded local-rings dependency, not a private replacement.
- The generic point and k(C): `C.functionField` is Mathlib's generic stalk of this
  integral scheme, the integral-case clause of def-sc-function-field. The component
  product construction is unnecessary in this integral case. The maps from sections
  and local rings into k(C) are `C.presheaf.germ` followed by `algebraMap`.
- Divisor D and its coefficients: `(D : C.Divisor)` is the existing finitely supported
  integer function on `closedPoints C`; `D P` is n_P, without any effectiveness assumption.
- O_C(D) and its section formula: `M := D.associatedModule C`, and
  `D.sectionModule C V`, are the recorded def-sc-divisor constructions. Their carrier
  consists of locally constant function-field-valued functions with zero-or-order
  bounds at every closed point. Integral nonempty opens are irreducible, so these
  locally constant functions are constant and give exactly the displayed subset of
  k(C). `Scheme.ord` in this definition is the normalized DVR order at closed curve
  points, as explained by the node's proof. On the empty open the carrier is the
  singleton empty function, hence the zero module.
- Closed point P and uniformizer t: `P : closedPoints C` and
  `t : C.presheaf.stalk P.val`, with the implication hypothesis
  `IsLocalRing.maximalIdeal (C.presheaf.stalk P.val) = Ideal.span {t}`.
  The closed stalk is a dimension-one DVR, so this is precisely the uniformizer
  condition and cannot admit t=0 or a unit.
- t^{-n_P} inside k(C): `c` is the integer power `(-D P)` of the image of t under
  `algebraMap (C.presheaf.stalk P.val) C.functionField`.
- Open neighbourhood U of P: `∃ U : C.Opens, P.val ∈ U ∧ ...`.
- For EVERY nonempty open V contained in U: the quantifiers are
  `∀ (V : C.Opens), V ≤ U → Nonempty V → ...`, including non-affine opens.
- The local section equality and the specified map a ↦ t^{-n_P}a: an equivalence
  `e : Γ(C,V) ≃ₗ[Γ(C,V)] D.sectionModule C V` whose value at EVERY x : V is c times
  the section's germ in k(C). Thus the equivalence is the actual multiplication map,
  giving equality of the indicated subsets, not an arbitrary abstract isomorphism.
  These maps automatically commute with restriction: target restrictions are
  pointwise, and the scalar germ maps commute with restrictions. The inverses also
  commute because the forward maps are bijective. Together with the unique map on
  the empty open, this is exactly the claimed O_U-module isomorphism.
- Invertibility: `M.IsInvertible`, the recorded `Scheme.Modules.IsInvertible` class.
- Stalk equality INSIDE k(C): the existential linear map
  `j : M.presheaf.stalk P.val →ₗ[C.presheaf.stalk P.val] C.functionField` is injective
  and satisfies `j (M.presheaf.germ V P.val hP s) = s.val ⟨P.val,hP⟩` for EVERY germ.
  These equations uniquely fix the canonical embedding induced by evaluation of the
  ambient constant-function section model. Its range is exactly
  `{g | ∃ a : C.presheaf.stalk P.val, g = c * algebraMap ... a}`.
  This specifies the fractional submodule t^{-n_P} O_{C,P}, not just an abstract
  linear equivalence of unrelated stalks.
- O_C(0)=O_C as subsheaves of k(C): for EVERY open V, including empty V,
  `((0 : C.Divisor).sectionModule C V : Set (V → C.functionField)) =
  Set.range (divisorScalarMap C V)`. The latter is precisely the structure sheaf's
  image under its pointwise germ embedding. Both sides restrict pointwise by the
  dependency's definitions, so equality on these section subsets gives the asserted
  equality as subsheaves, without equating differently bundled Lean carriers.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`, and its
  `IsConnectedCurve` specialization (the full class signatures and docstrings).
- `Sheaf.AlgebraicGeometry.FunctionField`: `Scheme.functionFieldOfComponents`
  was read; for the integral-case clause use Mathlib's `Scheme.functionField` and
  the generic-stalk algebra maps imported through the local-rings dependency.
- `Sheaf.AlgebraicGeometry.DivisorModule`: `Scheme.Divisor.associatedModule`,
  `Divisor.sectionModule`, `Divisor.sectionCondition`, `divisorScalarMap`, and
  `Divisor.moduleOfSmoothConnectedCurve` were read. The last wrapper has the same
  construction with the derived integral, regular and Noetherian instances;
  the statement uses its underlying associatedModule so the section types are explicit.
  Existing divisors themselves come from `WeilConjectures.AlgebraicGeometry.Curve.Divisor`.
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`:
  `Scheme.smooth_connected_curve_local_rings`, including its full existential
  integral-instance conclusion, all injection clauses, and normalized valuation clause.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, the local trivialization definition.
- `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`: existing module
  instance on `M.presheaf.stalk P`, used for the linear stalk embedding; its signature
  and `stalkLinearMapMk`/`germ_smul` were read. Stalks and germs are the usual
  Mathlib `TopCat.Presheaf.stalk` and `germ`.

Edge cases checked before drafting: zero, positive and negative coefficients give respectively
1, inverse powers and positive powers of t; zero rational functions satisfy the separate zero
case; no affineness or properness is imposed; characteristic is unrestricted; all neighbourhood
subopens are quantified; nonempty V is required exactly where the node requires it, while the
zero-divisor clause includes the empty open and both sides there are the unique empty function.
The empty scheme and dimension-zero schemes are already excluded by the source's connected
curve hypothesis. P may have coefficient zero and t is any uniformizer, not a chosen one.
The theorem's universes and variables are explicitly bound (`autoImplicit false`).

Searches for an existing statement:

- `msearch.py ... leanfinder "divisor module on smooth curve locally generated by inverse
  power of uniformizer"`: eight hits on elliptic-curve coordinate ideals, function
  fields, and power-series Weierstrass division; none is the curve divisor subsheaf statement.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Divisor, IsInvertible"`: zero hits,
  unknown identifier `AlgebraicGeometry.Scheme.Divisor` in the search service.
- `msearch.py ... grep "divisor.*(local|stalk)|associatedModule|sectionModule"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "invertible divisor sheaf on a smooth curve local uniformizer
  generator"`: service unavailable, Internal Server Error; no search verdict assigned.
- `rg` for `lem-sc-divisor-module-local|associatedModule|divisor.*[Ll]ocal` in the source
  `WeilConjectures` and project `lean/Sheaf`: the explicit associatedModule occurs in
  the recorded DivisorModule dependency, and other hits are unrelated associated-module
  constructions, Cartier-divisor and site divisor-local lemmas. No existing declaration
  gives this statement. A separate search for `module_local` in source, project modules,
  and `dag/lean_names_upstream.json` returned no declaration collision.
- Read Mathlib FunctionField's germ maps, the project's module stalk instance and full
  dependency modules/signatures. The local checkout has no `literature/stacks-project`;
  opened the actual source pages online: [0BE9](https://stacks.math.columbia.edu/tag/0BE9),
  [0AGA](https://stacks.math.columbia.edu/tag/0AGA), and
  [031T](https://stacks.math.columbia.edu/tag/031T). Their factorial-local Cartier-divisor
  construction and intersection-of-height-one-localizations support the node's proof.

No statement dispute or node fault found. All six supplied proof steps are preserved in the
Lean docstring; no proof has been supplied at stage 2. Independent second reading is left to
the designated second reader.

## Second reading by K1

Independent reading of the sandbox node and DivisorModuleLocal.lean, with all five
statement-dependency nodes and their source declarations open. No mathematical mismatch
was found; the Lean and node signature are retained unchanged. This reading adds only
this report section and fresh search records.

Object, hypothesis and conclusion checklist (each verdict: matches):

1. Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
2. Smooth connected curve C over k: `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`
   with `[IsConnectedCurve f] [Smooth f]`. Read Curve.lean's two class signatures:
   IsCurve extends separation, locally finite type and quasi-compactness;
   IsConnectedCurve adds ConnectedSpace and dimension exactly one. This is the node's
   nonempty connected curve, without adding properness, affineness or projectivity.
3. Derived integral and Noetherian scheme, generic point and field: the three `letI`
   clauses derive Noetherianity, regularity and integrality, rather than requiring extra
   hypotheses. Read the entire `smooth_connected_curve_local_rings` signature: its
   existential integral instance and its injection, nongeneric-point and DVR clauses
   are precisely those of the dependency. Mathlib `Scheme.functionField` is the stalk
   at `genericPoint C`, explicitly the integral-scheme clause of def-sc-function-field.
   Read FunctionField.lean: `stalkFunctionFieldAlgebra` is induced by stalkSpecializes;
   `algebraMap_germ_eq_germToFunctionField` identifies the composite section map with
   the canonical generic germ. Thus the maps used are the specified inclusions in k(C).
4. Divisor D with finitely many signed coefficients n_Q: `(D : C.Divisor)` and `D Q`.
   Read Curve/Divisor.lean: `Divisor` is `closedPoints C →₀ ℤ`, with no effectiveness
   condition or degree constraint.
5. The specified submodule O_C(D), including its section formula: `M :=
   D.associatedModule C`, `D.sectionModule C V`. Read DivisorModule.lean in full:
   sectionCondition is local constancy plus the separate zero-or-order inequality;
   sectionModule has exactly that carrier; modulePresheaf uses those sections and
   pointwise restrictions; associatedModule packages it with the named sheaf theorem.
   On nonempty integral opens every locally constant function is constant, giving the
   node's subset of k(C). The order is Mathlib Scheme.ord; its codimension-one formula
   uses Ring.ordFrac, the normalized DVR valuation here. The node's proof already
   explains this bridge by the length of successive uniformizer-power quotients.
   The smooth-connected-curve wrapper in the dependency returns this same construction;
   its integral instance is proof-irrelevant to the one chosen in this statement.
6. Closed point P and any uniformizer t in O_{C,P}: `∀ (P : closedPoints C)
   (t : C.presheaf.stalk P.val)`, followed by maximalIdeal = Ideal.span {t}.
   In the dependency's dimension-one DVR this means exactly a uniformizer, excluding
   zero and units; it does not restrict to a previously chosen uniformizer.
7. The rational scalar t^{-n_P}: `c := (algebraMap ... t) ^ (-D P)` uses integer powers
   in the actual function field, with the node's sign convention.
8. Neighbourhood U: `∃ U : C.Opens, P.val ∈ U ∧ ...`. It depends on P and t as required.
9. Every nonempty open V contained in U: `∀ (V : C.Opens), V ≤ U → Nonempty V → ...`.
   No affine-only or neighbourhood-of-P restriction is added to V.
10. Equality O_C(D)(V) = c O_C(V), with the displayed local isomorphism: the existential
    `e : Γ(C,V) ≃ₗ[Γ(C,V)] D.sectionModule C V` has pointwise value exactly c times
    the composite canonical germ of a. Its surjectivity gives precisely the section
    subset equality, and injectivity is the already-specified embedding of regular
    sections times nonzero c. This is equivalent to the node's equality, rather than
    an arbitrary abstract isomorphism. Pointwise restrictions and canonical germ
    compatibility force these maps to commute with restriction, giving O_U's module
    isomorphism; the empty-open component is unique.
11. Invertibility: `M.IsInvertible` resolves to `Scheme.Modules.IsInvertible`.
    Read Modules/Invertible.lean: exists_isoUnit requires every point to have a
    neighbourhood restricting to the structure sheaf. This is local freeness of rank
    one and entails quasi-coherence, exactly the dependency node's notion.
12. Fractional stalk inside k(C): `∃ j : M.presheaf.stalk P.val →ₗ[...] C.functionField`
    with Function.Injective, equality on every germ to `s.val ⟨P.val,hP⟩`, and range
    `{g | ∃ a : C.presheaf.stalk P.val, g = c * algebraMap ... a}`. Every stalk element
    has a germ representative, so the equations uniquely specify the canonical
    ambient-field inclusion. Read FlatPullbackStalk's module instance and germ_smul:
    the scalar ring is the actual structure-sheaf stalk. This gives the literal
    fractional submodule, without replacing it by an unrelated isomorphic stalk.
13. O_C(0) = O_C as subsheaves: equality of sectionModule's carrier with
    `Set.range (divisorScalarMap C V)` for every open V. The latter is the canonical
    pointwise image of regular sections by the dependency's definition. Both restrict
    pointwise, so sectionwise subset equality is the asserted subsheaf equality.

Source reading: this checkout lacks the Stacks .tex tree. Independently fetched and read
from the Stacks project's raw source the full statements and proofs at
`divisors.tex` labels lemma-local-rings-UFD-c1-bijective and
lemma-weil-divisor-is-cartier-UFD, and `algebra.tex` label
lemma-normal-domain-intersection-localizations-height-1. Cross-checked the tag pages
[0BE9](https://stacks.math.columbia.edu/tag/0BE9),
[0AGA](https://stacks.math.columbia.edu/tag/0AGA), and
[031T](https://stacks.math.columbia.edu/tag/031T).
The standing hypotheses are respectively locally Noetherian integral with factorial
local rings for surjectivity; locally Noetherian with a codimension-one integral divisor
and factorial stalks along it; and a Noetherian normal domain with fraction field.
The smooth connected curve supplies all of these properties. The source does not impose
properness or a characteristic restriction. The node's local calculation is the curve
specialization of these arguments, as its source record explicitly says.

Edge cases: the empty scheme and dimension-zero schemes are excluded by the node's
connected-curve hypothesis itself. No empty family hypothesis is present; the divisor
may have empty support. D=0 and n_P=0 give c=1; negative and positive n_P both use integer
powers. The zero rational function is included independently of ord's junk zero value.
Empty V is excluded only in the local section equality, as in the node, and is included
in the zero-divisor equality: both carriers consist of the unique empty function.
All nonempty V, including those omitting P, are covered. Characteristic is unrestricted.
The universe u is arbitrary; sharing it for the field and scheme is the source project's
standard scheme convention, and smaller field carriers can be universe-lifted without
changing any mathematical case. All variables and universes are explicit with autoImplicit
false. The conclusions follow P and t's binders, in the same order as the node; existence
of closed points and uniformizers prevents vacuity of the global clauses.

Independent searches (2026-10-11), using different conceptual words from the first worker:

- `msearch.py K1 lem-sc-divisor-module-local leanfinder "fractional ideal sheaf divisor
  stalk generated by uniformizer integer power"`: eight hits, namely FractionalIdeal.count
  and related Dedekind-domain factorization/valuation lemmas. These concern ring-level
  fractional ideals, not the sheaf, all-open local multiplication and canonical stalk
  statement here; no match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.ord"`: twelve hits in Mathlib
  OrderOfVanishing (ord, ord_mul, ord_add, le_ord_iff and related lemmas), not this statement.
- `msearch.py ... leansearch "sections of line bundle associated with divisor equal
  fractional ideal in function field"`: Internal Server Error, recorded unavailable;
  no negative search verdict inferred from the outage.
- Independent `rg` for fractional, uniformizer, module_local, sectionModule and
  associatedModule over source Curve/, Mathlib AlgebraicGeometry/, project
  lean/Sheaf/AlgebraicGeometry/ and dag/lean_names_upstream.json: divisor-module sections
  occur only in the recorded DivisorModule dependency. Source closed-point ideal
  invertibility and elliptic-curve fractional ideals are different statements; the
  project's associatedModule declarations concern another construction on sheafed
  spaces, not this divisor submodule. No existing declaration or name collision found.

No new definition node, dependency module or statement correction is present or needed.
No hollow definition or private copy was added. The sole theorem remains `by sorry`;
its docstring names the sources and blueprint id and follows all six node proof steps.
All four imports are used (explicit section model; derived integrality; invertibility;
module structure on stalks). No declaration has a Sheaf namespace prefix.

Validation: independent server compilation via scompile.py passed cleanly in 2.4 seconds,
with no errors or warnings. The node's lean.statement was checked against the unchanged
file signature. deliver2.py --no-push printed OK: preflight and compilation passed.
