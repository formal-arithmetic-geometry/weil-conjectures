## Worker report

Record the exact existing declaration
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` (branch `slopmaster2`).
No new module or declaration is needed. Only the item's `lean` field changes.
The current published module was also read using
`scompile.py --source WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`;
its theorem signature matches the local source verbatim.

The node and its current main-20261015 blueprint unit have the same statement.
The upstream declaration docstring explicitly names this unit and Stacks Tag 0EYU.
Its surrounding module documents the negative-degree, filtered-torsion,
etale-local affine-space and universal relative-dimension-one induction argument.
This is a stage-2 statement binding; the recorded upstream proof still rests on
postponed upstream lemmas, as already recorded in the item's `lean_audit`.
No claim of an axiom-free completed proof is made.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Existing Lean |
| --- | --- |
| Four arbitrary schemes X, S, T, Y | `{X S T Y : Scheme.{u}}` in the explicit variable declaration |
| f : X → S, g : T → S, e : Y → T, h : Y → X | `(p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)`; p is the node's f |
| Square Cartesian | `(sq : IsPullback e h g p)`; e followed by g equals h followed by p |
| f smooth | `[Smooth p]` |
| g quasi-compact | `[QuasiCompact g]` |
| g quasi-separated | `[QuasiSeparated g]` |
| Arbitrary commutative ring Λ | `(Λ : Type (u + 1)) [CommRing Λ]` in the explicit variable declaration |
| Every degree q | `(q : ℤ)`, including negative degrees |
| Any sheaf of Λ-modules on T_et | `(F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))` |
| Every geometric-stalk element killed by a positive globally invertible integer | `[Scheme.IsTorsionSheafOfInvertibleOrder S F]` |
| The stated canonical arrow is an isomorphism | `IsIso (Etale.baseChangeHomologyMap Λ sq q F)` |

The torsion class was opened in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`.
Its field is
`exists_isUnit_nsmul_eq_zero (Ω : Type u) [Field Ω] [IsSepClosed Ω]
(s : Spec (.of Ω) ⟶ T) (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0`.
Thus the integer depends on the stalk element, and invertibility is on S globally.
There is no uniform annihilator or neighbourhood-only replacement.
The separably closed geometric points are the project's recorded geometric-stalk
encoding. The coefficients and module category have the required u+1 size,
with geometric points in u; no extra universe equality is imposed.

Dependency declarations used and read:

- `sk-def-bc`: `Etale.BaseChangeProperty`, `Etale.baseChangeHomologyMap`,
  `Etale.UniversalBaseChangeProperty` in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`.
  Read the full signatures, definitions and docstrings. The theorem uses precisely
  its recorded `baseChangeHomologyMap`. The map applies the degree-q homology functor
  to `Etale.baseChange`, after placing F in degree zero. Its source and target are
  the defined `Etale.baseChangeSourceFunctor` and `Etale.baseChangeTargetFunctor`.
  Exact module inverse image identifies these with the two classical sheaves.
  In `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`, the actual
  derived arrow is the composite of the unit, canonical square exchange and counit.
- `sk-def-smooth`: read the full recorded module
  `Sheaf.AlgebraicGeometry.AllowedTorsion`, including
  `AlgebraicGeometry.allowedTorsion_colimit_map_isIso` and its docstring.
  It reuses `Scheme.IsTorsionSheafOfInvertibleOrder` from the upstream torsion module;
  the theorem uses that same class. Its extra declarations construct the divisibility
  diagram and cocone and state its colimit isomorphism and counterexample.
  No new definition of allowed torsion is necessary here.
  Smoothness is the upstream/Mathlib `AlgebraicGeometry.Smooth`, whose full class
  signature and affine-open definition were read in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

Edge cases checked against the signatures and constructions:

- q < 0 remains included; the upstream proof handles it by vanishing.
- q = 0 remains included, with no positive-degree binder.
- The zero sheaf and zero coefficient ring remain included: each zero stalk element
  is killed by 1, a positive global unit. No nontriviality assumption is present.
- Empty schemes remain included; no `Nonempty` or point-selection hypothesis occurs.
- Identity morphisms and arbitrary Cartesian representatives remain included;
  the result is not restricted to a chosen categorical pullback object.
- No characteristic is excluded except what the elementwise positive invertible-order
  hypothesis actually requires. An annihilator 0 cannot satisfy `0 < n`.
- The source need not be affine, nor the base Noetherian or a field; qcqs is imposed
  only on g, as in the node. Smoothness has its ordinary local definition.
- Unbounded elementwise torsion is included; no fixed n is an input to the theorem.

Searches performed (through msearch.py with group Q88 and this item):

1. LeanFinder query: "Smooth base change for higher direct images of torsion etale
   module sheaves with globally invertible orders along a smooth morphism".
   Eight hits about etale base change and Kahler differentials, none this theorem.
2. Loogle query: `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`.
   One hit: `AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`;
   normalization, not higher direct images.
3. Mathlib grep: `baseChangeHomologyMap|smooth.base.change|higherDirectImage`.
   Four hits in Normalization and Smooth/IntegralClosure, no etale cohomology theorem.
4. `grep -rn "sk-thm-smooth-base-change"` in the upstream WeilConjectures tree
   found the theorem's blueprint docstring in SmoothBaseChange/Theorem.lean.
5. `rg -n 'IsTorsionSheafOfInvertibleOrder|isIso_baseChangeHomologyMap_of_smooth'`
   in the upstream WeilConjectures and side Sheaf trees found the upstream theorem,
   its canonical torsion class, and the side AllowedTorsion module reusing that class.
6. `rg -n 'isIso_baseChangeHomologyMap_of_smooth' dag/lean_names_upstream.json`
   had no hit; the full source and published source, rather than that stale index,
   establish the exact existing match.

No repair note exists for this item. No statement correction, dependency repair,
new node, new sorry, or disputed statement is needed.

Validation: deliver2.py --no-push checks the existing declaration with a real
scompile.py import/#check probe and runs server preflight. The independent second
reading and final delivery belong to the second reader.

## Second reading by Q88

I independently read the sandbox node and its `lean.statement`, the unchanged
main-20261015 blueprint unit, Stacks `etale-cohomology.tex` Tag 0EYU
(`theorem-smooth-base-change`, including the section introduction and the second
proof), and the complete upstream `SmoothBaseChange/Theorem.lean`. I also read
its current published source with `scompile.py --source`; the signature is
unchanged. The section imposes no standing Noetherian, affineness, field, or
finite-type hypothesis. Stacks states the abelian-sheaf result; the blueprint
explicitly states its constant commutative-ring module version. The recorded
declaration is exactly that version, without coefficient flatness.

My object/hypothesis/conclusion inventory, including surrounding variables:

| Node item | Actual Lean rendering and verdict |
| --- | --- |
| Arbitrary schemes X, S, T, Y | `{X S T Y : Scheme.{u}}`. Exact; no scheme property assumed. |
| f : X → S, g : T → S, e : Y → T, h : Y → X | `(p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)`. Exact, with p denoting f. |
| The square is Cartesian | `(sq : IsPullback e h g p)`. Exact orientation: `e ≫ g = h ≫ p`, with the pullback universal property. |
| f smooth | `[Smooth p]`. Exact ordinary scheme smoothness. Mathlib's `Morphisms/Smooth.lean` defines it through smooth ring maps on affine opens. No fixed relative dimension. |
| g quasi-compact | `[QuasiCompact g]`. Exact, on g only. |
| g quasi-separated | `[QuasiSeparated g]`. Exact, on g only. |
| Arbitrary commutative coefficient ring Λ | `(Λ : Type (u + 1)) [CommRing Λ]`. Exact under the recorded module-sheaf size convention, with no field, finiteness, nontriviality, or characteristic assumption. |
| Every degree q | `(q : ℤ)`. Exact, including zero and negative degrees. |
| Every sheaf F of Λ-modules on T_et | `(F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Exact recorded small-etale module-sheaf category. |
| Each geometric-stalk element killed by a positive integer invertible on S | `[Scheme.IsTorsionSheafOfInvertibleOrder S F]`. Its field quantifies over `(Ω : Type u) [Field Ω] [IsSepClosed Ω]`, `s : Spec (.of Ω) ⟶ T`, and each stalk element x, returning `∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0`. Exact global invertibility and elementwise annihilators. |
| The arrow f⁻¹ R^q g_* F → R^q h_* e⁻¹ F is an isomorphism | `IsIso (Etale.baseChangeHomologyMap Λ sq q F)`. Exact, including the specified canonical arrow. |

For H3/H4 I opened both dependency records and their actual sources.
`sk-def-bc` records `Etale.BaseChangeProperty`, `Etale.baseChangeHomologyMap`,
and `Etale.UniversalBaseChangeProperty` in `SmoothBaseChange/Defs.lean`.
I read their signatures and bodies, including `baseChangeSourceFunctor`,
`baseChangeTargetFunctor`, and `baseChangeHomologyNatTrans`. The arrow is the
homology of `Etale.baseChange` at F[0]. In `BaseChangeTheorems/MorphismDefs.lean`
I checked the construction: the derived-adjunction unit, the square comparison
assembled from inverse-image composition, and the derived-adjunction counit.
Thus its objects are H^q(p^* Rg_* F[0]) and H^q(Rh_* e^* F[0]), canonically the
displayed classical sheaves since module inverse image is exact. The node
explicitly uses this derived formulation. The bounded-below classical
comparison isomorphisms mentioned as unavailable in the upstream module
comment are not extra hypotheses or arbitrary data in this statement.

`sk-def-smooth` records `Sheaf.AlgebraicGeometry.AllowedTorsion`. I read that
complete module and the upstream torsion class it imports. It reuses
`Scheme.IsTorsionSheafOfInvertibleOrder`, rather than another meaning of torsion.
Its main theorem supplies the divisibility-indexed filtered union, and its
kernel diagram, cocone and counterexample have real constructions. Those
additional properties are proof inputs, not extra hypotheses here. The actual
theorem uses the same class and the same Mathlib `Smooth`. Neither dependency
needs repair. No new node or dependency module is delivered.

Edge cases: empty schemes and the zero sheaf are included, with no point
existence or nonempty hypothesis. The zero coefficient ring is permitted by
`CommRing`; its zero stalk elements are killed by the allowed integer 1.
Both q = 0 and q < 0 are included by the integer quantifier. An annihilator
0 fails `0 < n`; n = 1 is permitted and forces the element to be zero. There
is no residue-characteristic restriction beyond the given invertibility
condition, no uniform exponent, and no affine or Noetherian base assumption.
Identity squares and every Cartesian representative are included: Y is
arbitrary with sq, rather than a chosen pullback object. No index set is an
input here; the allowed-torsion index in the dependency contains 1. Universes
are explicitly bound by `universe u`, with scheme/geometric-point size u and
coefficient/module size u+1, exactly as in the recorded dependencies. There
is no independent test-object universe making a hypothesis vacuous, nor any
new equality of universes. Quantification over separably closed fields is
the dependencies' geometric-point encoding; algebraic closures already give
a conservative family, so larger presentations of geometric points do not
introduce another condition on the sheaf.

Independent searches, using wording different from the worker's:

1. `msearch.py ... leanfinder 'Inverse image along smooth scheme morphism
   commutes with derived pushforward of etale torsion coefficients'`: eight
   hits about ordinary scheme-module pushforward composition and etale
   morphism properties, none this theorem.
2. `msearch.py ... loogle '"base change"'`: no hits.
3. `msearch.py ... grep
   'inverseImage.*higherDirectImage|higherDirectImage.*inverseImage|isIso_baseChangeHomologyMap_of_smooth'`:
   no Mathlib hits. Direct `rg` of Mathlib algebraic geometry, upstream
   `WeilConjectures/SixFunctors`, and this project's `lean/Sheaf` for
   smooth/base-change phrases and the theorem name found the exact upstream
   theorem. Mathlib's normalization under smooth base change concerns
   another object. The project's derived smooth-base-change statements
   concern complexes (I opened the bounded-below module and target signature),
   and do not replace this degreewise module-sheaf theorem. The upstream-name
   index lacks the exact name; the opened local and published sources supply
   the binding evidence.

H5/H6/H8/H9: this delivery adds no Lean declaration, data, proof, or sorry.
It reuses an existing theorem, whose blueprint docstring and Stacks attribute
identify this node and Tag 0EYU. The complete module explains negative-degree
vanishing, filtered torsion and quotient coefficients, etale-local affine-space
reduction, composition, and universal relative-dimension-one induction. The
node's fuller seven-step proof remains unchanged. The upstream proof's
reachable sorries remain recorded in `lean_audit`; an existing stage-2 binding
does not certify a completed proof. All variables and the sole universe are
explicitly bound. There is no repair note, `statement_change`, or disputed
statement to audit.

No mismatch was found; no statement or dependency was changed. I retained the
existing binding and appended this independent reading. A literal comparison
verified that `lean.statement` is verbatim the theorem signature, that the
natural-language statement is verbatim the blueprint unit, and that the
sandbox node differs from the repository node only in its `lean` record.
The required delivery dry run compiles an import/`#check @` probe through
`scompile.py` and runs server preflight; there are no delivered Lean files
requiring separate compilation.

Validation completed: `deliver2.py Q88 sk-thm-smooth-base-change --no-push`
reported `OK (dry run): commit e49dab89bc passes the preflight and compiles;
nothing pushed`. The compiled existing-declaration probe was clean. Only the
item's node and this report were staged by the wrapper.
