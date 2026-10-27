## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToEllMarkedAlgebraization` states
`AlgebraicGeometry.exists_primeToEll_marked_algebraization`. Its sole proof is `sorry`;
there are no new definitions, helper axioms, dependency repairs, or changes to the
mathematical statement. The node copy changes only in `lean`.

This is a fresh statement delivery after the previously reviewed module was deleted
as dead code, as recorded in `lean_removed`. I read the archived Q25 report and the
current node, and reconstructed the statement using the current dependency modules.
The archived report supplied a correspondence checklist; every clause below was
checked against the final file and current declaration signatures. The former Sheaf
normal-scheme, G-ring, and function-field modules now have upstream owners, and those
WeilConjectures modules are imported here. The newly recorded complete-local-excellence
proof dependency is also imported.

Source read directly with `pdftotext -layout` on the repository's ILO PDF:
Expose V 2.1.1--2.1.2, printed pp. 64--65, and 3.1.1--3.1.4, printed p. 66.
V 3.1.3 gives a completion at a closed point of the special fibre and exact inverse
images of the markings. V 3.1.4 gives the equal-characteristic identity choice.
The normal affine neighbourhood, regular completion map, and dimension clauses are
those of the node and its expanded ten-step geometric proof. No source correction
or statement dispute was required.

Hypothesis-by-hypothesis correspondence:

- The prime is `(ell : ℕ) (hEll : ell.Prime)`.
- `X : Scheme.{u}` is the same input scheme. `[IsAffine X]` and
  `[IsLocalRing Γ(X, ⊤)]` express a local scheme, namely the spectrum of its local
  coordinate ring. This does not impose a smaller class of local schemes.
- `[IsNoetherian X]` is Noetherianity. Maximal-ideal completion is
  `[IsAdicComplete (IsLocalRing.maximalIdeal Γ(X, ⊤)) Γ(X, ⊤)]`.
- `hNormal : IsNormalScheme X` is normality. The separately supplied `[IsIntegral X]`
  is precisely the first conjunct of `hNormal`, repeated as instance data so Lean can
  form `X.functionField`. It adds no mathematical hypothesis: any input satisfying
  `hNormal` supplies this instance by `hNormal.1`. A nonempty normal local scheme is
  integral, so the published normal predicate's integral clause causes no restriction.
- `d : ℕ`, `hd : 2 ≤ d`, and `hDim` express dimension exactly `d ≥ 2`.
- `hInv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x)` is invertibility on `X`.
- `Z : Set X`, `hZ : IsClosed Z`, and `hRare : IsNowhereDense Z` are exactly the
  nowhere dense closed marking. No chosen ideal or nonempty marking is required.

Conclusion-by-conclusion correspondence:

- The three existential schemes are `Xplus`, `Y₀`, and `W`. The existential instance
  binders give `Xplus` affine, integral, Noetherian, local and maximal-ideal-adically
  complete, and `IsNormalScheme Xplus` gives the required normality. Affineness is
  part of the meaning of a local scheme.
- The existential map `p : Xplus ⟶ X` satisfies `IsFinite p ∧ Surjective p`.
- The existential algebra `Algebra X.functionField Xplus.functionField` is constrained
  by the triangle
  `Spec.map (CommRingCat.ofHom (algebraMap X.functionField Xplus.functionField)) ≫
  X.fromSpecFunctionField = Xplus.fromSpecFunctionField ≫ p`.
  Hence it is the function-field map of this `p`, rather than an unrelated algebra.
  `Nat.Coprime (Module.finrank X.functionField Xplus.functionField) ell` says its
  degree is prime to ell. This also forces finite degree: an infinite-dimensional
  field extension has finrank zero, and zero is not coprime to the prime ell.
- `Y₀` has the same affine/local/completeness/Noetherian instance binders;
  `IsRegularScheme Y₀`, `IsExcellent Γ(Y₀, ⊤)`, and
  `topologicalKrullDim Y₀ = ((d - 1 : ℕ) : WithBot ℕ∞)` give every remaining base
  condition. Integrality in its existential instance data is a consequence of being
  regular local, not a restriction on the permissible bases.
- `W` is affine, integral and Noetherian by its existential instance binders, excellent
  by `IsExcellent Γ(W, ⊤)`, and normal by `IsNormalScheme W`. For an affine scheme,
  excellence of its coordinate ring is exactly excellence of the scheme.
- `f₀ : W ⟶ Y₀` satisfies `IsDominant f₀`, `LocallyOfFiniteType f₀`, and
  `QuasiCompact f₀`; the last two together are the dependency node's finite-type
  condition. Every fibre is the actual scheme `f₀.fiber y`, with topological Krull
  dimension at most one. Its fibre at `genericPoint Y₀` has dimension exactly one.
- `IsClosed ({w} : Set W)` and `IsClosed ({f₀ w} : Set Y₀)` say that `w` is a closed
  point above the unique closed point of the local base. Specifying closedness on
  both schemes does not require a stronger condition on the residue extension.
- `Z_W : Set W` satisfies `IsClosed Z_W ∧ IsNowhereDense Z_W`.
- `g : Xplus ⟶ W` has an existential isomorphism `e` onto the spectrum of
  `AdicCompletion (IsLocalRing.maximalIdeal (W.presheaf.stalk w))
  (W.presheaf.stalk w)`. Its equality with `e.hom`, followed by Spec of the canonical
  completion algebra map, followed by `W.fromSpecStalk w`, identifies the actual
  completion morphism at `w`. No arbitrary map is substituted for this construction.
- `p ⁻¹' Z = g ⁻¹' Z_W` is the exact set-theoretic equality in the node.
- `RingHom.IsRegular (g.appTop).hom` states regularity of `g`, since its source and
  target are affine. The published predicate includes flatness and Noetherian
  geometrically regular fibres. Its test over finite purely inseparable extensions
  agrees with regularity over all finite residue-field extensions by Stacks 0381;
  this is the convention explicitly recorded in `def-weil-pbc-g-ring`.
- The two universal stalk-unit conditions express invertibility of ell on `Y₀` and `W`.
- Equality of `ringChar Γ(X, ⊤)` and the characteristic of its local residue field
  expresses equal characteristic. Its implication concludes
  `∃ h : Xplus = X, p = eqToHom h`: the selected map can literally be the identity,
  retaining all other clauses for that same selected algebraization.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity uses
  the existing `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, defined using the published
  `IsQuasiExcellent` and `IsUniversallyCatenary`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  namely `IsLocallyNoetherian ∧ IsRegular`, with the upstream stalkwise `IsRegular`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and the
  dependency's `QuasiCompact` condition (its Mathlib module is imported transitively).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`;
  the canonical ring map and ring structure come from AdicCompletion.Algebra.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, present via
  the affine regular ring map's flatness condition.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular`, `Algebra.IsGeometricallyRegular`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: its documented arbitrary integral-scheme
  clause uses Mathlib's `Scheme.functionField`. The canonical generic-stalk morphism
  is `Scheme.fromSpecFunctionField` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`; and
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`.

The module imports all currently recorded, available proof-dependency modules without
`public`, except those already public statement dependencies. The two algebraization
inputs and excellent-normalization preparation have no recorded Lean module at this
reading, so no invented import was added. They are proof dependencies, rather than
notions needed to type this statement.
The docstring gives all ten proof steps and their role, including kernel localization,
normality descent, the dimension formula, and the nowhere-density argument.

Edge cases checked: `Z = ∅` is allowed and is not replaced by a nonempty effective
marking; the entire nonempty scheme cannot be a nowhere dense marking. Empty special
fibres are allowed in the dimension bound because `topologicalKrullDim ∅ = ⊥`.
The generic fibre must have dimension exactly one and is therefore nonempty. The case
`d = 2` gives base dimension one, with no natural-subtraction ambiguity. Both
characteristic zero and positive equal characteristic satisfy the identity clause;
mixed characteristic does not trigger it. The unit condition excludes precisely the
residue characteristic ell. Integral/local conditions exclude the zero ring and empty
local schemes, as in the source. All schemes use the same arbitrary universe `u`, and
geometric regularity retains the published max-universe field-extension test.

Searches for reuse (2026-10-24 UTC):

- `msearch.py ... leanfinder "Partial algebraization of a complete normal local scheme
  preserving a closed subset after a finite extension of degree prime to ell"`:
  eight hits, concerning normalization, Zariski's main theorem, and finiteness of
  global sections; none states the item.
- `msearch.py ... loogle "IsAdicComplete, IsLocalRing, AdicCompletion"`:
  two hits, `AdicCompletion.instIsAdicCompleteMaximalIdeal` and
  `AdicCompletion.isAdicComplete_of_fg`; these are completeness instances, not the item.
- `msearch.py ... leansearch "A complete normal local scheme is a completion of a
  relative curve after finite cover prime to ell preserving a closed subset"`:
  eight hits for local Noetherianity and normalization, no exact statement.
- `msearch.py ... grep "algebraization|marked_algebraization|primeToEll"`:
  zero Mathlib hits.
- `rg -n "primeToEll_marked_algebraization|marked.algebraization|prime_to_ell"`
  over `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`:
  only unrelated condensed prime-to-ell acyclicity declarations were found.
- Exact-node-id search in `lean/WeilConjectures`: no hits. Broader algebraization
  searches found proper formal algebraization, torsion-controlled algebraization,
  and punctured power-series formal-hom results, with different objects and conclusions.
- The existing dependency nodes already supply all notions, including the normal
  scheme predicate, excellent ring predicate, regular map, and integral function field.
  Their recorded declarations and docstrings were read in the current source tree.
  No new node is needed.

Validation: `scompile.py Q09 lem-per-prime-to-ell-marked-algebraization <module>`
checks this file separately in sandbox and library modes against the published live
build. The first compile identified one docstring whitespace warning, which was fixed.
The final compile was clean in both modes (2.1 s sandbox, 2.0 s library).
The prescribed `deliver2.py ... --no-push` printed OK: its server preflight and
per-file compile passed.
All variables and universe `u` are explicitly bound with `autoImplicit` disabled.
The node's `lean.statement` is extracted verbatim from the theorem signature.
All source lines are at most 100 characters. Only sandbox files were written, and
only the authorized scompile/deliver2 wrappers perform compiler or Git bookkeeping.

## Second reading by Q09

The dispatcher forbids starting another agent and assigns independent review to the
maintainer. This is therefore an author's separate final reading, not a claim of an
independent review. I reopened the node and final theorem and checked each hypothesis
and conclusion against the correspondence above. The completion triangle uses the
canonical map from the actual stalk at `w`; the generic-point triangle pins the algebra
structure to `p`; the marking equality is exact; the generic fibre has dimension exactly
one while empty other fibres are allowed; both scheme-unit clauses and the literal
identity clause in equal characteristic are retained. The only repair after compilation
was docstring whitespace. No mathematical mismatch, new definition, or statement
change was found. The maintainer's independent reader remains the delivery reviewer.
