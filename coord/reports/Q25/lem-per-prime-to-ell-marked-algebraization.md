## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToEllMarkedAlgebraization` states
`AlgebraicGeometry.exists_primeToEll_marked_algebraization`, with its only proof `sorry`.
It introduces no definitions, helper axioms, or dependency repairs. The mathematical
statement is unchanged. The statement-dependency list gains the already published nodes
`def-sbc-normal-dominant-galois`, `def-weil-pbc-g-ring`, and `def-sc-function-field`, for
normal schemes, regular ring maps, and the function field of an arbitrary integral scheme.
Their existing definitions are imported, not copied.

Source read directly: ILO PDF, Expose V 2.1.1--2.1.2 (printed pp. 64--65),
3.1.1--3.1.4 (printed p. 66), and the geometric assembly in the item's proof.
V 3.1.3 gives the completion at a closed point of the special fibre and exact inverse
images of each marking; V 3.1.4 supplies the equal-characteristic identity choice.
The additional normal-neighbourhood, regular-completion, and fibre-dimension clauses
are retained exactly as the node states and its ten-step proof explains.

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
- `Sheaf.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`.
- `Sheaf.RingTheory.GRing`: `RingHom.IsRegular`, `Algebra.IsGeometricallyRegular`.
- `Sheaf.AlgebraicGeometry.FunctionField`: its documented arbitrary integral-scheme
  clause uses Mathlib's `Scheme.functionField`. The canonical generic-stalk morphism
  is `Scheme.fromSpecFunctionField` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`; and
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`.

The module imports all currently recorded, available proof-dependency modules without
`public`, except those already public statement dependencies. The two algebraization
inputs have no recorded module at this reading, so no invented import was added.
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

Searches for reuse (2026-10-18 UTC):

- `msearch.py ... leanfinder "partial algebraization complete normal local ring finite
  extension prime to ell marked closed subset relative curve"`: eight hits, concerning
  Zariski's main theorem, good reduction, regular loci and universal factorizations;
  none states this algebraization result.
- `msearch.py ... loogle "IsAdicComplete, IsRegularLocalRing,
  AlgebraicGeometry.Scheme.functionField"`: zero hits for the combined query.
- `msearch.py ... leansearch "algebraization of a complete normal local ring as a
  relative curve preserving a closed subset"`: eight unrelated normalization and
  elliptic-curve hits; no exact statement.
- `msearch.py ... grep "algebraization|algebraisation|primeToEll|prime_to_ell"`:
  zero Mathlib hits.
- `rg -n "marked.algebraization|prime_to_ell|primeToEll"` in upstream
  `WeilConjectures`, and `grep -rn` for the exact node id there: no hits.
- `rg` in `lean/Sheaf` found the consumer's proof-plan reference in
  `UniformizationNodalQuotientReduction.lean`, not a statement of this result. Searches
  for normal schemes, excellent rings, regular maps and function fields located the
  dependency interfaces listed above, which were read before use.
- DAG definition-node inspection located the already recorded normal-scheme,
  geometric-regularity and function-field nodes. No new definition node is needed.

Validation: `scompile.py Q25 lem-per-prime-to-ell-marked-algebraization <module>`
compiled the final module in both sandbox and library modes without errors or warnings
(about three seconds per mode). All variables and the universe are explicit; the file
has no line over 100 characters. No statement dispute or source correction was needed.

## Second reading by Q25

This is the author's separate self-check, not a claim of independent review; the
maintainer supplies the independent reader, as required by the dispatcher brief.
I reopened the node and final declaration together and checked every hypothesis and
clause against the correspondence above. In particular I checked the two triangles
against the types of `fromSpecStalk` and `fromSpecFunctionField`, the order of the
contravariant Spec map, the exact equality of closed supports, both fibre dimension
clauses, and the literal equal-characteristic identity. I also checked that integrality
of the input is only duplicated instance data from its normality predicate, and that
regularity tests the ring map induced by `g` rather than a different map. The final
reading found no mismatch. The dependency list was expanded to cite three existing
notions used directly; no mathematical statement, definition, or proof was changed.
