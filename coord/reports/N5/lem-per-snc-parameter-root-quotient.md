## Worker report

Item: lem-per-snc-parameter-root-quotient. Stage 2: one theorem with `sorry`, two
fully specified helper structures, no proved theorem and no hollow definition.
Module: `Sheaf.AlgebraicGeometry.SNCParameterRootQuotient`.
Main declaration: `AlgebraicGeometry.exists_sncParameterRootQuotient`.

I read the item's statement, source, all ten proof steps, all eleven original
statement-dependency records and their declarations. I also read ILO Expose IX
Proposition 2.1 and its proof on printed pp.133--134 (PDF pp.139--140), including
IX 2.2, directly from the local PDF. The source first reduces etale locally to a
strict local regular parameter chart, writes the root invariant-ring model, and
uses Abhyankar for essential surjectivity. The node's proof makes the finite-data
descent back to pointed affine etale neighbourhoods explicit. That is the proof
plan in the theorem docstring.

The helper structures belong to this item's own conclusion: they spell out the
input pointed parameter neighbourhood and the entire output quotient model.
They introduce no alternative normalization, boundary, regularity, torsor,
parameter-system, polynomial quotient, or invariant-ring definition.
`SNCParameterNeighborhood` permits the prescribed chart still to contain other
boundary components away from its selected point: its equation and component
conditions are required only after restriction to an open `D` containing that
point. `SNCParameterRootQuotient` makes those conditions global on the refined
chart, so that the unwanted components have actually been removed.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Integral regular Noetherian Y | `(Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y] (_hY : IsRegularScheme Y)` |
| Strict normal crossings boundary T | `(T : Y.IdealSheafData) (_hT : IsStrictNormalCrossingsBoundary T)` |
| V is the boundary complement | `Scheme.Opens.toScheme T.support.compl`; its immersion is `Scheme.Opens.ι T.support.compl` |
| Finite group G; n is its order | `(G : Type v) [Group G] [Finite G]`, with `n` everywhere instantiated as `Nat.card G` |
| n invertible on Y | `_hn : ∀ x : Y, IsUnit (Nat.card G : Y.presheaf.stalk x)` |
| Connected finite etale G-torsor | `P : Scheme.GaloisCoverAction G ...` and `[ConnectedSpace P.Z]`; the recorded action already includes finiteness, etaleness, surjectivity, simple transitivity on geometric fibres, and the quotient property |
| k(V')/k(Y) is the field extension induced by the cover | The conclusion existentially supplies `IsIntegral P.Z` and `Algebra Y.functionField P.Z.functionField`; `Y.fromSpecOfAlgebraFunctionField P.Z.functionField = P.Z.fromSpecFunctionField ≫ P.π ≫ Scheme.Opens.ι T.support.compl` fixes the structural field map |
| Finite normalization b:Z->Y | `IsFinite (Y.fromNormalizationIn P.Z.functionField)` is the premise of the conditional conclusion; Z and b are precisely the recorded `normalizationIn` and `fromNormalizationIn` |
| Geometric points z above y | `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, `y`, `z`, and `z ≫ Y.fromNormalizationIn ... = y` |
| Existence of a pointed affine etale neighbourhood U=Spec A | `Nonempty (SNCParameterRootQuotient ...)`; its inherited fields are `A`, `u`, `etale`, `point`, and `point_base` |
| A regular Noetherian | Inherited `[noetherian : IsNoetherianRing A]` and `regular : IsRegularRing A` |
| Finitely many t_i, allowing r=0 | `t : List A`; indices are `Fin t.length`, so r is `t.length` |
| Equations of precisely the components through the selected point | `equations` identifies the pulled-back boundary ideal with the principal product ideal; `components` makes each individual zero subscheme integral; `distinct_components` distinguishes their supports; `vanishing` places all selected equations at the marked prime |
| Parameters lie in the local maximal ideal and extend to regular parameters | `vanishing` is membership in the selected prime of A, equivalently membership in the maximal ideal of its local ring; `parameters` maps the list by the actual `StructureSheaf.toStalk` homomorphism and requires it to be a sublist of a full `IsLocalRing.IsRegularSystemOfParameters` list |
| V x_Y U = D(product t_i) | `complement : u ⁻¹ᵁ T.support.compl = PrimeSpectrum.basicOpen t.prod`; the two opens define the asserted canonical open subscheme |
| zeta is a unit, zeta^n=1, all nontrivial differences units | `zeta : Aˣ`, `zeta_pow`, and `zeta_difference`, with both bounds `1 ≤ a` and `a < n` |
| B is the displayed polynomial quotient | `Algebra.ParameterRoot.Ring t.get n`, definitionally `Algebra.pthRootAlgebra n t.length A t.get` |
| H is a subgroup of (Z/nZ)^r | `H : AddSubgroup (Fin t.length → ZMod n)` |
| H fixes A and rotates each root by zeta^{h_i} | `action : H →+ Additive (B ≃ₐ[A] B)` supplies the action laws and fixes coefficients; `action_root` specifies the image of every canonical quotient variable using the ZMod representative `.val` |
| The action is the canonical indicated action | Every algebra homomorphism out of this quotient is determined by its coefficient and variable values (`Algebra.ParameterRoot.hom_ext`); consequently the displayed action has no free choice once H and zeta are fixed |
| B^H consists of elements fixed by every h | The actual subtype `↥(⨅ h : H, AlgHom.equalizer (action h).toMul.toAlgHom (AlgHom.id A _))`; Mathlib's equalizer has carrier `{b | action h b = b}`, and the intersection imposes it for every h |
| Pointed affine etale W->Z, and W Noetherian | `W`, `affine`, `noetherian_W`, `w`, `etale_W`, `lift`, `lift_z` |
| W->U over b, preserving the selected points | `to_base`, `square`, and `lift_base` |
| Isomorphism W = Spec(B^H) over U | `iso` and `iso_over`; the latter uses the actual canonical coefficient map to the equalizer-intersection subalgebra |
| Refines any prescribed pointed etale parameter neighbourhood | The second conjunct quantifies over every `Q : SNCParameterNeighborhood T y`; its result supplies M, a coordinate-ring map `f : Q.A ⟶ M.A`, an etale `Spec.map f`, and `Spec.map f ≫ Q.u = M.u` |
| Preserves the point and the prescribed equations | `M.point ≫ Spec.map f = Q.point` and the literal ordered-list equality `M.t = Q.t.map f.hom` |
| Empty boundary: r=0, B=A, H=0 | `empty_boundary : T.support = ⊥ → t = []` forces r=0. The existing `Algebra.ParameterRoot.emptyEquiv` identifies this zero-variable quotient with A as an A-algebra. `Fin 0 → ZMod n` is the zero group, so its only additive subgroup is the zero subgroup |

The existential integrality and field-algebra structures are notation-enabling
conclusions, not extra hypotheses: a connected finite etale cover of this regular
base is integral. The generic-point equation pins the field extension, rather than
allowing an unrelated algebra structure or an arbitrary comparison map. This is
the same dependent-existential convention used in the published
`AlgebraicGeometry.normalizationIn_functionField_extends_cover`, but that theorem
is not assumed here (it has a field-base hypothesis that this node does not have).
No field-base, excellence, separatedness, local connectedness, log structure on Z,
monoid chart for b, prescribed action on the cover, or ramification-degree equality
was added. The two output structures are data with explicit properties; only the
existence theorem has a postponed proof.

Statement dependency declarations used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  reached through the recorded boundary module.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`:
  `AlgebraicGeometry.Scheme.GaloisCoverAction`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalizationIn`, `fromNormalizationIn`, and
  `fromSpecOfAlgebraFunctionField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with geometric points
  expressed inline as morphisms from `Spec (.of Ω)` per the dependency convention.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme.ΓSpecIso`.
- Added existing landed definition dependency `def-sfb-parameter-root-algebra`:
  `WeilConjectures.RingTheory.PthRootAlgebraLocal`, `Algebra.pthRootAlgebra`.
  The public import `Sheaf.RingTheory.ParameterRootAlgebra` exposes its exact
  abbreviation `Algebra.ParameterRoot.Ring` and quotient variable `root`.

All recorded proof dependencies that have modules or Mathlib matches are imported
privately. The three not-yet-stated geometric/root inputs
`lem-per-regular-boundary-divisorial-chart`, `lem-per-snc-root-algebra-structure`,
and `lem-per-snc-root-punctured-torsor-splitting` have no recorded module to import;
their statements are proof inputs rather than unstated notions in this signature.
No dependency was replaced and no new node is required.

Edge cases checked before writing and again while reading the final signature:

- Empty boundary, and a point outside a nonempty boundary: zero branches, the empty
  product 1, the full basic open, the zero-variable root quotient, trivial H.
- Trivial G: `Nat.card G = 1`, only the exponent equation for zeta remains, and
  the strict-difference range is empty. No condition `n > 1` occurs.
- Finite groups have positive order, so the artificial zero-exponent root algebra
  case is never imposed on this torsor theorem, although the reused definition
  itself supports exponent zero.
- Nonclosed marked point: its prime in A need not be maximal; the maximal-ideal
  assertion belongs to its stalk. The signature uses the actual stalk, avoiding
  an accidental closed-point assumption on Spec A.
- The prescribed chart may contain other boundary components. Its local open D
  permits them; the output has the global product equation after their removal.
- The torsor need not remain connected after strict localization. H can have any
  index compatible with the selected branch; no local degree n is asserted.
- No field-base or excellence assumption, no positive-dimensional hypothesis,
  and no nonempty-boundary hypothesis occurs. An integral Y is already nonempty.
- Scheme/geometric-point sizes follow the recorded `def-weil-geometric-point`
  convention at universe u; G has its independent universe v.

Searches for an existing exact statement (all on 2026-10-24):

- `msearch.py ... leanfinder "Etale locally a tame finite torsor over a normal
  crossings complement is the invariant ring of a simultaneous parameter root
  algebra"`: eight unrelated standard-etale/local-algebra results; no exact theorem.
- `msearch.py ... loogle "MulSemiringAction, FixedPoints, MvPolynomial"`: no hits;
  the service reported unknown identifier FixedPoints. Direct source search then
  found Mathlib's fixed-point subalgebras and `AlgHom.equalizer`; the latter is
  used directly, with no substitute invariant-subalgebra definition.
- `msearch.py ... grep "fixedSubalgebra|invariantSubring|invariants|rotation"
  RingTheory`: ten unrelated isotypic/Frobenius results, no root quotient theorem.
- `msearch.py ... leansearch "simultaneous root algebra invariant ring etale local
  normalization torsor"`: eight localization/etale-descent results, no exact theorem.
- `rg` in the project's `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib found the
  reusable `pthRootAlgebra` and `Algebra.ParameterRoot` API, the normal crossings
  parameter criterion and finite-root extension results, but no parameter-root
  invariant-ring quotient statement. The existing root definition node was found
  in `dag/nodes`; `blueprint_refs.py search "parameter root"` found no blueprint
  node with those literal words. No definition node was duplicated.
- `rg` and `grep -rn` for this item's id in upstream Lean found no declaration.
  `SNCParameterNeighborhood`, `SNCParameterRootQuotient`, and
  `exists_sncParameterRootQuotient` have no prior declaration in the searched
  upstream/project files or the upstream declaration index.

No STATEMENT-DISPUTED flag, statement correction, dependency fault, or new node.
Only `lean` and the addition of the already landed definition dependency change
in the item JSON. The original statement and proof are preserved verbatim.

Validation uses `scompile.py` only, compiling this one module in module mode
against the live published library. The full import set passed in both sandbox
and final-module mode; the revised existential signature is checked again in the
mandatory dry run. Every universe and variable is bound explicitly, and no line
exceeds 100 columns. Expected sorry warnings are the only permitted warnings.

## Second reading by N5

This is a separate in-thread rereading of the final node and module, not a claim
of independent review by another agent. The dispatcher forbids subagents and
assigns the independent reading to the maintainer.

I matched the hypothesis and output fields again against the table above. Two
issues found during this rereading were repaired: integrality of the torsor total
space is now supplied existentially rather than imposed as a new hypothesis;
and prescribed charts have local equations on a pointed open, whereas output
charts have the global product equation, allowing the promised removal of other
components. I checked the coefficient-algebra compatibility equation, the
subgroup's additive notation, all root-coordinate exponents, the equalizer
carrier, the isomorphism's canonical coefficient map, both pointed squares,
the refinement direction and the ordered pullback equations. Empty lists and
one-element groups remain included. No source statement was changed.
