## Worker report

The module `Sheaf.AlgebraicGeometry.NormalAffineRationalIndeterminacy` states
`AlgebraicGeometry.Scheme.existsUnique_affine_extension_and_indeterminacy_dim_one`.
It contains one theorem with proof `sorry`, and no definitions or auxiliary theorems.
Only the item's `lean` field changes. There are no new nodes, dependency modules,
statement corrections, or disputed statements.

The source is BLR, *Néron Models*, §4.4 Lemma 2, printed p.109, PDF page index 115,
read in the primary scan:
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
The supporting scalar intersection theorem was read in
`literature/stacks-project/algebra.tex`,
`lemma-normal-domain-intersection-localizations-height-1`, Tag 031T(2).
The latest blueprint direct-image statement was also read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md`.
The BLR assertion applies to an arbitrary affine target; it imposes no finite-type
or factoriality hypothesis. The docstring carries all six proof steps and names
all twelve proof dependencies, including specialization of the reflexive-module
intersection criterion to the module R.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| W is a nonempty integral scheme | `(W : Scheme.{u}) [IsIntegral W]`; this class includes nonemptiness and domains of sections on nonempty opens. |
| Noetherian, meaning locally Noetherian and quasi-compact | `[IsNoetherian W]`; Mathlib's class extends `IsLocallyNoetherian W` and `CompactSpace W`. |
| Every local ring is an integrally closed domain | `_hnormal : ∀ x : W, IsDomain (W.presheaf.stalk x) ∧ IsIntegrallyClosed (W.presheaf.stalk x)`. |
| An arbitrary commutative ring A, with H = Spec A | `(A : Type u) [CommRing A]`, and `Spec (CommRingCat.of A)` throughout. |
| A dense open D and a morphism h from D | `(D : W.Opens) (_hD : Dense (D : Set W)) (h : D.toScheme ⟶ Spec (CommRingCat.of A))`. |
| E is the union of every open V admitting an extension hV agreeing with h on V ∩ D | `(E : W.Opens)` with `_hE : E = sSup {V : W.Opens \| ∃ hV, ...}`. The displayed equality is exactly this definition of E, supplied as an equality binder rather than a new definition. |
| Agreement on V ∩ D | `W.homOfLE (inf_le_left : V ⊓ D ≤ V) ≫ hV = W.homOfLE (inf_le_right : V ⊓ D ≤ D) ≫ h`. |
| A unique hE restricting to every such hV | The first conjunct is `∃! hE : E.toScheme ⟶ Spec (CommRingCat.of A), ∀ V hV, agreement → ∃ i : V ≤ E, W.homOfLE i ≫ hE = hV`. The existential inclusion expresses the inclusion needed to form the restriction; it does not assume an extension. Its proof is immaterial by proof irrelevance. |
| Every irreducible component of the closed complement | `∀ C ∈ irreducibleComponents {x : W // x ∉ E}, ...`. This is the subspace of the complement; E is open, so the complement is closed. |
| A generic point ξ of that component | `∃ ξ : W, IsGenericPoint ξ (Subtype.val '' C) ∧ ...`. The image transports the component subset from the complement subspace to W. |
| Local ring dimension equals one | `ringKrullDim (W.presheaf.stalk ξ) = 1`, with Mathlib's `WithBot ℕ∞` dimension. |
| The complement may be empty | No nonemptiness hypothesis is imposed on the complement or on its set of components; universal quantification has no instances when it is empty. |
| No field, finite generation of A, or factoriality of W | No such binders occur. Both schemes live in a common arbitrary universe `u`; there is no cardinal restriction inside that universe. |

The binders E and its defining equality are just an explicit way of stating a
result about the open defined by the displayed union. This introduces no
mathematical assumption on the data: every complete lattice of opens has this
supremum. In particular the theorem requires no chosen extension on E. Taking
V = D and hV = h in its first conclusion recovers hE restricted to D = h.

Statement dependencies used, with declarations and modules (full signatures and
docstrings read in the pinned source):

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`; its `IsNoetherian` combines the two
  Noetherian hypotheses without changing them.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`, used inline
  on every stalk as the dependency record prescribes;
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme` (publicly available through the scheme imports).
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`; the dependency is a Mathlib leaf with no `lean`
  record, and its exact `mathlib_match` is used.
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`.

`W.homOfLE`, the canonical inclusion of open subschemes from
`Mathlib.AlgebraicGeometry.Restrict`, renders all restrictions; there is no
private restriction map or independent notion of rational-map domain.

The available proof dependencies are imported without `public`:
`Mathlib.AlgebraicGeometry.FunctionField`, `.GammaSpecAdjunction`, `.Gluing`,
`.AffineScheme`, `.ResidueField`, `Mathlib.Topology.NoetherianSpace`,
`Mathlib.RingTheory.Ideal.Height`,
`WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection`, and
`Sheaf.RingTheory.ReflexiveHeightOneIntersection`.
The Noetherian and sober proof dependencies also use the already-public
statement modules. The two project declarations are respectively
`AlgebraicGeometry.Scheme.exists_integral_section_denseOpen` and
`Module.isReflexive_iff_isTorsionFree_and_heightOne_intersection`.
All recorded proof-dependency interfaces are available; none is deferred or omitted.

Edge cases checked before writing and again after elaboration:

- W cannot be empty: this is part of integrality, not an added assumption.
  Density then forces D nonempty. Empty extension opens V are still included.
- If D = W, or h extends globally (for example a constant morphism), E is top,
  the unique extension exists, and the component clause is vacuous.
- If W is the spectrum of a field, every dense open is top, so no dimension-one
  point is incorrectly required.
- If A is the zero ring, Spec A is empty and there is no morphism from the
  nonempty D. The theorem retains this case as an implication with no such input;
  it does not add `Nontrivial A`.
- On the affine plane, h defined by 1/x has complement V(x), whose generic local
  ring has dimension one. A regular function on the punctured affine plane
  extends globally, so no component of dimension two is asserted.
- Normal singular schemes are allowed. On the normal quadratic cone xy = z²,
  x/z = z/y has divisorial boundary V(y,z); no regularity or factoriality binder
  has slipped into the Lean statement.
- An infinitely generated ring A is allowed: the conclusion quantifies over
  actual scheme morphisms, without a finite generating family or finite-type
  map. The proof's ring homomorphism is reconstructed coordinate by coordinate.

Searches for an existing statement:

- `msearch.py ... leanfinder "A rational map from a normal Noetherian integral scheme to an affine scheme has indeterminacy locus of pure codimension one"`:
  eight hits, including `Scheme.RationalMap.domain`, `.dense_domain`,
  `.toPartialMap`, `.fromFunctionField` and `.ofFunctionField`. None asserts
  the pure-codimension-one boundary conclusion. The source
  `Mathlib.AlgebraicGeometry.Birational.RationalMap` was read: its domain is
  the union of equivalent partial-map domains, and the representative gluing
  API supplies no normality/codimension theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.RationalMap, IsIntegral, IsNoetherian"`:
  zero hits.
- `msearch.py ... grep "indeterminacy|Hartogs|normal.*rational|rational.*normal" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "The indeterminacy locus of a rational map from a normal noetherian integral scheme into Spec A has pure codimension one"`:
  eight hits on rational maps, partial maps and germ-injectivity; no exact theorem.
- `rg -n 'indeterminacy|Hartogs|normal.*rational|rational.*normal'` in both
  `lean/WeilConjectures` and `lean/Sheaf`: unrelated analytic Hartogs theorems,
  local regular-scheme Hartogs for functions and divisors, normalizations and
  rational coefficient material; no exact affine-indeterminacy statement.
- `grep -rn 'lem-sfb-normal-affine-rational-indeterminacy' lean/WeilConjectures`:
  no hits. The item id and proposed declaration name were also searched in
  `dag/lean_names_upstream.json`: no hits.

Validation: `scompile.py Q92 lem-sfb-normal-affine-rational-indeterminacy <module>`
passed both the sandbox compile and library-module compile, with no warnings or
errors. `set_option autoImplicit false` is explicit in the module. The initial
probe used an ambiguous coercion of the complement set to a type; this was
replaced by the explicit subspace type `{x : W // x ∉ E}`. No mathematical
statement changed. Every line of Lean has at most 100 characters.

## Second reading by Q92

The dispatcher assigned one worker and explicitly forbids starting other agents.
This section records a separate second pass by that same worker, not an
independent-agent review; the delivery is supplied for the maintainer's independent
review as the assignment specifies.

Reopened the node and final Lean file and checked the correspondence table above.
The normality condition remains on every stalk; Noetherian includes compactness;
integrality includes nonemptiness. The target is the actual Spec of an unrestricted
commutative ring. In the union and restriction conclusion both maps are pulled
back to precisely V ∩ D, with left inclusion to V and right inclusion to D.
E's defining equality is not replaced by an assumed morphism on E. Unique
existence applies to maps restricting to every candidate hV, including empty V
and V = D. The inclusion witness in the restriction clause is required to exist,
so this is not an implication made vacuous by an absent inclusion.

Components are components of the closed complement subspace, not components of W.
`Subtype.val '' C` is exactly the corresponding closed irreducible subset of W;
`IsGenericPoint` asserts its singleton closure, and the local ring is W's actual
stalk at that point. The dimension conclusion is exactly one, not at most one.
An empty complement creates no component obligation. No missing clause, extra
hypothesis, or second definition was found. No further change was needed after
the explicit-subtype elaboration fix.
