## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCoordinateDerivations` states
`AlgebraicGeometry.Scheme.hasEtaleCoordinateCalculus`. Its only theorem has proof `sorry`.
The item statement and all its other fields are unchanged; only `lean` is attached.
There are no new nodes, dependency repairs or statement disputes.

The conclusion is expanded in `HasEtaleCoordinateCalculus`, whose data is a fully written
proposition. The five transparent auxiliary constructions are only the canonical scalar
structures, their derivation types, and the coordinate pullback used in that proposition;
they do not choose any derivations or introduce an independent mathematical notion.
Every declaration belongs to this node and is listed in `lean.declarations`.
No data definition contains `sorry`; there are no auto-bound variables or file-local instance commands.
The scalar `letI` declarations occur only in definitions, not in the theorem signature.

Hypotheses and clauses, in the order of the node:

- A field k is `(k : Type u) [Field k]`.
- A k-scheme U is `(U : Scheme.{u}) [U.Over (Spec (.of k))]`. Finite type is the
  recorded conjunction represented by `[LocallyOfFiniteType (U ↘ Spec (.of k))]` and
  `[QuasiCompact (U ↘ Spec (.of k))]`.
- The integer n ≥ 0 is `(n : ℕ)`, including 0. The coordinate morphism is
  `x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))`. Its k-linearity is
  `[x.IsOver (Spec (.of k))]`, and its étaleness is `[Etale x]`. Being over k is implicit
  in the node's k-scheme coordinate map and explicit in its proof step 1.
- Every affine open V is quantified as `∀ (V : U.Opens) (hV : IsAffineOpen V)`.
  Its ring A is exactly `Γ(U, V)`, not an arbitrary affine algebra or a replacement chart.
  `etaleCoordinateSection` is restriction of `x.appTop (AffineSpace.coord ... (ULift.up i))`.
  `etaleCoordinateSectionAlgebra` is the scalar map k → Γ(Spec k) → Γ(U, ⊤) → Γ(U, V).
- The basis clause is `∃ b : Module.Basis (Fin n) Γ(U,V) (KaehlerDifferential k Γ(U,V)),
  ∀ i, b i = KaehlerDifferential.D k Γ(U,V) (etaleCoordinateSection ... V i)`.
- For every A-module M (any universe v, `[AddCommGroup M] [Module Γ(U,V) M]`),
  `Module.compHom M (algebraMap k Γ(U,V))` installs precisely its induced k-module.
  `Function.Bijective (fun E : Derivation k Γ(U,V) M ↦ fun i ↦ E (etaleCoordinateSection ... i))`
  is the actual evaluation map, with no chosen equivalence in place of the map.
- One existential family `D` supplies a k-derivation of each affine section ring for each i.
  The delta clause is `D V hV i (etaleCoordinateSection ... V j) = if i = j then 1 else 0`.
  The following clause quantifies over every k-derivation E with these values and asserts
  `E = D V hV i`; thus the derivations are unique with exactly the required normalization.
- Commutation on each affine open is the pointwise equality
  `D V hV i (D V hV j c) = D V hV j (D V hV i c)`.
- The differential expansion is the literal finite sum
  `KaehlerDifferential.D k Γ(U,V) c = ∑ i, D V hV i c • KaehlerDifferential.D ... (x_i|V)`.
- For every smaller affine W ≤ V, its actual presheaf restriction map satisfies
  `res (D V hV i c) = D W hW i (res c)`. No principal-open assumption is imposed.
- One existential family `d : ∀ p : U, Fin n → EtaleCoordinateStalkDerivation k U p`
  acts on the actual local rings `U.presheaf.stalk p`, with their scalar map through the
  global germ. For every affine V containing p, the compatibility clause is
  `d p i (germ V p hp c) = germ V p hp (D V hV i c)`. The same d works for all affine
  neighbourhoods, so there is no dependence on a selected affine chart. The final clause
  asserts commutation on every local ring as well.
- Regularity of every finite iterate is built into the actual type: `D V hV i` maps A to A,
  so `is.foldr (fun i b ↦ D V hV i b) c` is an element of A for every finite word is,
  without any existence or localization assumption. No tautological extra conjunct is used.
- Every field extension L/k is `(L : Type w) [Field L] [Algebra k L]`. The map
  `τ : Γ(U,V) →ₐ[k] MvPowerSeries (Fin n) L` is a k-algebra homomorphism, using the
  canonical coefficient algebra structure. For every constants tuple `a : Fin n → L`,
  the hypothesis is exactly `∀ i, τ (x_i|V) = MvPowerSeries.C (a i) + MvPowerSeries.X i`.
- First Taylor comparison is `MvPowerSeries.pderiv L i (τ c) = τ (D V hV i c)` for every i,c.
  The next clause uses `List.foldr` on every word, giving all iterated partial derivatives
  in the same order on both sides, including the empty word.
- Wherever τ extends to germs is expressed without an extra extension assumption:
  for every p ∈ V and every `τp : U.presheaf.stalk p →ₐ[k] MvPowerSeries (Fin n) L`,
  *if* `∀ c, τp (germ V p hp c) = τ c`, then first and every iterated partial derivative
  of τp agree with τp of the corresponding d-derivatives for every germ. These are actual
  extensions through the canonical germ map, not arbitrary ring homomorphisms.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (CommRing + DivisionRing, with
  Nontrivial and the inverse law in DivisionRing).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; both recorded signatures were read.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (affine-local étale ring maps).
- `def-sbc-affine-space`: `AlgebraicGeometry.AffineSpace` and `AffineSpace.coord`,
  `Mathlib.AlgebraicGeometry.AffineSpace`; `SpecIso` and its coordinate normalization were
  also read. `ULift (Fin n)` is the recorded index convention at scheme universe u.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`, `Mathlib.RingTheory.Kaehler.Basic`.
  The statement uses `Derivation` from Mathlib, with precisely the induced scalar module.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic` (publicly supplied by Derivative).
- `def-trf-formal-power-series-partial-derivative`: `MvPowerSeries.pderiv`,
  `Mathlib.RingTheory.MvPowerSeries.Derivative`; read its R-derivation signature, coefficient
  formula, and constant and variable identities.

The proof dependencies are imported non-publicly where they are not already statement
imports: `ΓSpec.adjunction` (GammaSpecAdjunction), the affine étale criterion
`HasRingHomProperty.Spec_iff` and open restriction instance (Etale),
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` (Etale.Kaehler),
`KaehlerDifferential.mvPolynomialBasis` (Kaehler.Polynomial),
`IsAffineOpen.isLocalization_stalk` and the canonical affine immersion/germ comparison
(AffineScheme and its imports), and `Derivation.exists_completion_and_unique_localization`
(WeilConjectures.RingTheory.Derivation.CompletionAndLocalization, using only part (2)).
The recorded signatures and docstrings were read, including the full localization theorem.
The theorem docstring gives all six proof steps, including the commutator cancellation,
restriction uniqueness, local fraction formula, and induction for the Taylor comparison.

Sources read: local Stacks algebra.tex, lemma-formally-etale-omega (0H93),
lemma-differentials-polynomial-ring (00RX), and lemma-universal-omega (00RO).
These give precisely the differential comparison, polynomial basis and universal derivation;
the restriction/commutator/Taylor consequences are the node's own argument and are retained.
The example CompactObject module is withdrawn; its node points to the upstream twin, whose
header and module/declaration documentation were read as the current example.

Edge cases checked before writing: n=0 gives an empty basis of the zero differential module,
a unique zero derivation into every module, an empty differential sum, no coordinate i,
and the identity for the empty word; MvPowerSeries (Fin 0) L still has its usual coefficient
ring meaning. An empty affine V has the zero ring and all its modules are zero; basis and
evaluation remain meaningful, while no unital map to a nonzero L-series ring exists.
No point is asserted in an empty open. Arbitrary positive characteristic is included;
no factorials or characteristic-zero assumptions occur. U need not be separated, and W is
any smaller affine open; compatibility uses the actual presheaf map. Arbitrary modules
(universe v) and field extensions (universe w) are quantified, rather than fixed witnesses.

Searches performed (no exact existing statement found):

- msearch.py / LeanFinder: “An etale coordinate chart has a differential basis and unique
  commuting coordinate derivations compatible with restriction to affine opens and arbitrary
  formal power series homomorphisms”. Eight hits: standard étale presentations and ordinary
  étale/smooth algebra facts, no full coordinate-calculus theorem.
- msearch.py / Loogle: `KaehlerDifferential, Derivation`. Twelve hits, including D and the
  universal property; these are used, none states this theorem.
- msearch.py / grep: `coordinate.*deriv|deriv.*[Ee]tale|[Ee]tale.*deriv` in RingTheory.
  One unrelated local-structure standard étale presentation hit.
- rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for all seven new
  declaration names: no matches. rg of WeilConjectures and Sheaf for coordinate derivations
  found other graded-bialgebra/formal-coordinate results, not an étale scheme chart calculus.
  grep of WeilConjectures for this node id returned no matches.

Validation: prescribed scompile.py passed against current server sources, with no errors or
non-sorry warnings (5.0 s reported, 60 s limit, two threads). Its local attempt encountered
`OSError(28, 'No space left on device')`; the wrapper's server confirmation succeeded.
All definitions are fully written; the only postponed theorem is the named item theorem.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
