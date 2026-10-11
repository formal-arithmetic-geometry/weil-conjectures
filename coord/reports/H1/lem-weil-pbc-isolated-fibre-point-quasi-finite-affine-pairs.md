## Worker report

The module `Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs` states
`AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`.
Its proof is `sorry`; no result is proved and no definition is introduced.
The node is unchanged outside `lean`. No new or dependency modules are needed.

Hypothesis and clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`; no global finite type,
  quasi-compactness, separation or Noetherian hypothesis is assumed.
- Point x: `(x : X)`. The named image s is inlined as `f x`.
- The fibre X_s and its unique point above x: `f.fiber (f x)` and `f.asFiber x`.
  `asFiber` is defined using `fiberHomeo`, and `fiberι_asFiber` gives its image x;
  injectivity of the fibre projection supplies uniqueness without an extra hypothesis.
- Isolatedness: `hisolated : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))`.
- Arbitrary opens: `(U : X.Opens) (V : S.Opens)`.
- Affineness of their open subschemes: `hU : IsAffineOpen U`, `hV : IsAffineOpen V`.
  These provide canonical charts `hU.isoSpec`, `hV.isoSpec` over their rings of sections,
  rather than adding arbitrary choices of isomorphism as hypotheses.
- x belongs to U: `hx : x ∈ U`.
- f(U) lies in V: `hUV : U ≤ f ⁻¹ᵁ V`.
- A = O_X(U), R = O_S(V): `Γ(X, U)`, `Γ(S, V)`.
- Induced ring map φ: `(f.appLE V U hUV).hom`. Its `toAlgebra` gives exactly
  the R-algebra structure used in both parts of the conclusion.
- Prime q corresponding to x: `hU.primeIdealOf ⟨x, hx⟩`.
- φ is finite type: `∃ hft : Algebra.FiniteType Γ(S, V) Γ(X, U)` under that
  algebra structure. This is a conclusion, not an extra assumption.
- Quasi-finiteness at q: after installing precisely that finite-type witness,
  `Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩)`.
  The recorded definition asserts openness of the singleton of the corresponding
  prime in `κ(p) ⊗[R] A`, using `PrimeSpectrum.preimageHomeomorphFiber`.
  The tensor factors are in Mathlib's canonical fibre-ring order.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (Mathlib match; no lean record required).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber`, `fiberι`, `fiberHomeo`, `asFiber`,
  `Mathlib.AlgebraicGeometry.Fiber`; `Scheme.fromSpecResidueField` in
  `Mathlib.AlgebraicGeometry.ResidueField` constructs its base morphism.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; the canonical affine identification and prime
  are `IsAffineOpen.isoSpec` and `IsAffineOpen.primeIdealOf` in
  `Mathlib.AlgebraicGeometry.AffineScheme`. These are available transitively.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`: `Algebra.IsQuasiFiniteAtPrime`,
  `Sheaf.RingTheory.QuasiFiniteAtPrime`, imported directly and used without duplication.

Edge cases checked before writing: empty source admits no x; empty U contradicts hx;
empty V contradicts hUV and hx. Thus a zero section ring with empty spectrum cannot
produce a missing prime. U and V need not be connected or nonempty independently,
and no irreducibility, reducedness or finiteness of the entire fibre is required.
A nonempty fibre with one isolated point and other positive-dimensional components
is allowed. Arbitrary characteristics are allowed. The common scheme universe u is
Mathlib's scheme category convention, and no independent test-object universe occurs.

Searches (actual runs logged in searches.jsonl):

- LeanSearch, "An isolated fibre point of a locally finite type scheme morphism gives
  a quasi-finite ring map at its prime on any affine pair": service unavailable
  (Internal Server Error); no mathematical verdict based on this search.
- Loogle, `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt`: found the stalk-map predicate,
  `QuasiFiniteAt.quasiFiniteAt`, and `quasiFiniteAt_iff_isOpen_singleton_asFiber`.
  The affine-pair result uses the localization notion rather than the recorded
  isolated fibre-ring prime definition, and separately lacks the finite-type clause.
- LeanFinder, "isolated point in scheme fibre implies induced ring map on affine
  open sections is quasi finite at corresponding prime": found global
  `LocallyQuasiFinite.quasiFinite_appLE` and `Scheme.Hom.finiteType_appLE`.
  Neither is the statement here: the former assumes the global property.
- Mathlib grep through msearch, `quasiFiniteAt_iff_isOpen_singleton|finiteType_appLE|def asFiber`
  in AlgebraicGeometry: found the above component results, no exact statement.
- Source project rg, `isolated.*affine|isQuasiFiniteAtPrime|quasiFiniteAt_iff_isOpen_singleton`:
  uses of Mathlib's isolated-point equivalence in Isogeny and ZariskisMainTheorem,
  no exact match. Grep of the item id in WeilConjectures returned no match.
- Sheaf rg for `IsQuasiFiniteAtPrime|isolated.*affine` in AlgebraicGeometry and searches
  in RingTheory: the shared definition and other ring-theoretic statements exist;
  no affine-pair statement. The chosen full declaration name was also checked in
  dag/lean_names_upstream.json, Mathlib and WeilConjectures and was absent.

Source checked: the local Stacks checkout is not present on this machine, so read
https://stacks.math.columbia.edu/tag/01TH (Lemma 29.21.6, (2) implies (4), last paragraph)
and https://stacks.math.columbia.edu/tag/01T2 (Lemma 29.15.2, (1) implies (2)) directly.
They agree with the node. The module docstring includes all six proof steps and the
supporting node names, including chart compatibility, residue-field naturality,
open fibre products, the affine fibre-ring identification and uniqueness of its prime.
No statement correction or dispute.

## Second reading by H1

I independently read the node statement, its Stacks source (Tags 01TH and 01T2), and the Lean declaration.
The object and hypothesis correspondence is as follows:

- The morphism of schemes is `{X S : Scheme.{u}}` and `f : X ⟶ S`.
- “Locally of finite type” is exactly `[LocallyOfFiniteType f]`; no global finite-type,
  quasi-compactness, separatedness, or Noetherian hypothesis is added.
- The point is `x : X`; the source's `s = f(x)` is rendered by `f x`.
- The fibre and its projection are rendered by `f.fiber (f x)` and its canonical
  projection; the source's unique point over `x` is Mathlib's canonical `f.asFiber x`.
  Thus `hisolated : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))` says exactly that
  this point is isolated in the fibre.
- Affine opens `U,V`, their affine hypotheses, membership `hx : x ∈ U`, and image
  containment are rendered by `U V hU hV hx hUV`, with `hUV : U ≤ f ⁻¹ᵁ V`.
- The section rings are `Γ(X,U)` and `Γ(S,V)`, and the induced map is
  `(f.appLE V U hUV).hom.toAlgebra`; the corresponding prime is
  `hU.primeIdealOf ⟨x,hx⟩`.
- The conclusion is exactly the two source clauses: an existential finite-type
  witness `hft : Algebra.FiniteType Γ(S,V) Γ(X,U)`, followed under that witness by
  `Algebra.IsQuasiFiniteAtPrime ... (hU.primeIdealOf ⟨x,hx⟩)`.

No mismatch was found and no Lean or node correction was needed. In particular, the
existential finite-type witness is the Lean rendering of the source's “finite type”
clause and supplies the typeclass required by the recorded quasi-finiteness definition;
`hV` is retained because the node requires the target open to be affine. The module
contains only the requested theorem with a `sorry` proof and its docstring records all
six proof steps from the node.

Edge cases checked: an empty source or empty `U` cannot satisfy the point-membership
hypothesis; `hUV` and `hx` force `V` to contain `f x`; no nonemptiness, reducedness,
connectedness, characteristic, or fibre-finiteness assumption is introduced. The
universe is shared by both schemes as in the node, and there is no independent test
universe. Zero section rings and empty spectra therefore cannot create an unbound
prime under the hypotheses. The statement covers arbitrary characteristic and the
case of a fibre having other components besides the isolated point.

Searches were rechecked against Mathlib, `WeilConjectures/`, and `lean/Sheaf/` using
Loogle/LeanFinder-style searches and `rg` for `isQuasiFiniteAtPrime`, affine-pair,
and isolated-fibre names. Only component results (`Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`,
`QuasiFiniteAt.quasiFiniteAt`, `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`,
`PrimeSpectrum.preimageHomeomorphFiber`, and `finiteType_appLE`) were found; none
states this affine-pair theorem or the project's fibre-ring definition. The source
pages confirm Tag 01TH (2) implies (4), with finite type supplied by Tag 01T2.
Compilation with `scompile.py` succeeds.

Dependency signatures checked independently: `LocallyOfFiniteType.finiteType_appLE`
quantifies over all affine pairs; `IsAffineOpen` is `IsAffine` of the open subscheme;
`hU.isoSpec : U ≅ Spec Γ(X,U)` and `hU.primeIdealOf` are the canonical chart and its
point map. `Scheme.Hom.fiber` is the residue-field pullback, and `asFiber` is defined
by the inverse of `fiberHomeo`, not by an extra chosen lift. I opened the recorded
`Sheaf.RingTheory.QuasiFiniteAtPrime` definition: its data is an actual open-singleton
predicate in `PrimeSpectrum (p.asIdeal.Fiber S)`, with no `sorry` or stronger field
assumption. This is exactly the dependency node up to the prescribed tensor swap.
No new nodes or dependency replacement modules are required. The node's stored
`lean.statement` agrees verbatim with the module signature. The independent Loogle
query `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` and LeanFinder query `isolated fibre
point finite type map on affine open sections quasi finite at prime` both ran
successfully; their component results agree with the no-exact-match verdict above.
