## Worker report

The module `Sheaf.Paper.RealBoundaryPathIndependence` states
`RealSheaves.boundary_inertia_invariants_path_independent`. Its proof is `sorry`.
The helper `RealSheaves.BoundaryInertiaPathIndependence` is the full reducible predicate,
whose body supplies the ordinary open-curve instance and universally quantifies the Weil
presentation, sheaf, two path maps, local representations and Frobenius lift. The theorem
asserts this predicate. This keeps the derived instance out of the hypotheses and keeps
instance bindings inside an unfoldable definition, not in the theorem statement.
The statement gives a linear equivalence between the two inertia-invariant spaces and the
pointwise equation `A (T₁ x) = T₂ (A x)`. No statement correction or new DAG node is proposed.

Hypotheses and clauses, read against the node (proof binders inside the predicate have an
underscore prefix to satisfy Lean's unused-variable linter; their hypotheses are retained):

- `D : RealSheaves.Setup.{u,v}` supplies both primes, the positive exponent, the finite base
  field, its algebraic closure, the coefficient closure and embedding of d-real-setup.
  `C₀` is over `Spec D.k₀`, and `hC : D.IsCurve C₀` is exactly the nonempty, separated,
  smooth, finite-type, pure-dimension-one, geometrically connected curve convention.
- `U₀ : C₀.Opens` is the open immersion (its canonical map is `U₀.ι`), `hU` says nonempty,
  and `hS : (U₀ : Set C₀)ᶜ.Finite` says its complement is finite. `s`, `hs : s ∉ U₀`
  select a boundary point. No affine or proper assumption is present.
- The binders from `H` through `hξ` are copied from the recorded decomposition-landing
  interface, preserving its local field models and characterizing equations. `hH` says
  that H is the henselization of the stalk at its maximal ideal; the localization at this
  ideal does not change the local stalk. `K` with `IsFractionRing H K` is its fraction
  field. `Ω` is an algebraic closure of K; the algebra and scalar tower instances express
  the structural maps. The local integral closure, local structural map and algebraic
  closure residue-field instances express the compatible local/residue closures.
  `a`, `ha` specify extension of every field automorphism to the integral closure;
  `Ωr`, its algebraic-closure instance and `e` identify the chosen residue closure.
  `r`, `hr` specify the residue homomorphism on every residue class; it is not arbitrary.
  `Φ`, `hΦ` are geometric residue Frobenius, inverse to raising to `#κ(s)`.
  `ξ`, `hξ` specify the local generic point's canonical factorization through the open.
- `W` is the recorded global Weil-group presentation. Its ordinary curve structure is
  supplied explicitly by `D.openIsCurve C₀ hC U₀ hU`, not assumed in the main theorem.
  `B`, `M`, `DM` are the recorded fundamental-representation presentation data (base point,
  Frobenius path, lisse stalk transport, geometric-kernel identification and degree-one
  lift). `F : WeilSheaf D.k₀ D.l U₀.toScheme` and `hF : F.IsLisse` are the lisse Weil sheaf.
  The vector space is precisely
  `ProEtale.LisseMonodromy.StalkSpace B.t (F.toLisse hF)`, with coefficients in the upstream
  chosen algebraic closure `PadicAlgCl D.l`. This uses that dependency's coefficient model.
- The geometric base point is `B.t`; `B.path` identifies its arithmetic fibre functor with
  that at `W.basePoint`. The two `γ₁`, `γ₂` have the same local geometric source. Composing
  with `B.path.symm` gives the two paths to the arithmetic image of `B.t`. Thus the use of
  `W.basePoint` in their displayed target is exactly the fundamental-group presentation
  of paths to the geometric base point, not a replacement of the local geometric point.
- `θ₁`, `θ₂` take values in `W.fundamentalGroup`. `hθ₁`, `hθ₂` impose the exact
  decomposition-landing formula on every cover P and every local fibre point z: after
  transport back by γ the action is precomposition by `Spec.map σ.toRingHom`.
  This pins down both decomposition maps; it does not replace them by arbitrary conjugate
  homomorphisms. Continuity is already a property of these characterized maps by the
  imported decomposition-landing theorem, not an extra hypothesis of this statement.
- The local Weil group is `(Subgroup.zpowers Φ).comap r`, exactly the inverse image of the
  integer powers of residue geometric Frobenius. `τ₁`, `τ₂` are the restrictions of θ to
  this group with codomain W. `hτ₁`, `hτ₂` specify their composites with the actual inclusion
  `W.toFundamentalGroup`; therefore they are the unique lifts of the decomposition maps,
  not freely chosen auxiliary maps. Their existence is the imported landing assertion.
- `α₁`, `α₂`, with `hα₁`, `hα₂`, name exactly the local representations
  `(WeilGroup.fundamentalRep M DM F hF).comp τₐ`. The equalities introduce no independent
  representation assumption. The Weil representation is defined on the entire W.
- The inertia subgroup of the local Weil group is
  `r.ker.comap ((Subgroup.zpowers Φ).comap r).subtype`. This is I_s with its inclusion into
  W(K_s); every element of the full kernel lies in W(K_s) since 1 is a power of Φ.
  `Representation.invariants` of the restriction along its subtype is exactly the
  vector subspace fixed by every inertia element, using the operations dependency's
  stated Mathlib convention. Normality is synthesized from kernel and comap normality.
- `φ` is any element of the local Weil group with `hφ : r φ.val = Φ`, hence any residue
  geometric Frobenius lift. `αₐ.toInvariants … φ` is its induced linear operator. It is
  invertible since it belongs to a group representation. The quotient action
  `Representation.quotientToInvariants` from the Mathlib dependency identifies operators
  for lifts in the same inertia coset. The conclusion's `≃ₗ` and pointwise equation are
  exactly the requested linear isomorphism and Frobenius intertwining, with no choice of
  a specific isomorphism or assertion that it is canonical.

Dependency declarations read and used:

- `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup`, `Setup.IsCurve`,
  `Setup.coefficientCharFact`; the supplied `Setup.openIsCurve` is described below.
- `Sheaf.Paper.RealBoundaryDecompositionLanding`:
  `RealSheaves.exists_boundary_decomposition_landing`; its full signature and docstring
  supply the local models, the fibre-action characterization and the subgroup landing.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation`:
  `AlgebraicGeometry.WeilGroup.fundamentalRep`, `BasePointData`, `WeilMonodromyData`, and
  `WeilSheaf.toLisse`. The live source was read with `scompile.py --source` because that
  module is absent from the older local source checkout.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`:
  the operations docstring of `WeilGroup.detLine` explicitly records subgroup invariants
  as `(ρ.comp I.subtype).invariants`. Imported for the recorded dependency; the actual
  subspace construction is Mathlib's `Representation.invariants`.
- `Mathlib.RepresentationTheory.Invariants`: `Representation.invariants`, `toInvariants`,
  `quotientToInvariants` and `quotientToInvariants_lift`; their full signatures and
  documentation were checked in source. The latter pair is the exact Mathlib match of
  lem-real-boundary-frobenius-invariants.
- Proof dependencies already stated are reached by the imports of decomposition landing,
  the Weil representation and `Sheaf.FieldTheory.FiniteFieldAbsoluteGalois`
  (`finiteField_absoluteGaloisGroup`). The path notion is the actual natural isomorphism
  of the recorded `Scheme.FiniteEtale.fiber` functors. The local-constants proof dependency
  currently has no Lean record; no import of a nonexistent module is introduced. Its
  source-based five-step use is retained in the main theorem's proof docstring.

Edge cases checked: identical paths (the identity isomorphism suffices); zero-dimensional
stalk V=0; zero invariant subspace; trivial inertia; a nontrivial residue degree e_s>1;
negative Weil degrees; all Frobenius lifts, not only one distinguished lift. An empty open
is expressly excluded by the node. Empty complement has no s satisfying hs, so the boundary
assertion then has no instance. Neither inertia nor the local Weil group is assumed finite,
and no action of the full arithmetic fundamental group on the stalk is presumed.

Searches for existing statements (2026-10-18):

- `msearch.py`, LeanFinder: “Changing etale paths gives Frobenius equivariant linear
  isomorphisms of inertia invariant spaces of a lisse Weil representation”. No exact
  match; the hits concern arithmetic Frobenius conjugacy and residue-field isomorphisms.
- `msearch.py`, Loogle, `Representation.quotientToInvariants`: two exact matches for the
  quotient action and its lift, used through Mathlib; neither asserts path independence.
- `msearch.py`, LeanSearch: “conjugate paths give isomorphic inertia invariants commuting
  with Frobenius”. Eight hits concern arithmetic Frobenius conjugacy, topological paths
  and linear conjugation, with no exact match.
- `msearch.py`, grep, `path.*indepen|indepen.*path|conjugat.*invariants`: three results in
  topological homotopy and fundamental groupoids, not etale Weil representations.
- `rg` of the project's older source RealSheaves modules for path, inertia and boundary,
  and for the exact node id throughout WeilConjectures: no exact statement. BoundaryInertia
  and BoundaryConstruction supply related constructions, not this path-independence theorem.
- `rg` in `lean/Sheaf` for path independence and RealBoundary declarations found the
  decomposition-landing module but no statement of this item. The upstream name index
  was also searched; no matching declaration. `openIsCurve` was searched in both source
  trees and the upstream index and was not already defined.

The main theorem docstring contains the complete five-step proof of the node, including
factorization on the finite residue-field quotient, inertia conjugacy, inverse maps from
rho(w) and rho(w^{-1}), and the Frobenius calculation. All universes and variables are
explicit; no file-local notation, local instance, hidden choice of a map or theorem proof
other than `sorry` is introduced.

## Dependency modules

`d-real-setup`: the recorded module has the correct chapter curve predicate, but it exposes
no bridge from that predicate to the ordinary `AlgebraicGeometry.IsCurve` structure on an
open subscheme, required by the recorded Weil representation API. The dependency repair
preserves its entire existing source and adds `RealSheaves.Setup.openIsCurve`, with the
full elementary proof in its docstring and proof `sorry`. The result is a proposition-valued
structure, so it introduces no undetermined data. The assertion predicate installs this result before
binding `WeilGroup` and adds no IsCurve hypothesis. The only node change is its `lean`
record, including the required explanation and declaration list. Existing characteristic
and coefficient-prime interfaces are preserved.

## Second reading by Q01

The delivered section said that no independent reading had been done (the author's own
recheck only; delivery-errors H11). This section replaces it. The maintainer's second
reader (cc review service, run 2) wrote it with the node, the source place and both
modules open. Nothing in the Lean was changed.

Source: main-20261015 sk-d-real-boundary, d-real-boundary.md ("Another choice of path
changes the homomorphism by conjugation, and V_s^{I_s} with its residue Frobenius action
is independent of the choice up to Frobenius-equivariant isomorphism") and
d-real-boundary.proof.md (g = wd, conjugation preserves I_s, rho(w) identifies the two
invariant spaces). The node states exactly this with nothing added.

Node clauses and the Lean that renders them:

1. C₀/k₀ is a curve of d-real-setup: `D : Setup`, `[C₀.Over (Spec D.k₀)]`,
   `hC : D.IsCurve C₀`. This is the recorded predicate (nonempty, separated, smooth, LOFT, QC,
   pure dimension 1, geometrically connected). OK.
2. j : U₀ → C₀ is a nonempty open with finite complement, and s ∈ S₀: `U₀ : C₀.Opens`, `hU`,
   `hS`, `s`, `hs : s ∉ U₀`. OK. No affine or proper assumption.
3. The local objects D_s, I_s, W(K_s), the residue map r_s and Φ_s, as in decomposition-landing:
   the binders `H … hξ` are copied verbatim from `exists_boundary_decomposition_landing`.
   I compared them clause by clause. `D_s = Ω ≃ₐ[K] Ω`, `r_s = r` (pinned by `hr`),
   `I_s = r.ker` restricted to `W(K_s) = (zpowers Φ).comap r`, and Φ is geometric
   Frobenius by `hΦ` (Φ⁻¹ x = x^{#κ(s)}). OK.
4. A lisse Weil sheaf on U₀ with its Weil fundamental representation ρ on V = F_ū:
   `F : WeilSheaf D.k₀ D.l U₀`, `hF : F.IsLisse`, and `fundamentalRep M DM F hF` on
   `StalkSpace B.t (F.toLisse hF)`. These are the recorded declarations of
   def-wf-fundamental-representation (live source read). The ordinary `IsCurve` instance
   that the API needs comes from `Setup.openIsCurve` (hC, hU), not from a new hypothesis.
5. Two paths from the same local geometric point, giving θ₁ and θ₂: `γ₁ γ₂` share the source
   `fiber (Spec Ω → Spec K → U₀)`. `hθ₁` and `hθ₂` are the landing formula
   θ(σ) = γ a_σ γ⁻¹ on every finite étale P, so θ is determined by γ and is not an arbitrary
   conjugate. The target is `W.basePoint`, which `B.path` identifies with ū = `B.t`. OK.
6. ρ∘θ_a restricted to W(K_s): `τ₁` and `τ₂` into `W.carrier` with `hτ` (unique lifts,
   because `toFundamentalGroup` is injective through `weilGroupEquiv`). Then
   `α_a = fundamentalRep … ∘ τ_a` (`hα`). OK.
7. V_{s,a}^{I_s}: `Representation.invariants (α_a.comp I_s.subtype)`. This is the operations
   node's convention for invariants and is the same as fixing θ_a(I_s). OK.
8. T_a is the restriction of ρ(θ_a(Φ)) for a Frobenius lift, and does not depend on the lift:
   `φ` with `hφ : r φ = Φ` is any lift, the same for a = 1 and 2, and
   `α_a.toInvariants I_s φ`. lem-real-boundary-frobenius-invariants is recorded as
   `mathlib_match = Representation.quotientToInvariants`, and that is used. OK.
9. Conclusion, ∃ A linear iso with A T₁ = T₂ A: `∃ A : … ≃ₗ[PadicAlgCl D.l] …,
   ∀ x, A (T₁ x) = T₂ (A x)`. It is neither weaker (a full linear equivalence) nor stronger
   (no canonicity is claimed). OK.

The statement is wrapped in `BoundaryInertiaPathIndependence`, an exposed Prop-valued
definition. Its body is the whole assertion, so it is not a hollow definition. The theorem's
proof is `sorry`. Note: the docstring calls the definition "reducible", but it is a plain
`@[expose]` def. It can be unfolded, so this does not matter.

Truth check: the docstring proof uses only the homomorphism law of ρ on W.carrier. Because
of this, the universally quantified presentation data (W, B, M, DM) cannot make the
statement false. The existence of θ and τ (landing) means it is not vacuous.

Edge cases: identical paths (A = id); V = 0; trivial or total inertia invariants; e_s > 1;
a nonempty open of a geometrically connected curve (so a WeilGroup structure exists);
S₀ = ∅ (no s, so nothing is asserted); Frobenius lifts that differ by inertia.

Dependency module (d-real-setup, §1(B)): the existing source is preserved byte for byte.
The only additions are the `Curve` import and the theorem `Setup.openIsCurve`, with proof
`sorry`. This theorem is true: a finite-type k₀-scheme is noetherian, so an open subscheme
is QC, LOFT and separated over k₀, of dimension ≤ 1. `AlgebraicGeometry.IsCurve` is a
Prop-valued class with exactly these fields. Only the `lean` field of the node changed,
and it has a `lean.note`.

Searches: the worker's LeanFinder, Loogle, LeanSearch and grep records were re-read. The
reviewer also checked the live `WeilFundamentalRepresentation`, `LinearAlgebra` and
`RealSheaves/Basic` (`WeilGroup`) modules. No existing path-independence statement was found.

Compile: `tools/nt_compile.py --json` on both modules (setup first) against the local
side overlay. Result: `RealSheavesSetup` 4.0 s, `RealBoundaryDecompositionLanding` 4.9 s,
`RealBoundaryPathIndependence` 6.0 s, rc 0, no diagnostics. An error probe confirmed that
diagnostics are shown.
