## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianLogPairStrictResolution` states
`AlgebraicGeometry.exists_noetherian_log_pair_strict_resolution`. Its only theorem has
proof `sorry`. No definition, helper, node correction, or dependency repair is needed.
The complete thirteen-step DAG proof is included in its theorem docstring, including
integrality and excellence along the normalized log blowups, boundary strictification,
termination, the parameter calculation, and final composition.

Hypotheses and clauses, read against the unchanged node:

- The input scheme is `M : Scheme.{u}`, with `[IsIntegral M]` and `[IsNoetherian M]`.
  `IsIntegral` includes nonemptiness. `IsNoetherian` includes local Noetherianity and
  quasi-compactness; its affine coordinate rings are Noetherian.
- Excellence is `hExcellent : ∀ W : M.affineOpens, IsExcellent Γ(M, W)`, the affine-open
  criterion already used by the published excellent-normalization interface. It is the
  scheme interpretation of the recorded excellent-ring definition, without a field,
  characteristic, finite-dimensionality, or finite-type hypothesis.
- `B : TopologicalSpace.Closeds M` is precisely a closed subset, without imposing an
  additional subscheme structure. `U`, `j`, `[IsOpenImmersion j]`, and `hBU` present its
  open complement. `hU : DenseRange j` says this complement is dense, equivalently that
  the closed subset B is nowhere dense. These are presentation data for the pair, not
  an extra geometric restriction: every such B supplies its canonical open subscheme.
- `hlog : IsDivisorialFineSaturatedLogRegularPair M U j hU` uses the recorded divisorial
  fs log structure with its etale charts, exact triviality locus, regular strata, and
  characteristic-rank dimension formula. Local Noetherianity is inherited from M.
- `∃ (R : Scheme.{u}) (e : R ⟶ M) (A : R.IdealSheafData)` supplies exactly the resolution
  scheme, morphism, and closed boundary subscheme. The ambient universe is unrestricted.
- `IsIntegral R ∧ IsRegularScheme R ∧ IsNoetherian R` supplies all three properties of R.
  The regular-scheme predicate explicitly includes local Noetherianity, matching the
  repaired recorded dependency rather than silently using only stalkwise regularity.
- `IsProper e` is the recorded properness class.
- The existential `V`, `W`, and `i : W.toScheme ≅ V.toScheme`, with both `Dense` clauses
  and `i.hom ≫ V.ι = W.ι ≫ e`, says precisely that e induces an isomorphism on dense open
  subschemes. It does not require the isomorphism to hold on the whole complement of B,
  which the proof establishes but the node does not require.
- `IsStrictNormalCrossingsBoundary A` uses the recorded reduced effective Cartier,
  distinct integral regular component, and regular expected-codimension intersection
  criterion. This is strict normal crossings, not an etale-only branch condition.
- `e ⁻¹' (B : Set M) ⊆ (A.support : Set R)` is the requested support containment.
  No equality of supports or of subscheme structures is added.
- The final `∀ x : R` chooses an affine neighbourhood `W` and membership `hx`. The
  sections `t : Fin s → Γ(R, W)` give actual equations on this neighbourhood. The list
  `l` is a full regular system of parameters of the ordinary local ring at x via the
  recorded `IsLocalRing.IsRegularSystemOfParameters`. Its needed Noetherian-ring proof
  is existentially bound as `hN` and supplied explicitly to the predicate. Such a proof
  is automatic from Noetherianity of R, so this introduces no additional restriction.
- `List.ofFn (fun a ↦ (R.presheaf.germ W.1 x hx).hom (t a)) |>.IsPrefix l` says the germs
  of the equations form an initial part of a regular system of parameters. An arbitrary
  part can always be reordered to the front; the node prescribes no order.
- The injectivity of `a ↦ Ideal.span {t a}` and equality of `(A.ideal W).minimalPrimes`
  with its range identify the equations with exactly the distinct reduced irreducible
  components on the neighbourhood. Each germ is a parameter and hence a nonunit, so
  each component passes through x. Conversely, shrinking away from the finitely many
  components not containing x gives exactly this affine presentation. Prime component
  ideals are intrinsic Mathlib minimal primes, not a second boundary definition.
- `A.ideal W = Ideal.span {∏ a : Fin s, t a}` is exactly the local product equation.
  This asserts the equation on an actual neighbourhood, not merely an equality of
  stalk ideals or an equality of set-theoretic supports.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` and its full quasi-excellent and
  universally catenary definitions.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used through
  `Mathlib.AlgebraicGeometry.Noetherian` and its scheme/affine/stalk instances.
- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`, whose full signature and
  divisorial-chart and dimension docstrings were read.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.

All recorded proof-dependency modules are imported without `public`, except those already
needed publicly by the statement. The finite-proper and proper-composition Mathlib matches
come from the public proper-morphism import. The cotangent and Nakayama Mathlib matches
are exposed by the imported regular-local-ring proof interfaces. There is no import cycle.

Edge cases checked: B empty gives U=M and allows A empty; then `s=0`, the empty family of
minimal primes is the minimal-prime set of the unit ideal, the product is 1, and the empty
prefix is permitted. At a point outside A this same case applies regardless of its local
dimension. A zero-dimensional regular stalk permits `l=[]`, exactly as the parameter
node requires. The empty scheme is excluded only by the input integrality condition,
which already includes nonemptiness in both source and Mathlib. Positive characteristic,
non-finite-type excellent schemes, and Noetherian schemes of unbounded global dimension
are not excluded. No global uniform bound on local parameter lengths is introduced.
A self-intersecting normal-crossings component cannot satisfy the final strict-boundary
criterion; the separate strictification step in the proof is essential.

Searches made:

- `msearch.py` LeanFinder: "An integral excellent Noetherian log regular pair admits a
  proper birational regular resolution with strict normal crossings boundary" returned
  eight unrelated smooth-chart and normalization results, with no matching statement.
- `msearch.py` Loogle: "AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsProper,
  IsRegularSystemOfParameters" returned zero matches (the final side-project identifier
  is unknown to the Mathlib-only search service).
- `msearch.py` Mathlib grep: `log.regular|strict.normal.crossings|birational.*resolution`
  under AlgebraicGeometry returned zero matches.
- Direct `rg` searches of upstream WeilConjectures, the Mathlib source, and side
  `lean/Sheaf` for log regular pairs, strict normal crossings, birational resolutions,
  the item id, and the proposed theorem name found no exact existing statement.
  The upstream item-id search has no match. The side `exists_log_regular_desingularization`
  was opened: it assumes finite type over an algebraically closed field and only gives
  normal crossings. The nodal-pair resolution and field-relative strict-divisor interfaces
  also have different hypotheses and cannot replace this general excellent theorem.
  `dag/lean_names_upstream.json` was included in the proposed-name search.

Source grounding: read the local ILO PDF, physical pp. 88--89 (printed 82--83), for
VII Theorem 4.3, and physical pp. 123--124 (printed 117--118), for VIII 4.1.2--4.1.8 and
Remark 4.2.2(i). The first gives the regular Noetherian birational resolution; the second
supplies permissible strictification and the regular-intersection characterization.
The proof docstring follows the node's complete excellent-Noetherian argument rather
than the published finite-type-over-a-field desingularization statement.

Validation: the prescribed `scompile.py Q46 lem-per-noetherian-log-pair-strict-resolution`
compiled the delivered file as both sandbox and library module (2.6 and 2.5 seconds),
without errors or warnings. Every variable and universe is explicitly bound.
No statement fault or disputed assertion was found.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
