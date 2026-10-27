## Worker report

The module `Sheaf.RingTheory.CohenMonoidSurjectionPrincipalKernel` states
`AddMonoidAlgebra.cohenMonoidSurjection_principalKernel`, with its proof exactly
`by sorry`. No definition or proof is added. The statement and proof plan were read
from the DAG; the cited source was checked in ILO, Exposé VI 1.6(ii), printed p. 70
(PDF page 76), which gives the Cohen model and the relation congruent to p modulo
the monomials and parameters. The principal-kernel refinement is explicitly the
agent argument recorded in the node, rather than a verbatim theorem in ILO.

Hypotheses and objects, clause by clause:

- The coefficient ring is `C : Type u`, `[CommRing C]`, with `hC : IsCohenRing p C`.
  The published predicate includes primality, the DVR domain condition, maximal
  ideal `(p)`, and completeness. `[IsLocalRing C]` supplies the same local structure
  for the existing completed-model API; it adds no mathematical condition to a
  Cohen ring. The residue field k is not used separately by the statement: it is
  C's residue field, already of characteristic p by this predicate.
- The additive monoid is `P : Type v`, `[AddCommMonoid P]`;
  `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` is the recorded
  finite-generation, integrality, and saturation predicate, not a private copy.
  `hsharp` says an invertible element of P is zero, exactly the sharp condition.
- `n r : ℕ` includes n=0. `hr` names r as the rational dimension of the group
  completion, `Module.finrank ℚ (TensorProduct ℤ ℚ (Additive
  (Algebra.GrothendieckGroup (Multiplicative P))))`. Fs ensures this dimension is
  finite, so this is the integral rank stipulated in the node. The equality only
  names r; it does not restrict the allowable monoids.
- `ToricMonoid.Complete C P n` is the already published completion of
  `MvPolynomial (Fin n) (AddMonoidAlgebra C P)` at `(m_C,z^q (q≠0),T_i)`. Cohen's
  `m_C=(p)` makes this precisely B in the node. Its finite-sum polynomial and
  monoid-algebra definitions have the specified monomial multiplication.
- `ToricMonoid.completedChartIdeal C P n` is the published extension J of the
  monomial and variable ideal. N is named by an explicit ideal binder and `hN`
  identifying it with the span of the images of the nonzero monomials alone.
- The target is an arbitrary `S : Type w` with `[CommRing S]`,
  `[IsNoetherianRing S]`, `[IsLocalRing S]`. Mathlib's local-ring class includes
  nontriviality, so the required nonzero clause is present without a redundant
  `[Nontrivial S]`. No completeness, log structure, or presentation is assumed.
- `hdim : ringKrullDim S = ((n+r : ℕ) : WithBot ℕ∞)` is finite dimension n+r.
- `φ` is a ring homomorphism from this B, `[IsLocalHom φ]` expresses locality,
  `hφ` is surjectivity, and `hJ` is `Ideal.map φ J = maximalIdeal S`. Because φ
  is surjective, ideal image agrees with set image, so this is exactly φ(J)=m_S.

Conclusions, clause by clause:

- The first existential gives `j ∈ J` and `φ j = φ (p : B)`.
- The equation for `maximalIdeal (MvPowerSeries (Fin n) C)` states m_D=(p,T_i).
- `∃ e : (B ⧸ N) ≃ₐ[C] MvPowerSeries (Fin n) C` gives the coefficient-preserving
  stratum identification. The following equation fixes every T_i, identifying
  the canonical quotient in the node. N kills precisely the displayed monomials.
- The universal `∀ j ∈ J, φ j = φ p → ...` covers EVERY qualifying lift j, using
  `p-j` explicitly throughout for θ; there is no statement-local let binder.
- Its first conjunct gives `θ-p ∈ J`, and the next gives `RingHom.ker φ = span {θ}`.
- The next three conjuncts give respectively `e(θ)-C(p) ∈ (T_i)`,
  `e(θ) ∈ maximalIdeal D`, and `e(θ) ∉ (maximalIdeal D)^2`.
- The four quotient conjuncts give Noetherianity, locality, integral-domain status
  (including nonzero), and Krull dimension n+r for B/(θ).
- The final existential `eS : (B ⧸ span {θ}) ≃+* S` is constrained by
  `∀ b : B, eS (Ideal.Quotient.mk _ b) = φ b`. This specifies the induced map on
  every element, hence the stated values on all z^q and T_i. `IsLocalHom
  eS.toRingHom` records the local-ring-isomorphism assertion explicitly; the inverse
  of a ring equivalence also reflects units.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, full definition and docstring.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: the recorded fs-log interface;
  its public import `Sheaf.AlgebraicGeometry.LogRegularPair` provides the actual
  `AlgebraicGeometry.IsFineSaturatedMonoid` definition, read in full.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` and `AdicCompletion.of`;
  `Mathlib.RingTheory.AdicCompletion.Algebra` provides its ring/algebra structures.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, and `X`;
  `Mathlib.RingTheory.MvPowerSeries.Inverse` exposes the canonical local-ring instance.
- `Sheaf.RingTheory.CompleteToricModel`: `ToricMonoid.Complete` and
  `ToricMonoid.completedChartIdeal`, owned by `def-trf-complete-toric-model`.
  Their complete definitions and source docstrings were reread for this repair.
  They abbreviate the published completion and completed boundary ideal without
  changing the ring, its algebra structure, or its generators. The definition
  node is added to stmt_deps, as requested by the maintainer's H2 return.
- `Sheaf.RingTheory.LogRegularSaturationNormality` is now a plain, proof-only
  import for `AddMonoidAlgebra.completedLocalModel_normal`; its theorem node is
  not added to stmt_deps. It remains in the unchanged proof_deps.
- Proof-only imports: `Sheaf.RingTheory.FormalMonoidRingDimension`,
  `AddMonoidAlgebra.formalMonoidRing_dimension`, and
  `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`,
  `MvPowerSeries.power_series_field_cohen_regular_complete`.
  `lem-trf-polynomial-power-series-monoid-completion` has no Lean record yet and
  is not used to construct statement data; its future proof import is omitted.

Edge cases checked before writing: for P={0}, the nonzero monomial family is
empty and N=0; for n=0, `Fin n` is empty and the variable ideal is zero; with
both trivial, J=0, the premise forces φ(p)=0, θ=p, S is the residue field, and
all dimensions are zero. A ramified example P=ℕ, n=0, θ=p-z is also covered.
No arbitrary residue field, prime, monoid, or target-ring universe is excluded;
C, P, and S have independent explicit universes u, v, w. No field condition is
imposed on S. No statement fault or STATEMENT-DISPUTED issue was found.

Searches for existing statements (msearch.py, group Q60, this item):

- LeanFinder: “A surjective local homomorphism from the completed monoid algebra
  over a Cohen ring whose boundary ideal maps onto the maximal ideal has principal
  kernel generated by p minus a boundary element”. Eight hits including
  `AdicCompletion.kerProj_surjective`, `kerProj`, Fontaine theta, and completion
  projections; none asserts the principal-kernel or stratum clauses here.
- LeanSearch: “A surjection from a completed monoid algebra over a Cohen ring has
  principal kernel p minus a boundary element”. Eight hits on completion kernel
  projections, algebra generators, and generic quotient equivalences; no match.
- Loogle: `RingHom.ker, Ideal.Quotient.lift, IsLocalHom`: zero hits.
- Mathlib grep: `cohen.*(surj|kernel)|principal.*kernel` in RingTheory: one unrelated
  valuation-subring principal-unit-group hit; no match.
- Project rg: `cohen.*(surj|kernel)|principal.*kernel|CompletedLocalModel|
  localModelBoundaryIdeal` in lean/WeilConjectures and lean/Sheaf. Located and reused
  the model helpers in LogRegularSaturationNormality; no theorem matching this node.
- Exact node-id search in lean/WeilConjectures: no match. Exact proposed declaration
  search in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no clash.

Validation: scompile.py compiled the sandbox and final library module cleanly
(3.9 s and 5.2 s). Initial missing power-series local-instance import and redundant
nontriviality binder were repaired before this clean compile. Every universe and
variable is explicit; no extra linter suppression is used.

## Second reading by Q60

The dispatcher prohibits other agents; this is a separate self-reading of the node
and final file, with the maintainer's independent delivery review still to follow.
I rechecked the Cohen predicate, fs and sharp hypotheses, all completion and
boundary generators, r and finite dimension, the local surjection and its full
boundary image. I checked that existence of a lift is separate from the universal
claim for every lift; that the coefficient-algebra equivalence fixes variables;
that congruence, membership and nonmembership in the square are all present;
and that the hypersurface map agrees with φ on every element and is local.
I checked the final four ring properties and the two empty generating families.
No mismatch remained. In particular, no completeness hypothesis was introduced
on S and the existing completed-model definitions were reused rather than copied.
The only dependency-list addition is now `def-trf-complete-toric-model`, the
already landed definition owner of the model interface.

## Repair of H2 at returned head 0becf4d26e33

The returned delivery incorrectly added the normality theorem node to stmt_deps
solely to obtain its construction helpers. Compared the retained sandbox with the
current main node and reread the landed `def-trf-complete-toric-model` node and its
module. Rebuilt the node copy from current main, retaining all fields outside
stmt_deps and lean, and added only that existing definition node to stmt_deps.
Replaced the public model import with `Sheaf.RingTheory.CompleteToricModel` and
replaced every model and boundary-ideal occurrence in the signature with
`ToricMonoid.Complete C P n` and `ToricMonoid.completedChartIdeal C P n`.
Normality is an explicit plain import, used only by the documented proof plan.
Refreshed lean.statement from the repaired file verbatim. These are transparent
abbreviations of the same objects, so all hypotheses, conclusions and empty cases
checked above remain identical. No S2 reviewer fix is being requested: this worker
repair supplies the corrected statement-dependency list before independent review.

Separate repair self-reading: checked every occurrence of the two model notions,
the model type in N, phi, both quotient equivalences and each ring-property
conclusion; checked J in hJ, the existence clause and the universal lift clause.
The mathematical statement has not changed. The direct theorem dependency was
removed from stmt_deps and retained in proof_deps and as a plain proof import.

Repair validation: scompile.py completed successfully for both the sandbox probe
and final library module, with no errors or warnings (library compile 2.6 s).
A comparison against the current main node confirms that only lean and stmt_deps
change, the sole added dependency is def-trf-complete-toric-model, and proof_deps
is unchanged. The Lean file has maximum line width 94 characters.
