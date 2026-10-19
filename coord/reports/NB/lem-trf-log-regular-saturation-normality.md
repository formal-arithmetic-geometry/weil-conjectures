## Worker report

The module `Sheaf.RingTheory.LogRegularSaturationNormality` states
`AddMonoidAlgebra.completedLocalModel_normal`, with its proof `sorry`. It also gives real
constructions for the ideals and completion explicitly introduced in the node. These four
helpers belong to this node's model construction and are listed in `lean.declarations`;
there is no additional independent notion or new DAG node.

Clause-by-clause correspondence:

- The additive commutative monoid is `(P : Type v) [AddCommMonoid P]`.
  `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` uses the existing
  predicate with only a multiplicative type tag. Its three conjuncts are finite generation,
  injectivity of the canonical Grothendieck-group map (integrality), and root saturation
  inside that same group completion. Thus none is replaced by an unrelated embedding.
- Sharpness is `hsharp : ∀ a b : P, a + b = 0 → a = 0 ∧ b = 0`.
  In a commutative monoid, having an additive inverse is precisely participating in such
  an equation, so this says that zero is the only invertible element.
- `(n : ℕ)` includes zero; `Fin n` indexes exactly the n polynomial variables.
- The finite sums `L[P][t]` are the existing
  `MvPolynomial (Fin n) (AddMonoidAlgebra L P)`. A basis term is
  `MvPolynomial.monomial e (AddMonoidAlgebra.single q c)`; the two existing convolution
  multiplications give exactly the node's `z^q z^q' = z^(q+q')` and variable multiplication.
- `localModelBoundaryIdeal L P n` is the supremum of the ideal spanned by
  `MvPolynomial.C (single q 1)` for `q ≠ 0` and the ideal spanned by all `MvPolynomial.X i`.
  No coefficient maximal ideal is included here.
- `localModelCompletionIdeal L P n` adds the image of `IsLocalRing.maximalIdeal L`
  under the canonical coefficient algebra map. `CompletedLocalModel L P n` is exactly
  `AdicCompletion` of that ideal and that polynomial ring, hence the node's `B_L(P,n)`.
- `completedLocalModelBoundaryIdeal` extends only the monomial-and-variable ideal along
  the canonical polynomial-to-completion algebra map; it is exactly `(z^q,t)B_C(P,n)`.
- Case (i) is the first conjunct, quantified over every `(k : Type u) [Field k]`.
  No characteristic or perfectness condition is imposed.
- Case (ii) is the second conjunct, quantified over all commutative local rings `C`,
  all `p : ℕ` with `IsCohenRing p C`, and all `θ` in their completed model. The existing
  Cohen predicate includes `Nat.Prime p`, domain, discrete valuation, maximal ideal
  `(p)`, and `(p)`-adic completeness. The explicit local-ring instance is inherent in
  the Cohen hypothesis and permits the maximal-ideal notation; it imposes no additional
  mathematical restriction. There is no restriction on the residue field.
- The exact parameter condition is
  `θ - (p : CompletedLocalModel C P n) ∈ completedLocalModelBoundaryIdeal C P n`.
  The ring in the conclusion is the actual quotient by `Ideal.span {θ}`.
- Both cases conclude `IsDomain ... ∧ IsIntegrallyClosed ...` as prescribed by the
  normal-ring dependency. The former includes nonzeroness; the latter uses the existing
  `FractionRing` and says integral closure in that fraction field. Stating the two cases
  as a conjunction gives every allowed R without introducing an arbitrary ring or map.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, with its imported
  `Sheaf.AlgebraicGeometry.LogRegularPair`: `AlgebraicGeometry.IsFineSaturatedMonoid`.
  Read both the fs-log node's statement and the predicate's complete signature/docstring.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`; its commutative-ring and
  algebra structures come from `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`. The recorded module was absent
  locally; read the live full source using `scompile.py --source` rather than defining it.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with the prescribed `IsDomain` conjunction for normal domains.

Proof imports include the recorded support-projection, power-series regularity,
regular-local hypersurface, regular-local localization, and regular-ring normality
modules. Their source declarations and proof docstrings were read. The orthant embedding
node has no recorded Lean declaration, so its import is omitted; the theorem's proof
remains `sorry`, and the docstring names that proof prerequisite explicitly. All six DAG
proof steps, including ideal identification, the constant-coefficient check, descent to
the quotient, ambient normality, and the retraction fraction argument, are in the docstring.

Source check: read ILO Exposé VI 1.6 directly with `pdftotext -layout`: its sharp fs P,
field model, Cohen model, and congruence of f to p modulo P minus zero and the variables
agree with the node and these constructions. Normality is the DAG's agent-origin proof;
no result is attributed to the unavailable Kato text.

Edge cases checked before drafting and again against the final signature:

- `P={0}`: the nonzero-monoid generator set is empty. There is no positivity or nonempty
  generator hypothesis. Sharpness and the fs predicate include this case.
- `n=0`: `Fin 0` is empty, so the variable ideal vanishes and no variable is selected.
- Both together: case (i) is the completion of a field at zero, hence the field; in
  case (ii) the boundary ideal is zero, forcing θ=p and giving C/pC after completeness.
- Characteristic zero and positive-characteristic fields are both included, as are
  arbitrary imperfect Cohen residue fields. Zero coefficient rings cannot satisfy the
  field or Cohen hypotheses; no contradictory conclusion for the zero ring is asserted.
- Coefficient and monoid universes are independent (`u`, `v`); all are explicitly bound.

Searches (the prescribed msearch wrapper records exact raw results in searches.jsonl):

- LeanFinder: "The completion of a sharp saturated finitely generated monoid algebra
  over a field is a normal domain, as is its Cohen ring quotient by p plus nonconstant
  terms". Eight hits, including `PreTilt.isDomain`, `Tilt`, and Dedekind adic completions;
  their returned signatures concern different rings and do not state this result.
- Loogle: `IsIntegrallyClosed, AddMonoidAlgebra`: zero hits.
- LeanSearch: "Normality of completed saturated monoid algebras over fields and Cohen
  rings": eight hits for ordinary power series and the generic completion algebra
  structures; no saturated-monoid normality theorem.
- Mathlib grep through msearch:
  `IsIntegrallyClosed.*MonoidAlgebra|MonoidAlgebra.*IsIntegrallyClosed|saturated.*normal`:
  zero hits.
- `rg` in the upstream WeilConjectures tree for the item id, `IsFineSaturatedMonoid`,
  `IsCohenRing`, and the proposed construction/theorem names: no matching definition or
  theorem there. CohenRing was instead read through the live source wrapper.
- `rg` in `lean/Sheaf`: found the existing `IsFineSaturatedMonoid` in LogRegularPair and
  the support-projection proof prerequisite; no theorem of normality or existing model
  completion/ideal construction. The upstream declaration-name index and Mathlib/source
  searches contain none of the proposed new full names.

No statement correction, disputed statement, dependency module, or new node is needed.
The initial compile required `noncomputable` annotations on the three ideal definitions
because their Mathlib monoid-algebra ring structures are noncomputable; these annotations
were added without changing any construction or mathematical statement.

## Second reading by NB

Author's separate self-check, not an independent review (the dispatcher brief forbids
starting another agent; independent review belongs to the maintainer). Reopened the node
and the module and traced the fs predicate down to its canonical group-completion
conditions. Checked that the boundary ideal excludes the coefficient maximal ideal,
whereas the completion ideal includes it; this distinction preserves θ-p's exact
congruence. Checked that the quotient is by θ, not θ-p. Checked both domain and integral
closure conclusions in each conjunct. The multiplicative tag preserves addition and zero
as multiplication and one, and the sharpness formula is equivalent to the source's
unit condition. Checked that no nonempty generator list, nonzero n, perfect residue field,
or extra regularity of P is assumed. All source clauses match; no mathematical change
was needed during this second reading. The constructions contain no sorry; the only
postponed proof is the named theorem matching this DAG node.
