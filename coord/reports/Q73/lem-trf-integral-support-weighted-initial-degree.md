## Worker report

Item: `lem-trf-integral-support-weighted-initial-degree`, group Q73, stage 2.
The delivery states `AddMonoidAlgebra.not_isIntegralElem_of_negative_support_weight`
in `Sheaf.RingTheory.IntegralSupportWeightedInitialDegree`. Its only proof is `sorry`.
No definitions, helper declarations, dependency repairs, or statement changes are needed.
The sandbox initially contained only dispatcher `.brief*` markers and no delivery artifacts.

Clause-by-clause correspondence:

- A field k is `{k : Type u} [Field k]`.
- A finitely generated torsion-free abelian group H is `{H : Type v}
  [AddCommGroup H] [AddGroup.FG H] [IsAddTorsionFree H]`. The last class requires
  injectivity of every positive natural scalar multiplication, equivalent for a group to
  the node's torsion-free condition. The independent coefficient/group universes impose
  no size restriction.
- The additive submonoid P of H is `P : AddSubmonoid H`, with no finiteness, saturation,
  generation, sharpness, or properness hypothesis on P.
- The integer group homomorphism is `w : H →+ ℤ`. Nonnegativity at every element of P
  is `(hw : ∀ p ∈ P, 0 ≤ w p)`.
- The finite formal sum x is `x : AddMonoidAlgebra k H`. Mathlib's data is a finitely
  supported coefficient function `x.coeff : H →₀ k`. Thus `x.coeff.support` is the actual
  finite support S, not an arbitrarily enlarged set with possibly zero coefficients.
  The nonzero hypothesis is `(hx : x ≠ 0)`.
- The negative exponent hypothesis is `(hneg : ∃ g ∈ x.coeff.support, w g < 0)`.
- The conclusion is `¬ (AddMonoidAlgebra.mapDomainRingHom k P.subtype).IsIntegralElem x`.
  `P.subtype : P →+ H` is the canonical inclusion, and `mapDomainRingHom` sends a monomial
  at p to the same monomial at its image. `RingHom.IsIntegralElem` is precisely existence
  of a monic polynomial over `AddMonoidAlgebra k P` whose evaluation through this map at
  x vanishes. This is integrality over k[P] with the specified embedding, not integrality
  for an arbitrary algebra structure. It avoids adding an algebra instance binder.

Dependency declarations read and used:

- `def-trf-fine-fan-blowup`: recorded module `Sheaf.AlgebraicGeometry.FineFanBlowup`,
  main declaration `AlgebraicGeometry.FineFan.SmoothFunctorialDesingularization` and its
  full signature/docstring were read, along with `IsFine`, `IsSharp`, `saturation` and
  its imports. The dependency supplies the additive monoid conventions; the item needs
  no fan, blowup or tower object. The module is imported to retain this DAG dependency;
  its unrelated fan structure is not an extra hypothesis. Standard additive monoid
  algebra data comes directly from Mathlib, so no fan-specific private copy is made.
- Mathlib's `AddMonoidAlgebra`, `AddMonoidAlgebra.mapDomainRingHom`,
  `AddSubmonoid.subtype`, `AddGroup.FG`, `IsAddTorsionFree`, and
  `RingHom.IsIntegralElem` supply all actual statement data. Read MapDomain.lean:289--302,
  Defs.lean (monoid algebra data), Finiteness.lean:395--410, Algebra/Group/Defs.lean:787--792,
  and IntegralClosure/IsIntegral/Defs.lean:35--54.
- Proof dependency `lem-trf-monoid-algebra-domain-fraction` has no Lean record or Mathlib
  match on the base, so there is no module to import yet. Its full DAG statement and proof
  were read. The theorem docstring records exactly how the signed generators of H supply
  its finite-generation/generation hypotheses. It is needed only in the future proof,
  not to form any object in this statement. No replacement theorem was introduced.

Source read: ILO Exposé VIII, printed p.104 (PDF page 110), Lemma 3.2.9, its proof via
normality and the common dense group-algebra torus, and the first proof paragraph of
Lemma 3.2.12 with k[P] inside k[Pgp]. The explicit negative-initial-weight argument is
agent-written in this node, as its source/proof_origin say; the docstring includes all
four DAG proof steps without attributing that expansion verbatim to ILO.

Edge cases checked before writing:

- x = 0 has empty actual support, and is explicitly excluded as the node says.
- H trivial or w = 0 makes the negative-support hypothesis impossible. No nontriviality
  hypothesis on H, nonzero hypothesis on w, or injectivity of w was added.
- P = {0} is allowed. P = H forces w = 0 by nonnegativity at p and -p, so the same case
  is vacuous. An arbitrary infinitely generated P is still permitted.
- With H = ℤ, P = ℕ inside ℤ and w the identity, the monomial of exponent -1 fits the
  hypotheses and is correctly asserted nonintegral over k[P].
- For H = ℤ² and projection w, distinct support exponents may share the least weight.
  The initial component is a sum, rather than one chosen monomial; the domain argument
  ensures its powers do not vanish. No injective-weight assumption was smuggled in.
- Positive-characteristic fields are allowed: cancellation may delete exponents but
  cannot produce exponents below the bound, and a nonzero power in the group-algebra
  domain remains nonzero. The degree-zero monic polynomial is 1 and cannot vanish.

Searches made during this continuation (all via the authorized msearch.py Q73/item wrapper
except the named direct rg reads):

- LeanSearch: `An element of a torsion free abelian group algebra with negative support
  weight is not integral over a nonnegative weight submonoid algebra`.
  OK, 8 hits. Returned torsion-free classes/modules, HahnModule torsion freeness,
  subalgebra torsion freeness, and MonoidAlgebra.instIsTorsionFree; none is this assertion.
- LeanFinder: `A negative support weight obstructs integrality over a submonoid algebra`.
  OK, 8 hits: Finsupp.NonTorsionWeight, MvPolynomial.NonTorsionWeight,
  IsLocalization.coeffIntegerNormalization_mem_support, IsAlmostIntegral,
  Finsupp.NonTorsionWeight.ne_zero, Finsupp.nonTorsionWeight_of,
  MvPolynomial.nonTorsionWeight_of, and a RootPairing inequality. These describe other
  weight or localization notions and do not state the group-algebra integral obstruction.
- Loogle: `AddMonoidAlgebra, RingHom.IsIntegralElem`: OK, 0 hits.
- Mathlib grep: `IsIntegral|infDegree_mul|le_inf_support_mul` in Algebra/MonoidAlgebra:
  OK, 4 hits, all in Degree.lean. Read `le_infDegree_mul` at 637--640; it is only the
  lower bound on product degree and does not state the nonintegrality obstruction.
- Direct rg of upstream WeilConjectures and side lean/Sheaf for AddMonoidAlgebra,
  MonoidAlgebra, support-weight and integrality terms found toric local-model and
  representation declarations but no matching statement. Exact item-id search in upstream
  WeilConjectures and dag/lean_names_upstream.json gave no hits. The proposed declaration
  name was also searched in Mathlib, upstream, side Lean and lean_names_upstream.json:
  no hits. The item already records extensive prior logged searches with the same verdict.

Compilation: the initial new-style `module` header failed because the recorded fan module
uses legacy imports (`cannot import non-module ... from module`). Removed that header and
used ordinary imports, consistently with the dependency module. Re-ran the required
scompile.py wrapper: sandbox clean in 3.4 s and library-identity compile clean in 3.3 s,
with no errors or warnings. Every variable and universe is explicit; autoImplicit is false.

No STATEMENT-DISPUTED issue or source-based correction is needed.

## Second reading by Q73

This is the dispatched worker's separate second pass, not an independent worker; the brief
explicitly prohibits starting other agents and delegates independent review to the maintainer.
Reopened the node and final file and checked every binder: field, abelian group, finite
generation, torsion freeness, arbitrary additive submonoid, integer additive homomorphism,
nonnegative weights on precisely P, nonzero group-algebra element, and a negative exponent
in its actual coefficient support. All are present with the same quantifier order/content.
The conclusion uses the canonical inclusion P.subtype, and the definition of IsIntegralElem
uses monic polynomial evaluation over exactly k[P]. No arbitrary algebra/map binder, chosen
minimum, support witness, or ordered-group structure has become an extra hypothesis.
The docstring carries the four proof steps, including the signed-generator application,
component-of-powers calculation, positive-degree argument, and vanishing of lower terms.
The only mismatch found on this second pass was the incompatible file header, already
corrected before the successful compile; no mathematical mismatch was found. The node JSON
is copied unchanged except for lean, whose statement is the file's verbatim signature.
