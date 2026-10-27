## Worker report

Repair of returned immutable head `66e1dea814f7`. The return said that
`def-sfb-epp-weak-solution` had meanwhile been created on `sheaf-dag` by another delivery.
The current main node and its full Lean declaration were read. Q139's landed module
`Sheaf.RingTheory.EppWeakSolution` defines
`IsDiscreteValuationRing.IsEppWeakSolution` with exactly the finite-extension and
normalized-branch criterion needed here. The duplicate definition node and module
have been removed from this sandbox delivery. Neither landed file is modified.
The item cites and imports that existing definition instead.

The returned theorem used a `HasEppWeakSolution` helper in its duplicate module.
That helper is not in the landed API. Its body is now written directly as the conclusion:
`∃ (N : Type (max u v w x z)) (_ : Field N) (_ : Algebra K N)
(_ : Algebra A N) (_ : IsScalarTower A K N), IsEppWeakSolution A B K L N`.
Thus the repair changes the delivered Lean and its dependencies, rather than merely
rebasing or re-pushing the old packet. The new packet contains only the item's module,
item node and this report. It creates no nodes and repairs no dependency node.

The item's current-main statement, proof and proof_deps were compared with the retained
returned packet and agree. They remain unchanged. The node copy was refreshed from
current main and changed only in `lean` and by adding the now-landed
`def-sfb-epp-weak-solution` to `stmt_deps`. The theorem's docstring retains all seven
steps of the original proof. Its entire proof is `sorry`; no theorem is proved here.

Sources read: Stacks Project, `more-algebra.tex`, Tag 09EM (remark-construction),
Tag 09EN (definition-solution), Tag 09ET (lemma-solution-after-strict-henselization),
and the strict-residue and completion paragraphs of Tag 09F9 (theorem-epp), including
its use of 09EJ and 09ES. The current node records this as an auxiliary historical
source result, not a statement in an older blueprint snapshot.

Hypothesis and clause correspondence:

- `A`, `B` carry `CommRing`, `IsDomain` and `IsDiscreteValuationRing`.
  `Algebra A B` specifies the given ring map; `hinj` is its injectivity and
  `IsLocalHom (algebraMap A B)` is locality, equivalent to maximal-ideal contraction.
- `K`, `L` have `Field`, the specified ring algebra structures and `IsFractionRing`.
  `Algebra K L` with `IsScalarTower A B L` and `IsScalarTower A K L` specifies
  the induced compatible fraction-field inclusion.
- `p : ℕ`, `hp : 0 < p` and `[CharP (IsLocalRing.ResidueField A) p]` express
  positive residue characteristic. `hperfect` is surjectivity of the pth-power map.
- `hcore` quantifies every upper residue element admitting p^n-th roots for every
  natural n and requires `IsSeparable (ResidueField A) a`. Mathlib's separability
  predicate includes algebraicity: a nonalgebraic element has zero minimal
  polynomial, which is not separable. The residue algebra is the canonical one
  induced by the original local map.
- `π` and `hπ : maximalIdeal A = Ideal.span {π}` specify the fixed uniformizer.
- The outer existential supplies DVRs `A'`, `B'` and the three new algebra maps.
  `Algebra A B'` and the two scalar towers through `B` and `A'` say the square
  commutes. The three `IsLocalHom` binders and first three conjuncts assert that
  all three new maps are local and injective.
- `IsAdicComplete (maximalIdeal A') A'` and the analogous condition for `B'`
  give precisely maximal-ideal completeness. `maximalIdeal A' =
  Ideal.span {algebraMap A A' π}` preserves this same uniformizer.
- `IsAlgClosure (ResidueField A) (ResidueField A')` says the new lower residue
  is algebraic over the old one and algebraically closed, with its induced map.
- For each `a : ResidueField B'`, the biconditional identifies membership in the
  range of the canonical lower residue map with existence of p^n-th roots for
  every n. It states equality of the subfields inside the upper residue.
- The inner existential names actual fraction fields `K'`, `L'` of `A'`, `B'`
  with compatible algebra maps; it does not supply or assume a weak solution.
- For every compatible field extension `H/K'`,
  `IsEppWeakSolution A' B' K' L' H` is the landed finite weak-solution predicate.
  Its body is the reduced tensor quotient by its nilradical, both actual integral
  closures, and the canonical restriction of `h ↦ 1 ⊗ h` followed by reduction.
  For every maximal upper ideal q it requires maximal contraction, a DVR for each
  of the two localizations, and equality of the mapped ideals in the upper
  localization. `Module.Finite K' H` is the finite-dimensional condition.
- `CharP K p → ...` imposes the compositum condition only in equal characteristic p.
  `E : IntermediateField K' H` is finite separable, `r : ℕ` and `t : H` satisfy
  the specified root equation for the image of the original π, and
  `E ⊔ IntermediateField.adjoin K' {t} = ⊤` says these two subfields generate H.
  In characteristic zero of K the implication requires no additional condition.
- The explicit final existential above gives a finite weak solution `N/K` for the
  original map using the same landed predicate. The entire square lies outside
  the implication about H; its existence is unconditional on finding a solution.

The landed predicate is stated for compatible rings and fields generally. Applying
it to the DVRs and actual fraction fields already bound in this theorem is exactly
its specified specialization, with no new assumption. Its canonical normalization
map has the same body as the returned predicate's `eppNormalizationMap` construction;
finite dimensionality, maximal contractions, both DVR clauses and ideal equality
are identical. The theorem no longer imports `EppEssentiallyFiniteTypeTraits` through
a private copy of the weak-solution definition.

Dependency declarations read and used:

- `Sheaf.RingTheory.EppWeakSolution`:
  `IsDiscreteValuationRing.IsEppWeakSolution`. The landed definition's full
  signature, body and source docstring were read during this repair.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  uniformizers mean `maximalIdeal = Ideal.span {π}` by
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`. The Mathlib proof
  dependency `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` is available
  from this same module.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with compatible scalar towers.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, used by
  the landed weak-solution predicate.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, used by that predicate.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, used
  for both localized DVRs in that predicate.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (now imported
  explicitly since the removed helper module no longer supplies that import).
- `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing`, now imported
  explicitly for the same reason.
- `Mathlib.FieldTheory.Separable`: `IsSeparable`, `Algebra.IsSeparable`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: the canonical residue algebra.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`: `IntermediateField.adjoin`.

The following currently recorded proof modules were read in full and imported
without `public` for the future proof: `Sheaf.RingTheory.PrincipalRegularLocalCompletionDVR`
(`AdicCompletion.principalRegularLocalCompletion_dvr`),
`Sheaf.RingTheory.DvrStrictResidueSquare`
(`IsDiscreteValuationRing.exists_strict_residue_square`), and
`Sheaf.RingTheory.DvrCompletionExtensionApproximation`
(`IsDiscreteValuationRing.exists_finite_extension_tensor_equiv`). The latter two
are newly available since the returned delivery. The index-one base-change and
algebraic-normalization-structure proof nodes still have no recorded Lean modules
in the current read clone, so are not imported. No proof prerequisite is assumed
as a binder of the theorem.

Edge cases checked:

- DVRs exclude fields and the zero ring; the fixed uniformizer cannot be zero or
  a unit. The image-uniformizer conclusion adds no initial nonzero assumption.
- `p = 0` is excluded as in the node. `p = 1` is inconsistent with field
  characteristic; no additional primality assumption is imposed.
- `n = 0` in the perfect-core intersection adds no restriction, since p^0 = 1.
- Identity maps, trivial finite extensions and `r = 0` are allowed. No positive
  extension degree or strict field inclusion is required.
- Mixed characteristic remains allowed and requires no compositum condition;
  equal characteristic p retains exactly the prescribed uniformizer-root condition.
- Original DVRs need not be complete or henselian. The original upper residue
  need not be perfect or algebraic over the lower one.
- All maximal normalized upper branches are quantified, including both localized
  DVR assertions. No branch choice, residue separability conclusion or stability
  under further extensions is imposed by weak solutions.
- Input universes u, v, w, x are independent. The output DVRs and fraction fields
  live in their maximum; H and the final witness N may also use z. Thus the
  extension quantifier cannot become vacuous through an undersized universe.
- The square still exists independently of a supplied weak solution.

Searches for the original submission (recorded in the retained `searches.jsonl`):
LeanFinder queried the strict-residue/completion reduction and returned eight
unramified/ramification API hits; Loogle `IsDiscreteValuationRing, IsAdicComplete`
returned no hits; Mathlib grep `weakSolution|WeakSolution|Epp|perfectCore` in
RingTheory returned four incidental `ePp` variable hits. LeanSearch for completion
descent returned eight valuation/completion hits. Searches for a weak-solution
predicate returned ramification-index and unramifiedness APIs, which do not state
that predicate. Project/source rg and blueprint search then found no such predicate.
Those were historical search results before the parallel landing, not claims about
current main. This repair checks the newly landed node and reads its module directly;
that exact shared definition is now used. No replacement definition is introduced.

No statement correction, node fault or STATEMENT-DISPUTED flag is needed. Every
variable and universe is explicitly bound, `autoImplicit` is false, and no diagnostic
commands remain. The prescribed single-file server compile, dry run and delivery
validate the repaired packet against the current published library.

## Repair of return

The sole returned point was the duplicate new-node ID `def-sfb-epp-weak-solution`.
It is repaired by removing both duplicate sandbox files, retaining the shared import,
expanding the missing existential helper directly in the theorem's conclusion, and
refreshing the item record against current main. This packet modifies no shared
weak-solution declaration and creates no definition nodes. The mathematical item
statement, its original assumptions and every clause remain unchanged.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
