## Worker report

The module `Sheaf.RingTheory.RationalNodalCompletionAlgebra` states
`Algebra.rational_nodal_completion_algebra`, with a single `sorry` and no definitions.
The repository is read-only; all authored files are in this item's prescribed sandbox.
Only `lean` changes in the node copy. No statement correction, new node, or dependency
repair is needed.

The source was read directly in `literature/stacks-project/curves.tex`,
`lemma-nodal-algebraic` (Tag 0C49), and `varieties.tex`,
`lemma-complete-local-ring-structure-as-algebra` (Tag 0C52). The former constructs the
continuous coefficient-compatible binary quadratic presentation; the latter supplies the
coefficient section when the residue extension is separable. The module's docstring
retains all five steps of the node's accepted proof, including the two characteristic-free
factorizations and the inverse formal substitutions.

For readability below, A means `Localization.AtPrime p`, m means
`IsLocalRing.maximalIdeal A`, C means `AdicCompletion m A`, T means
`MvPowerSeries (Fin 2) k`, I means `Ideal.span {X 0 * X 1}`, and n means
`Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → T))`. These are report abbreviations;
the Lean signature writes the constructions out using the dependency declarations.

Hypothesis and clause correspondence:

- An algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A finitely generated k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]` and
  `hS : (algebraMap k S).FiniteType`. This uses the dependency's recorded
  `RingHom.FiniteType`, with the specified structural homomorphism.
- A maximal ideal p: `(p : Ideal S) [p.IsMaximal]`; its primality is inferred.
- The structure map k to S/p is an isomorphism:
  `hp : Function.Bijective (algebraMap k (S ⧸ p))`. Bijectivity of this ring map is
  exactly existence of an isomorphism having this prescribed forward map, without
  choosing an unrelated residue-field identification.
- A = S_p: every occurrence uses `Localization.AtPrime p`, not an arbitrary local ring.
- m = pA: `IsLocalRing.maximalIdeal (Localization.AtPrime p)` is precisely the extension
  of p under localization at p (Mathlib's localization-at-prime interface).
- The completion, its inverse-limit construction, and induced coefficient structure:
  `AdicCompletion m A` with its existing `CommRing` and `Algebra k` instances.
  `AdicCompletion.algebraMap_apply` identifies its structural map with completion of the
  structural map k to A. Mathlib indexes also at zero, where the quotient is the zero
  ring, so including that term does not change the inverse limit over positive powers.
- The assumed abstract ring isomorphism: `hnode : Nonempty (C ≃+* (T ⧸ I))`.
  No linearity or compatibility with scalars is assumed.
- The coefficient-compatible complete local isomorphism:
  the first existential supplies `e : C ≃ₐ[k] (T ⧸ I)`.
  Both rings are the stated complete local rings, so an algebra equivalence gives an
  isomorphism of complete local algebras. Locality is intrinsic to a ring isomorphism.
- Continuity in both directions: the two `@Continuous` clauses use e and `e.symm`
  respectively, and explicitly specify `(m.map (algebraMap A C)).adicTopology` on C
  and `(n.map (Ideal.Quotient.mk I)).adicTopology` on the quotient. These ideals are
  the respective maximal ideals. The first identity is
  `AdicCompletion.maximalIdeal_eq_map` (S is Noetherian by finite type over a field,
  and its localization is Noetherian); the second follows from the power-series
  maximal-ideal description and the surjective quotient map. Using the explicitly
  extended ideals avoids requiring derived Noetherian/local-ring instances as extra
  hypotheses. `Ideal.adicTopology` has all ideal powers as its zero-neighborhood basis.
- The equivalent quotient presentation: the second existential supplies
  `π : T →ₐ[k] C`, `Function.Surjective π`, and `RingHom.ker π.toRingHom = I`.
  It asserts this formulation alongside the isomorphism formulation, as the node's
  final proof step does. No construction has been replaced by an arbitrary input map.
- Continuity of π: its `@Continuous` clause gives T the n-adic topology and C the
  same extended-maximal-ideal topology as above.
- Constants are sent to the given structural images: the final clause is
  `∀ c : k, π (MvPowerSeries.C c) = algebraMap k C c`. This is written explicitly
  because the node explicitly specifies restriction to constants.
- No dimension hypothesis on S occurs. No characteristic hypothesis occurs.

Statement dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed field
  clause of def-weil-algebraic-closure's Mathlib match; its record also names
  `AlgebraicClosure` and `IsAlgClosure`, not needed for an already closed field).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`, its ring
  and scalar structures, and `AdicCompletion.algebraMap_apply`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`.
- `Mathlib.Algebra.Algebra.Hom` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `AlgHom`, `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mk`, and `Ideal.Quotient.mkₐ` (the last for the documented proof).
- `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`: `Ideal.adicTopology`, used
  directly to specify the node's topology without defining a duplicate notion.

All recorded proof dependency modules are imported, with no `public` on those imports:

- `Sheaf.RingTheory.SeparableClosedPointFormalPresentation`:
  `Algebra.separable_closed_point_formal_presentation`.
- `Sheaf.TraceFormula.FormalJacobianQuadraticCriterion`:
  `MvPowerSeries.formal_jacobian_quadratic_criterion`.
- `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`:
  `MvPowerSeries.power_series_field_cohen_regular_complete`.
- `WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete`:
  `MvPowerSeries.exists_ringHom_of_isAdicComplete`.

The remaining proof dependencies (algebraic closure and algebra-hom quotient) are
already among the public statement imports. The dependency declarations' complete
signatures and source/proof docstrings were read, not inferred from their names.

Edge cases checked before drafting:

- Characteristic 2 is included: the split form has discriminant 1 and the stated
  factorization never divides by 2. A nonzero determinant, not odd characteristic,
  is the coordinate-change condition.
- Disconnected S, components away from p, and arbitrary global dimension of S are
  allowed. The hypotheses and conclusions concern only localization at p.
- If S is the zero ring there is no maximal ideal p, so it cannot supply the required
  input; if A is a field, its completion cannot meet the split-node ring-isomorphism
  assumption. No excluded case is inserted as a new hypothesis.
- Both variables and their product are present literally; the quotient is the node,
  not the full series ring, either branch, its normalization, or a non-split quadratic.
- The field and algebra universes u and v are independent and explicitly declared.
  No extension-field test quantifiers or universe equalities are imposed.
- The source field has no ambient topology in the signature; adic topologies are
  specified explicitly, avoiding the coefficientwise topology on formal power series.

Searches for an existing statement (2026-10-24):

1. `msearch.py ... leanfinder`, query: "An abstract ring isomorphism of a rational
   completed local algebra to k[[u,v]]/(uv) can be replaced by a continuous coefficient
   preserving algebra isomorphism". Eight hits, including
   `LaurentSeries.powerSeriesAlgEquiv`, `LaurentSeries.ratfuncAdicComplRingEquiv`,
   and `PowerSeries.algEquivQuotientWeierstrassDistinguished`; none states coefficient
   rectification for a rational nodal completion.
2. `msearch.py ... loogle 'MvPowerSeries, AlgEquiv'`: twelve hits, including
   `MvPowerSeries.renameEquiv`, `isEmptyEquiv`, `optionEquivLeft`, and `finSuccEquiv`.
   These are variable reindexing or series decompositions, not this implication.
3. `msearch.py ... grep
   'nodal|ordinary.double|nondegenerate.*quadratic|quadratic.*hypersurface' RingTheory`:
   zero Mathlib hits.
4. `msearch.py ... leansearch`, query: "A rational nodal completed local ring over an
   algebraically closed field has a coefficient preserving isomorphism to the formal
   power series quotient by x times y". Eight hits, chiefly Weierstrass quotient and
   Laurent-series equivalences; no exact match.
5. `rg -n 'rational.nodal.completion|coefficient.*split.node|nodal.*[Cc]omplet'` across
   `lean/WeilConjectures` and `lean/Sheaf`, and `grep -rn` of the item id in
   `lean/WeilConjectures`: no existing realization of this item. Related Sheaf results
   include `MvPowerSeries.nodal_coefficient_straightening` and the private
   `scalar_nodal_completion` in `TraceFormula/NodalSubcurveBoundary.lean`. The former
   rectifies a coefficient section already on the standard node; the latter uses an
   arbitrary Noetherian local ring and gives only a scalar-compatible ring equivalence,
   has no continuous surjection conclusion, and is private. Neither is this exact node.
   Both were opened and read. Existing nodal quotient definitions were also inspected;
   this delivery defines no second nodal quotient, and uses Mathlib's quotient directly.
6. `rg -n 'rational_nodal_completion_algebra'` in both Lean trees and
   `dag/lean_names_upstream.json`: no name collision.

Validation: the prescribed `scompile.py Q16 lem-trf-rational-nodal-completion-algebra`
compiled both sandbox and library forms successfully (1.7 s and 5.6 s), with no errors
or warnings. The only proof is the named theorem's `sorry`. No definitions contain
postponed data. The file has no line over 100 characters and sets `autoImplicit false`.

## Second reading by Q16

The dispatcher expressly forbids starting another agent. This is a second pass by the
same worker, not a claim of independent authorship; independent review remains with the
maintainer, as the assignment specifies.

Reopened the node and final module and compared every hypothesis and clause. `hS` uses
the recorded finite-type ring-map interface, `hp` is about the specified structural map
on the quotient S/p, and `hnode` remains a plain ring equivalence. The conclusion uses
the induced k-algebra action on the actual completion, rather than the one transported
by `hnode`. The first existential gives both directional continuity clauses, and the
second gives every requested feature of π, including constants. Checked the source and
the completion/quotient maximal-ideal identifications to confirm the displayed adic
topologies are exactly the node's. No missing hypothesis, dropped conclusion, additional
dimension bound, characteristic restriction, or duplicate construction was found.
No changes were needed in this pass. No STATEMENT-DISPUTED issue was found.
