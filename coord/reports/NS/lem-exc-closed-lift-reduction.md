## Worker report

No new module: the exact statement already exists as
`Algebra.ClosedLift.bijective_reduction`, in
`WeilConjectures/RingTheory/ProEtale/ClosedLift.lean`, lines 167–172
(branch slopmaster2). Its docstring explicitly names this blueprint node.
Only the item's `lean` field changes. The existing proof is `sorry`;
this records a statement, not a proof completion.

Hypothesis and conclusion correspondence:

- The base ring is `(A : Type u) [CommRing A]`; the ideal is `(I : Ideal A)`.
- The input algebra is `(C : Type u) [CommRing C] [Algebra (A ⧸ I) C]`.
  `[Algebra A C] [IsScalarTower A (A ⧸ I) C]` express exactly the induced
  A-algebra structure, rather than an extra geometric hypothesis. Every
  quotient algebra admits this compatible structure.
- Its assumed ind-etaleness is `[Algebra.IndEtale (A ⧸ I) C]`.
- The lift is the same `Algebra.ClosedLift A C` used by the dependency node.
  It is the colimit of the small etale presentation diagram, not another lift.
- The specified map is `Algebra.ClosedLift.reduction A C I`, with source
  `ClosedLift A C ⧸ I.map (algebraMap A (ClosedLift A C))` and target `C`.
  Its definition is `Ideal.Quotient.lift` of `toAlgHom`, using
  `map_le_ker_toAlgHom`. Thus it is the specified quotient map of the node.
- The sole conclusion is `Function.Bijective (reduction A C I)`.
  A bijective ring homomorphism is an isomorphism (its inverse preserves
  addition, multiplication and the unit), so this says exactly the node's
  conclusion about that map, not merely existence of an unrelated isomorphism.

Dependency declarations read:

- `Sheaf.RingTheory.ProEtale.ClosedLiftMap`, `Algebra.ClosedLift.map`:
  its public import reuses upstream `Index`, `diagram`, `ClosedLift`, and
  `toAlgHom`. Read their full definitions in
  `WeilConjectures.RingTheory.ProEtale.ClosedLift`. The upstream model uses
  relation ideals rather than redundant finite generating lists; the recorded
  dependency explains their equivalence since etale algebras are finitely
  presented. The recorded postcomposition map is not needed by this theorem.
- `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes `Algebra.IndEtale`
  from `WeilConjectures.RingTheory.ProEtale.IndEtale`. Read its class signature:
  a small filtered colimit presentation with etale terms, which includes
  finite presentation. The dependency's principal ind-Zariski and weakly
  etale clauses do not occur in this statement.

Source read: the node's full blueprint page, and Stacks Project
`proetale.tex`, lemma-lift-ind-etale (Tag 097P), including the construction,
filteredness, and reduction proof. These assume an arbitrary ideal and an
ind-etale quotient algebra, exactly as the existing Lean theorem does.
The node's five proof steps remain unchanged; no new declaration or import
is needed under the existing-declaration rule.

Edge cases checked: arbitrary ideals, including zero and unit ideals; zero
rings and zero target algebras; all characteristics. No nontriviality,
nilpotence, proper-ideal or characteristic hypothesis occurs. The common
universe u is the upstream definition's universe convention and can be
chosen large enough for both rings; the filtered presentation's index is
in that same universe, so no smaller test universe is imposed.

Searches made:

- `msearch.py ... leanfinder` query: "The canonical reduction of the universal
  ind etale lift modulo the base ideal is a bijective ring homomorphism".
  Eight Mathlib hits, including `StandardEtalePresentation.lift_bijective`
  and formal-etale nilpotent-quotient results; none is this theorem.
- `msearch.py ... loogle` query:
  `Algebra.ClosedLift.bijective_reduction, Algebra.ClosedLift.reduction`.
  No hits; the Mathlib search service does not index the project declarations.
- `msearch.py ... grep` query:
  `ClosedLift|closedLift|closed_lift|bijective_reduction`, subdirectory
  `RingTheory`: no Mathlib hits.
- Direct `rg` for `ClosedLift|closedLift|closed_lift` in upstream
  `WeilConjectures` found `RingTheory/ProEtale/ClosedLift.lean`, and its
  downstream use in `AlgebraicGeometry/ProEtale/ClosedCoverExtension.lean`.
  Direct grep for the node id located the exact theorem and docstring.
- Direct `rg` in `lean/Sheaf` found only the dependency's `ClosedLiftMap`
  extension, which publicly reuses the upstream construction.
- `rg` for `bijective_reduction` in `dag/lean_names_upstream.json` returned
  no hit; direct source inspection supplies the exact declaration.

No statement correction, new node, dependency module, or disputed statement.
Validation: `deliver2.py --no-push` performs a server-only `#check` of the
existing declaration through scompile.py and the maintainer's preflight.

## Second reading by NS

I independently read the node and its five proof steps, both statement-dependency
nodes and their recorded modules, the blueprint source page, and Stacks
`proetale.tex`, lemma-lift-ind-etale (Tag 097P), lines 1220–1310. I also read
`coord/pefw-upstream-framework.md` and the exact ClosedLift and IndEtale sources
in the group clone, checking the corresponding upstream source declarations.

The statement, including the hypotheses inherited from the lift definition,
and its Lean correspondence are:

1. A commutative base ring A: `(A : Type u) [CommRing A]`. Exact; no field,
   Noetherian, characteristic, or nonzero-ring restriction.
2. An arbitrary ideal I of A: `(I : Ideal A)`. Exact; neither properness nor
   nilpotence is required by the source or the theorem.
3. An ind-etale A/I-algebra Cbar: `(C : Type u) [CommRing C]`
   `[Algebra (A ⧸ I) C] [Algebra.IndEtale (A ⧸ I) C]`. Exact. I read
   `Algebra.IndEtale.exists_colimitPresentation`: its category is small and
   filtered and every term is `Algebra.Etale`, including finite presentation.
4. Cbar regarded as an A-algebra through A/I: `[Algebra A C]`
   `[IsScalarTower A (A ⧸ I) C]`. Exact: the tower asserts precisely that
   the two structural maps compose to the supplied A-action. Every quotient
   algebra has the induced structure, and compatibility determines it.
5. The specified lift H_A(Cbar): `Algebra.ClosedLift A C`. Exact. I opened
   `Index`, `Index.Hom`, `diagram`, `coconeC`, `ClosedLift`, and `toAlgHom`,
   not just their names. The definition node's recorded ClosedLiftMap module
   publicly imports these same declarations. Its relation-ideal presentation
   model is equivalent to the node's finite-list model: etaleness implies
   finite presentation, so its relation ideals are finitely generated;
   forgetting the redundant choice of generators is fully faithful and
   essentially surjective. All compatible algebra maps are retained.
6. The quotient by I times the lift:
   `ClosedLift A C ⧸ I.map (algebraMap A (ClosedLift A C))`. Exact: the
   mapped ideal is the ideal generated by the images of I.
7. The specified map to Cbar: `Algebra.ClosedLift.reduction A C I`. Exact:
   it is `Ideal.Quotient.lift` of the colimit cocone map `toAlgHom`, using
   `map_le_ker_toAlgHom`; it is not an arbitrary isomorphism between the rings.
8. This map is an isomorphism: `Function.Bijective (reduction A C I)`.
   Exact for a ring homomorphism; its inverse function is a ring
   homomorphism. Conversely a ring isomorphism is bijective. All objects
   precede this sole conclusion; no existential lift or extra clause occurs.

Edge cases: I = zero and I = the unit ideal are allowed; zero A and zero C
are allowed. The latter includes the empty affine scheme case. There is no
scheme, n, characteristic, or arbitrary indexing-set binder in this theorem.
The presentation model allows n = 0. Its category has the identity
factorization and so is nonempty, even for zero rings. All characteristics
are covered. The common universe u is polymorphic; rings from different
universes may be considered in their common maximum universe by cumulativity.
The IndEtale indexing universe is that same u, not an independent smaller
test universe. No variable or universe is unbound.

Independent searches, using different terms from the first worker:

- `msearch.py NS lem-exc-closed-lift-reduction leanfinder` with query
  "The canonical map from an etale approximation modulo an ideal to the
  ind etale quotient algebra is injective and surjective": eight hits,
  including formally etale square-zero lifting and standard-etale
  presentation equivalences. Their displayed types do not express this map.
- `msearch.py ... loogle '"reduction"'`: twelve name hits, concerning Lean
  reduction and the WLOG tactic, with no matching algebra statement.
- Direct `rg` in Mathlib/RingTheory for bijective quotient/reduction names
  found residue-field and totally-split statements, not this lift theorem.
- Direct `rg` for `bijective_reduction|ClosedLift|closed_lift` in upstream
  WeilConjectures and project lean/Sheaf found exactly the existing theorem,
  its downstream ClosedCoverExtension use, and the dependency ClosedLiftMap
  module. I read the theorem and its ambient binders in full in both sources.

Verdict: the existing record is correct. Its `lean.statement` is verbatim
its two-line signature. No new module, definition node, dependency repair,
statement correction, or mathematical change is needed. Nothing is proved
in this delivery. The upstream theorem remains sorry; this is only a stage-2
statement attachment. The existing-source rule requires reuse rather than
rewriting its shorter docstring; the five-step proof remains available in
the node: form the quotient map and ind-etale colimit, lift etale stages for
surjectivity, obtain flatness by ind-etale stability, use the flat-quotient
kernel equation x = xe, then invert 1-e to kill the kernel.

Only this independent review was appended. The delivery tool checks the
existing declaration on the server through scompile.py, with no delivered
Lean file and no local compiler invocation.
