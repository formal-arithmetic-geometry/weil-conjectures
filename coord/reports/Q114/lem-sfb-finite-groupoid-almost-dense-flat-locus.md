## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupoidAlmostDenseFlatLocus` states
`AlgebraicGeometry.IsGroupoidScheme.exists_almostDense_finiteLocallyFree`, with
one `sorry` and no definitions or other postponed theorems. It renders Stacks
Tag 0ABA, `lemma-finite-flat-over-almost-dense-subscheme`, read directly in
`literature/stacks-project/more-groupoids.tex`, lines 2456–2527. No change to the
node statement, dependency lists, or proof is needed. This is a supporting lemma,
not the blueprint unit's statement. The current blueprint direct-images proof was
also consulted for its surrounding constructibility argument.

Clause-by-clause correspondence:

- Schemes U and R: `{U R : Scheme.{u}}`, with an explicit arbitrary universe `u`.
- Source, target, identity, inverse, composition: `s t`, `e`, `i`, and
  `c : pullback s t ⟶ R`. The hypothesis `hG : IsGroupoidScheme s t e i c` uses
  the recorded declaration, including its groupoid laws on every test scheme.
- Finiteness of both structure maps: `[IsFinite s] [IsFinite t]`, separately.
- An open subscheme W of U: `W : U.Opens`, with its canonical scheme
  `W.toScheme` and inclusion `W.ι`. This parametrizes every open subscheme up to
  its canonical isomorphism over U and imposes no affine or compactness condition.
- A closed subscheme W' of W: `W' : Scheme.{u}`, `j : W' ⟶ W.toScheme`, and
  `IsClosedImmersion j`. Its map to U is the composite `j ≫ W.ι`.
- Invariance of W as a subscheme: `s ⁻¹ᵁ W = t ⁻¹ᵁ W`. An open subscheme is
  determined by its underlying open with the restricted structure sheaf, so this
  is scheme-theoretic equality, not a loss of structure.
- Invariance of W' as a subscheme: there is an isomorphism
  `E : pullback s (j ≫ W.ι) ≅ pullback t (j ≫ W.ι)` with
  `E.hom ≫ pullback.fst t (j ≫ W.ι) = pullback.fst s (j ≫ W.ι)`.
  Thus the inverse-image subschemes agree over R, including their defining ideals.
  An arbitrary abstract isomorphism or equality of underlying point sets would
  not suffice; the equation over R is essential. The maps to R are monomorphisms,
  since they are pullbacks of the composite of a closed and an open immersion.
  Isomorphism over R therefore expresses exactly equality of these subobjects.
- The closed immersion is a homeomorphism: `IsHomeomorph j`. Together with the
  closed-immersion clause this is precisely the source's thickening condition;
  it permits nontrivial nilpotent structure and does not require a uniform
  nilpotence exponent.
- Saturated closure fills U:
  `t '' (s ⁻¹' closure (W : Set U)) = Set.univ`. This uses the original underlying
  maps of points. The order of the equality is reversed from the prose, without
  changing its content. It does not require W itself to be dense.
- Restriction along any a:T→U is the double fibre product already given by
  Mathlib's `pullback`; in the conclusion a is `j ≫ W.ι`. Put, just for this
  explanation, P = `pullback (j ≫ W.ι) s`. Then its arrow scheme is
  `pullback (pullback.snd (j ≫ W.ι) s ≫ t) (j ≫ W.ι)`.
  This is exactly `(W' ×_{U,s} R) ×_{t,U} W'`, with no arbitrary map selected.
- Its source is `pullback.fst (pullback.snd (j ≫ W.ι) s ≫ t) (j ≫ W.ι) ≫
  pullback.fst (j ≫ W.ι) s`, the projection to the first W' factor.
  Its target is `pullback.snd (pullback.snd (j ≫ W.ι) s ≫ t) (j ≫ W.ι)`, the
  projection to the last W' factor. The two last conjuncts state
  `.IsFiniteLocallyFree` for these two specific maps, separately.
  The induced groupoid operations are determined by restriction of the original
  operations and are explanatory in the node, not additional output data.

Dependency declarations read and used:

- `def-a1-groupoid-scheme`: `Sheaf.AlgebraicGeometry.GroupoidScheme`,
  `AlgebraicGeometry.IsGroupoidScheme`; full signature, fields and docstring read.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
  The node also records `AlgebraicGeometry.IsIntegralHom`, whose signature was
  read in `Mathlib.AlgebraicGeometry.Morphisms.Integral`; only finite is needed here.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  The imported groupoid module provides scheme pullbacks.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; used by the canonical `Scheme.Opens.ι`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`. Its full definition extends
  `IsFinite`, `Flat`, and `LocallyOfFinitePresentation`, exactly as the node says.
  The degree class in the same recorded dependency was also read; no degree
  constraint is part of this item's conclusion.

Proof dependencies: nonpublic imports provide
`AlgebraicGeometry.IsProper` and its finite-morphism instance (Proper),
`Scheme.Hom.isClosedMap` (UniversallyClosed),
`Scheme.Hom.finite_preimage_singleton` (QuasiFinite), and
`AlgebraicGeometry.Flat` / `AlgebraicGeometry.LocallyOfFinitePresentation`
(Flat / FinitePresentation). Finite base-change permanence is in the public
Finite import already used by the statement. The rank-filtration and
subset-saturation nodes currently have neither a Lean record nor a Mathlib
match; their arguments are preserved in the eight-step docstring. They are
proof-only dependencies and introduce no missing notion needed to type this
statement, so no new dependency statement is manufactured in this delivery.

Edge cases checked before drafting and again against the final signature:

- Empty U: the empty open and empty closed subscheme give empty restricted arrows;
  the homeomorphism and saturated-closure equality remain meaningful and true.
- Identity groupoid on an arbitrary scheme: take W=U and W'=U; the restricted
  projections are identities, hence finite locally free without any regularity.
- A constant finite group acting trivially: taking the full object scheme gives
  finite free restricted projections, with all invariance clauses exact.
- Nonreduced schemes: the isomorphism over R retains the closed subscheme ideals,
  and `IsHomeomorph j` allows a proper thickening. Nothing forces reducedness.
- Non-quasi-compact schemes with unbounded ranks across disjoint components:
  the statement has no rank bound, no finite index set and no compactness binder.
- W need not be dense: the conclusion is the saturation of its closure, exactly
  the source's weaker topological coverage property.
- There are no Noetherian, separation, flatness, finite-presentation, affine,
  surjectivity, or nonemptiness hypotheses added to the input. The sole universe
  `u` introduces no equality between independent site or coefficient universes.

Searches for an existing exact statement (all run for this item):

1. `msearch.py ... leanfinder` with query
   "A groupoid scheme with finite source and target has an invariant open and a
   closed thickening on which source and target are finite locally free and
   whose saturated closure is the whole scheme" returned eight results, including
   `ExistsHomHomCompEqCompAux.𝒰D`, `.𝒰D₀`, `.𝒰S`,
   `Scheme.RationalMap.openCoverDomain`, `LocallyOfFiniteType`, and open-cover
   constructions. None states this groupoid theorem.
2. `msearch.py ... loogle 'IsFinite, IsFiniteLocallyFree'` returned zero hits
   (the service reported unknown identifier `IsFinite`, so this query alone
   provides no evidence of absence).
3. `msearch.py ... grep 'groupoid.*(flat|dense)|invariant.*thickening'
   AlgebraicGeometry` returned zero Mathlib hits.
4. `msearch.py ... leansearch` with the query "A finite scheme groupoid admits an
   invariant open subscheme with an invariant closed thickening whose restricted
   source and target are finite locally free and whose saturated closure covers
   the object scheme" returned eight hits: finite-morphism definitions,
   finite closed immersions, restriction facts, and `Scheme.Opens.toScheme`.
   None states the result.
5. `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for almost-dense flat loci, groupoid restriction,
   and invariant subschemes found no exact theorem. The literal node-id search
   in `lean/WeilConjectures` found no match. Existing open-restriction and
   Cohen–Macaulay double-restriction modules were opened and read; neither gives
   this existence result. The latter's helper projections use the equivalent
   reversed pullback order; this module simply uses the recorded Mathlib
   projections in the node's displayed order and introduces no duplicate helper.

Validation: `scompile.py Q114 lem-sfb-finite-groupoid-almost-dense-flat-locus
<module>` compiled both the sandbox and library module on the server, in 4.3 and
5.7 seconds respectively, without errors or warnings. `autoImplicit false` is
set. All universes and variables are explicit. Every line is at most 100 columns.
The only node-field change is its Lean record. There are no node faults or
statement disputes.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
