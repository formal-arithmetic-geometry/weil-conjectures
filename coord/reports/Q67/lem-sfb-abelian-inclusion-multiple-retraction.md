## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.MultipleRetraction` states
`AlgebraicGeometry.IsAbelianVariety.exists_multiple_retraction`, with its only
proof `sorry`. It gives the positive-multiple retraction of the given closed
immersion of abelian varieties. No definitions, hypotheses or statement clauses
are changed. The node copy differs from the live node only in `lean`.

The inherited BLOCKED ending concerns an already accepted stage-1 split, not a
stage-2 delivery. The live node is split and reviewed under Q103, has no `lean`
record and has no released repair note. The stage-handoff paragraph of
`coord/brief-stage2.md` explicitly permits recording its statement in stage 2.
The accepted split, its proof and all dependencies are preserved verbatim.

Hypothesis and conclusion correspondence:

- "Let k be a field": `{k : Type u} [Field k]`.
- "A/k and B/k": `(A B : Over (Spec (.of k)))` records both structure maps
  to the same ground field. Morphisms in this category are over that field.
- "abelian varieties": `[GrpObj A] [IsAbelianVariety A]` and
  `[GrpObj B] [IsAbelianVariety B]`. The group data are separate from the
  recorded abelian-variety predicate, as its defining module requires.
- "i:B ↪ A": `(i : B ⟶ A)` supplies the specified morphism.
- "of k-group schemes": `[IsMonHom i]` supplies compatibility with the
  identity and multiplication; the group inverse compatibility follows.
- "closed immersion": `[IsClosedImmersion i.left]` is the closed-immersion
  property on the underlying scheme map, without adding an arbitrary
  subgroup presentation or a complement.
- "there exist an integer n>0": `∃ (n : ℕ), 0 < n ∧ ...` ranges over exactly
  the positive integers. No coprimality, invertibility or separability is
  imposed on n.
- "a k-group-scheme homomorphism r:A→B": `∃ (r : A ⟶ B), IsMonHom r ∧ ...`.
  This is existence of an algebraic scheme map, rather than a homomorphism
  only on rational points.
- "r ∘ i=[n]_B": `i ≫ r = 𝟙 B ^ n`, equality of morphisms over `Spec k`.
  Here the power uses `CategoryTheory.GrpObj.Hom.group` with the `MonObj`
  scope open. It is the pointwise n-fold sum, not iteration of composition.
  This is exactly the multiplication map documented by the recorded
  `AlgebraicGeometry.torsionSubgroupScheme` declaration.

Dependency declarations read and used:

- `def-weil-field`: `Field`, from `Mathlib.Algebra.Field.Defs` (mathlib_match).
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety`, from
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`; proper, smooth and
  connected, with group structure bound separately.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, from
  `Mathlib.CategoryTheory.Monoidal.Grp`; `CategoryTheory.IsMonHom`, from
  `Mathlib.CategoryTheory.Monoidal.Mon`; the specialization to schemes over
  a field is documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-sc-mult-n`: `AlgebraicGeometry.torsionSubgroupScheme`, from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. Its full definition
  is `GrpObj.ker (𝟙 G ^ n)` and its docstring explicitly identifies that power
  with multiplication by n. Thus no dependency interface repair or second
  definition of the multiplication map is needed.

The public imports give these recorded notions. Nonpublic proof imports give
`IsAbelianVariety.geometricallyIntegral`, `IsAbelianVariety.irreducibleSpace`
and `IsAbelianVariety.isCommMonObj` from the upstream `AbelianVariety.Basic`;
`exists_eq_snd_comp` from `AbelianVariety.Rigidity`;
`Scheme.exists_pullback_hom_of_isLimit` and
`Scheme.exists_pullback_fst_comp_eq_of_isLimit` from `AffineTransitionLimit`;
`ext_of_isSchemeTheoreticallyDominant` from `SchemeTheoreticallyDominant`;
and the Mathlib permanence results from `Morphisms.QuasiSeparated` and
`Morphisms.FinitePresentation`. The scheme-morphism module paths here have
the exact upstream prefixes used in the delivered imports.

The proof-dependency nodes `lem-sfb-smooth-commutative-subgroup-quotient`,
`lem-sfb-abelian-field-extension`, `lem-sfb-commutative-torsor-positive-weight`,
`lem-sfb-weil-extension-to-abelian-variety`, and
`lem-sfb-abelian-finite-product` have no recorded Lean modules yet and therefore
supply no imports. They are only proof dependencies and are not needed to type
this statement. Their IDs and proof uses remain in the node and are explicitly
named in the six-step proof docstring, for stage 3 and later import maintenance.

Source checked: Milne, Algebraic Groups, iAG2017, printed pp.151-153,
8.15-8.24, especially the full proofs of Lemma 8.22 and Proposition 8.23
and the normalization in the proof of Theorem 8.24. In Lemma 8.22 the integer
is 1 when a rational point exists, or the positive degree of a separable closed
point, so positivity does not impose a new condition. The docstring follows all
six steps of the accepted split, including generic spreading of both a map and
its identity and the rigidity proof of homomorphy.

Edge cases checked before writing:

- B trivial (dimension zero): the unique homomorphism A→B works with n=1.
- i the identity: r the identity and n=1 satisfy the exact equality.
- Both varieties trivial: still covered; no positive-dimension premise appears.
- A proper abelian subgroup of a product: its projection is an example with n=1.
- Arbitrary fields, including imperfect fields and positive characteristic:
  there is no algebraic-closure or perfectness assumption. In particular a
  positive n divisible by the characteristic remains permitted.
- Empty schemes are not spuriously excluded: a group scheme over a field has
  its identity section, and `IsAbelianVariety` already includes connectedness.
- The universe u is explicitly declared and used by the field and the over
  category according to the recorded interfaces. `autoImplicit false` verifies
  that no hidden variables are introduced.

Searches for an existing statement (raw remote-search records are in the
sandbox's searches.jsonl):

- msearch LeanFinder: "For an inclusion of abelian varieties over a field there
  exists a group scheme homomorphism retracting it up to multiplication by a
  positive integer". Eight hits: elliptic point base-change maps,
  abelianization, Selmer groups and affine-space morphisms; none gives this
  algebraic multiple-retraction theorem.
- msearch LeanSearch: "An inclusion of abelian varieties has a group scheme
  retraction up to multiplication by a positive integer". Eight hits: abstract
  categorical retracts, closed immersions, group extensions; no match.
- msearch Loogle: `"AlgebraicGeometry", "retraction"`. Zero hits.
- msearch grep: `retract|AbelianVariety|isogen` in `AlgebraicGeometry/Group`.
  Zero hits.
- Direct rg in upstream abelian-variety sources: `retract|reducib|complement`
  finds unrelated irreducibility and open-complement text, not a retraction.
- Direct rg across `WeilConjectures`, `Sheaf` and `dag/lean_names_upstream.json`:
  `multiple_retraction|multipleRetraction|inclusion.*retract|retract.*inclusion`
  finds unrelated module and complex retractions, no theorem about abelian
  inclusions. Searching the item ID in both Lean roots gives no existing
  blueprint binding. No notion or theorem was duplicated.

Validation: the delivered module compiled through scompile.py in both its
sandbox and its library module location against the server's published live
build, with no errors or non-sorry warnings (7.1 seconds and 3.6 seconds).
All source lines have at most 86 characters. There is exactly one named theorem,
no data definitions and no additional axioms. No statement dispute or node
fault was found.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
