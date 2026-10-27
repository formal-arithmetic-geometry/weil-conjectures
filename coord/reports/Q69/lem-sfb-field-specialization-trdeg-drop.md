## Worker report

The module `Sheaf.AlgebraicGeometry.FieldSpecializationTrdegDrop` states
`AlgebraicGeometry.field_specialization_trdeg_drop`, with proof `sorry`. It introduces
no definitions. Only the item's `lean` field changes; its accepted split, mathematical
statement, dependencies and provenance are preserved. No statement dispute or correction.

The inherited BLOCKED ending was a stage-1 stale-dispatch refusal. I read the current
node, its O3 report, the queue, and the stage-handoff paragraph of brief-stage2 section 0.
O3's accepted delivery supplied the split and explicitly supplied no Lean. The current
node has no Lean record, and no released repair note was found. Thus this is the authorized
stage-2 statement task, not a re-splitting of the accepted stage-1 work.

Every hypothesis and clause is rendered as follows:

- The field `k` is `{k : Type u} [Field k]`.
- The arbitrary scheme `X` is `{X : Scheme.{u}}`. The explicit common universe is the
  universe of the category of schemes and its morphisms; `u` is arbitrary.
- The specified morphism to the spectrum is `(f : X ⟶ Spec (.of k))`.
- Locally finite type is exactly `[LocallyOfFiniteType f]`. There is no `QuasiCompact`
  assumption, so this does not strengthen the node to finite type.
- The two points are `(x x' : X)` and distinctness is `(hne : x ≠ x')`.
- The specified direction of specialization is the literal closure hypothesis
  `(hsp : x' ∈ closure ({x} : Set X))`. Closure uses the existing Zariski topology of `X`.
- The fields are exactly `X.residueField x` and `X.residueField x'`, not fraction fields
  substituted into the statement. The two explicitly supplied algebra instances are
  `(f.residueFieldAlgebraMap x).toAlgebra` and
  `(f.residueFieldAlgebraMap x').toAlgebra`, so their base-field maps come from the given
  morphism `f`, rather than arbitrary field-extension structures.
- The conclusion is the strict cardinal inequality
  `@Algebra.trdeg k (X.residueField x') _ _ (f.residueFieldAlgebraMap x').toAlgebra <`
  `@Algebra.trdeg k (X.residueField x) _ _ (f.residueFieldAlgebraMap x).toAlgebra`.
  This is exactly the reversed writing of the node's `trdeg(kappa(x)) > trdeg(kappa(x'))`.
  No natural-number conversion or extra finiteness conclusion is introduced.
- There is no reducedness, separation, integrality, global dimension bound or
  quasi-compactness assumption. There is no characteristic restriction.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, same module.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, publicly imported.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, in `Mathlib.AlgebraicGeometry.ResidueField`.
  The existing canonical base-field map `Scheme.Hom.residueFieldAlgebraMap` is in
  `WeilConjectures.ZetaSeries`, publicly imported. I read its full definition: it
  composes the canonical map from `k` into the prime residue field, the inverse of
  `Scheme.Spec.residueFieldIso`, and `f.residueFieldMap`. It is available for every
  field, with no finite-field assumption.
- `def-kun-transcendence-degree`: `Algebra.trdeg`, in
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, publicly imported. Its definition
  is the supremum of cardinalities of algebraically independent subsets.

The proof plan imports the already stated non-Mathlib proof dependencies ordinarily,
without `public`: `WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`
(`AlgebraicGeometry.spec_field_point_residue_field` and its affine-open clause) and
`WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`
(`finiteType_domain_ringKrullDim_eq_trdeg`). Their signatures/docstrings were read.
The remaining proof dependencies are Mathlib notions supplied by these imports:
affine-open spectrum points, finite-type algebras and ring Krull dimension. The theorem's
docstring includes every step of the accepted five-step proof, with the node IDs.

Sources checked: the complete statement and proof of Stacks morphisms.tex,
lemma-dimension-fibre-specialization, Tag 06RU (3), and algebra.tex,
lemma-tr-deg-specialization, Tag 06RP. The former specializes to the unique point of
Spec k without adding any condition on X. I also read the current blueprint's
sk-thm-sf-ctf-stability-direct-images proof, especially paragraph (3); this prerequisite
is not the unit's own statement.

Edge cases checked before writing: an empty scheme cannot provide the two points.
The equality case is excluded exactly by `hne`; on Spec k there is no such pair.
For A=k[t], generic-to-closed specialization has degrees 1 and 0, confirming the
closure direction and strict inequality direction. For A=k[t,u], the chain
(0) < (t) < (t,u) gives degrees 2 > 1 > 0. Nilpotents, such as in
k[t,epsilon]/(epsilon^2), do not change the relevant prime quotients. No reducedness
is needed. An infinite disjoint union of affine finite-type charts is permitted;
the theorem does not impose global quasi-compactness. Nonseparated schemes are
also permitted, since the proof uses just one affine chart containing the specialized
point. Finite and imperfect fields are both included.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: `A nontrivial specialization on a scheme locally of finite type over a field strictly decreases residue field transcendence degree`.
  Eight hits: preimmersion of residue-field points, specializing-map locality,
  descResidueField, closed-point finite-type criterion, SpecToEquivOfField,
  Scheme.height_of_isClosed and the residue-field Field instance. None states strict drop.
- loogle: `"trdeg", "Specializes"`. Zero hits.
- grep: `trdeg.*special|special.*trdeg|trdeg.*residueField`. Zero hits.
- leansearch: `Nontrivial specialization strictly decreases residue field transcendence degree over a field`.
  Eight hits: lift_trdeg_le_of_surjective, Specializes.trans, trdeg_le_of_surjective,
  PrimeSpectrum.localizationMapOfSpecializes, trdeg_add_eq, lift_trdeg_add_eq,
  lift_trdeg_add_le, IsTranscendenceBasis.lift_cardinalMk_eq_trdeg. These are
  non-strict monotonicity, specialization maps or tower formulas, not the item.

Direct rg searches of Mathlib's AlgebraicGeometry and AlgebraicIndependent directories,
WeilConjectures, Sheaf and dag/lean_names_upstream.json found no declaration named
`field_specialization_trdeg_drop`, no item blueprint tag, and no existing strict-drop
statement. The broader transcendence-degree search found closed-point criteria,
closed-irreducible dimension formulas and the existing `Scheme.residueFieldTrdeg`
in `WeilConjectures.AlgebraicGeometry.Sites.SupportDimension`. None states this
strict-specialization result. That existing scalar invariant is not redefined:
the signature uses `Algebra.trdeg` directly with the canonical scalar maps.

Validation: scompile.py compiled both the sandbox view and the final library module
successfully, with no errors or disallowed warnings. `autoImplicit` is disabled;
all variables and the universe are explicit. The module has no line over 100 characters.
The dry run and final delivery are performed with deliver2.py.

## Second reading by Q69

No second reading by another worker: this is the dispatcher-started direct-delivery
workflow and the prompt prohibits starting other agents. The maintainer's independent
review reads the delivery. I re-read the node and the final signature to check every
binder, closure direction, strict inequality and canonical algebra instance against
the correspondence above; no mismatch was found.
