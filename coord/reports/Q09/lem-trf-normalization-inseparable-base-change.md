## Worker report

Repair of immutable head 59a6cff267db, all returned points addressed. The only declaration is
`AlgebraicGeometry.normalization_inseparable_base_change` in
`Sheaf.AlgebraicGeometry.NormalizationInseparableBaseChange`; its proof remains `sorry`.
There are no definitions, new nodes, dependency repairs, or changes to the node's TeX statement.
The node copy retains current main's fields and changes only `lean`.

For explanation here only, write Cᵢ for the pullback of C to kᵢ, Xᵢ for Cᵢ's reduction,
νᵢ for its normalization map, nᵢ for νᵢ followed by Xᵢ → Cᵢ, and fᵢ for the resulting
map to Spec kᵢ. The actual Lean signature writes out these terms without local notation or lets.

Hypothesis and clause audit:

- Fields k, k₁, k₂: `(k k1 k2 : Type u)` with the three `Field` instances.
- The compatible extension tower: the three `Algebra` instances and
  `IsScalarTower k k1 k2`; its maps are `Spec.map (CommRingCat.ofHom (algebraMap …))`.
- Both successive extensions finite and purely inseparable: the two `Module.Finite`
  and two `IsPurelyInseparable` instances.
- Integral finite-type k-scheme C: `C : Scheme.{u}`, `C.Over (Spec (CommRingCat.of k))`,
  `IsIntegral C`, `LocallyOfFiniteType (C ↘ …)`, and `QuasiCompact (C ↘ …)`.
- Base changes and integral reductions: `pullback` and `.nilradical.subscheme`, with
  existential witnesses `h1` and `h2 : IsIntegral …`. These are conclusions, not hypotheses.
- Their normalizations: `@Scheme.normalization _ h1/h2` and
  `@Scheme.fromNormalization _ h1/h2`, using the recorded upstream construction.
- Geometric normality of N₁: the implication's premise quantifies over every
  `(L : Type u) [Field L] [Algebra k1 L]` and every point z in the corresponding
  pullback, asserting `IsDomain` and `IsIntegrallyClosed` for its presheaf stalk.
- Comparison over C₂: `∃ e : N₂ ≅ pullback f₁ (Spec.map …)`. The first conjunct is
  `e.hom ≫ pullback.map … = n₂`. The specified `pullback.map` uses the actual
  N₁ → C morphism, the identity on Spec k₂ and Spec k₁ → Spec k, hence is exactly
  ν₁ × id followed by the canonical identification with C₂. Its two square equations
  are constructed using `pullback.condition` and `IsScalarTower.algebraMap_eq`.
- Uniqueness is `∀ e', e'.hom ≫ pullback.map … = n₂ → e' = e`. It ranges only
  over isomorphisms with the required equation; it does not assert uniqueness among
  arbitrary scheme isomorphisms.
- Geometric normality of N₂: the next conjunct is the identical stalk condition with
  `k2` and its structural map, quantified over all `(L : Type u) [Field L] [Algebra k2 L]`.
- Every closed subscheme: `(D1 : Scheme.{u}) (d1 : D1 ⟶ N₁) (_ : IsClosedImmersion d1)`.
  Its scheme-theoretic inverse image is `pullback d1 (e.hom ≫ pullback.fst f₁ …)`;
  its reduced inverse image is that pullback's `.nilradical.subscheme`.
  The theorem provides an isomorphism `eD` from this reduction to
  `(pullback (d1 ≫ f₁) (Spec.map …)).nilradical.subscheme`, exactly
  `(D₁ ×_{k₁} k₂)_red`. The two following equations require compatibility over
  D₁ (the first projections) and Spec k₂ (the second projections). Together they
  specify the canonical identification, rather than an unrelated scheme isomorphism.
- Finiteness: `IsFinite (d1 ≫ f₁) → IsFinite (…)`, where the conclusion's arrow
  starts at the reduced inverse image, continues through its reduction immersion,
  its projection to N₂, and f₂. Thus it asserts finiteness of that inverse image
  itself over k₂, without imposing finiteness on arbitrary closed D₁.

Dependency declarations used (recorded interfaces checked against the actual sources):

- `Field` (`Mathlib.Algebra.Field.Defs`); `Algebra`, `algebraMap`
  (`Mathlib.Algebra.Algebra.Defs`); `Module.Finite`, `IsPurelyInseparable`
  (`Mathlib.FieldTheory.PurelyInseparable.Basic` and its imports).
- `Scheme`, `Scheme.Hom` (`Mathlib.AlgebraicGeometry.Scheme`), `Scheme.Over` and
  its structural map (`Mathlib.AlgebraicGeometry.Over`), `IsIntegral`
  (`Mathlib.AlgebraicGeometry.Properties`), `LocallyOfFiniteType` and `QuasiCompact`
  (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its imports).
- `pullback`, `.fst`, `.snd`, `.map`
  (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, via scheme limits).
  The current `def-pc-base-change` record explicitly instructs consumers to use these
  for scheme base change; its primary `moduleBaseChange` declaration is for modules.
  The current upstream convention source was read with `scompile.py --source
  WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; no retired Sheaf copy is imported.
- `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, `.subschemeι`
  (`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and its imports).
- `Scheme.normalization` and `Scheme.fromNormalization`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`).
- `IsDomain`, `IsIntegrallyClosed` (`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`
  and its imports), used in the normal-domain inline form specified by the node record.
- `IsClosedImmersion` (`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`),
  `IsFinite` (`Mathlib.AlgebraicGeometry.Morphisms.Finite`).

Edge cases: identity extensions, characteristic zero, positive characteristic with a
nonreduced base change, and empty closed D₁ are retained. C itself is integral and thus
reduced; only its field base changes need not be reduced. No separatedness assumption
is added. For C = Spec Q(√2) and the identity tower, the conjugation automorphism is
excluded by the equation over C₂; the identity is the allowed canonical comparison.
The empty scheme is excluded for C only by the given integrality assumption, not for D₁.
The previously reviewed universe conventions and geometric-normality quantifiers are retained.

Searches from the retained packet, inspected in searches.jsonl: `msearch.py leanfinder`
with “normalization commutes further finite purely inseparable field extension geometrically
normal” returned purely inseparable field facts, no scheme comparison theorem; `msearch.py
loogle` with “normalization, IsPurelyInseparable, geometrically normal” returned no hits
(unknown identifier normalization); `msearch.py grep` with
“normalization.*purely.*inseparable” in Mathlib/AlgebraicGeometry returned no hits.
The repaired packet also repeats `rg` searches of WeilConjectures and lean/Sheaf for
normalization/base-change constructions and reads the recorded normalization and pullback
signatures. No existing exact theorem was found. No new notion was introduced.

Returned point (1): added the equation over C₂ and made uniqueness conditional on it.
Returned point (2): removed `True`, stated the reduced inverse-image isomorphism with both
projection equations, and stated its finiteness over k₂ under precisely the given finite
D₁/k₁ condition. Minor H9: removed the three unused/retired Sheaf imports.
Minor H8: expanded the docstring to follow all four DAG proof steps, including the dense
normal locus, reduction factorization, uniqueness on affine domains, and the finite quotient.
There is no outstanding STATEMENT-DISPUTED claim or node fault.

## Second reading by Q09

Author self-check under the dispatcher's no-subagent instruction; the maintainer supplies
the independent review. With the node and final module open, I checked every hypothesis and
clause using the audit above. I found and repaired both returned mismatches: unrestricted
scheme-isomorphism uniqueness, and the vacuous closed-subscheme clause. The second reading
also required compatibility of eD with the projection to D₁ in addition to k₂, and checked
that the finiteness conclusion concerns the reduced inverse image in N₂ itself.
There are no statement-local lets, private copies, helper definitions, or added assumptions.
All data are existing Mathlib/upstream constructions; only the named theorem is postponed.
