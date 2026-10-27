## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.QuasiprojectivePointClosureProjectivity`
states `AlgebraicGeometry.quasiprojective_point_closure_projectivity`, with a single
`sorry` proof. There are no new definitions, dependency repairs, or statement corrections.
The node copy changes only `lean`.

Source read: Stacks `literature/stacks-project/limits.tex`,
`lemma-Noetherian-dvr-valuative-proper` (Tag 0208), the equivalence of (1) and (4)
and its properness argument. The node's agent-formulated assembly adds the closed
ambient embedding, H-projectivity, and dense-base-open clauses from its six-step
proof. That proof is reproduced step by step in the declaration docstring.

Hypotheses and objects, in the order of the node:

- The Noetherian integral base is `S : Scheme.{u}` with `[IsIntegral S]`,
  `[IsLocallyNoetherian S]`, and `[CompactSpace S]`. Compactness means precisely
  quasi-compactness of the scheme's underlying space; it is the extra clause beyond
  local Noetherianity that the node explicitly requires.
- `K` is the canonical `S.functionField`, the stalk at `genericPoint S`.
  The generic inclusion is `S.fromSpecStalk (genericPoint S)`. Using this canonical
  field loses no choice of an identified function field and imposes no affine,
  normality, dimension, characteristic, or base-field hypothesis.
- `q : H ⟶ S` has `[IsHProjective q]`, `[LocallyOfFiniteType q]`,
  and `[QuasiCompact q]`: the last two are exactly finite type, as the dependency
  records specify. H-projectivity is the blueprint's finite projective-space
  embedding convention, not an alternative notion of projectivity.
- `j : M ⟶ H` with `[IsOpenImmersion j]` presents the specified open subscheme.
- `m : Spec S.functionField ⟶ M` and `hm` say that this point lies over the
  canonical generic inclusion of `S`.
- `i : R ⟶ M` with `[IsClosedImmersion i]`, `[IsIntegral R]`, and
  `hclosure : Set.range i = closure (Set.range m)` present the reduced closure.
  Integral implies reduced. A reduced closed subscheme with this support is exactly
  the reduced induced closed subscheme on the closure. This uses the existing
  closed-immersion and integral notions without defining a second reduced-closure
  construction. The domain of `m` is a one-point field spectrum, so its range is
  exactly the image point whose closure the node specifies.
- `f : R ⟶ S` and `hf : i ≫ j ≫ q = f` specify its structure morphism.
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, and
  `[LocallyOfFinitePresentation f]` are precisely the stated properties of `f`.
- `hgeneric` says that a map `a : Spec S.functionField ⟶ R` satisfies `a ≫ i = m`
  and makes `IsPullback a (𝟙 (Spec S.functionField)) f
  (S.fromSpecStalk (genericPoint S))`. This says exactly that the generic fibre is
  `Spec K` with the identification induced by `m`, including its scheme structure.
  It does not merely assert equality of the underlying generic-fibre point sets.
- In `hext`, `A : Subring S.functionField` ranges over all actual subrings of `K`.
  `[IsDiscreteValuationRing A]` excludes fields, as the dependency requires, and
  `[IsFractionRing A S.functionField]` expresses fraction field `K` via the
  inherited inclusion. The condition on `b` is the equality of its generic
  restriction with the canonical generic inclusion of `S`. The existential `v`
  satisfies both the equality over `S` and the generic restriction equal to `m`.

Conclusions, clause by clause:

- The first conjunct quantifies over each of these `(A,b)` and every lift `v`
  satisfying the two required compatibilities, and asserts
  `∃! w : Spec (.of A) ⟶ R, w ≫ i = v`. This is unique scheme-theoretic
  factorization through `i`, not just containment of the image in its support.
  The factor is automatically over `S` by `hf` and the compatibility of `v`.
- `IsProper f` is properness of the given structure map.
- `IsClosedImmersion (i ≫ j)` is the closed embedding into the original ambient `H`.
- `IsHProjective f` retains the exact projectivity convention of the hypothesis.
- `∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (f ∣_ U)` gives a dense base open
  and an isomorphism on its entire inverse image, as required. `Dense` means its
  closure is the whole base.
- The final sentence of the node is respected: no curve, normality,
  Hom-representability, or rational-curve hypothesis appears in the signature.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` and its
  reducedness instance.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded component-field
  module explicitly directs arbitrary integral schemes to Mathlib's
  `AlgebraicGeometry.Scheme.functionField`; its full definition is the generic
  stalk. The canonical map is `Scheme.fromSpecStalk` in
  `Mathlib.AlgebraicGeometry.Stalk`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, with its finite-coordinate closed embedding.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together
  with `QuasiCompact` from the corresponding morphism module.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`, and
  the parent universal-closedness convention.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`, and `subschemeι` describe the recorded
  reduction convention. Here no chosen reduction is needed: the integral closed
  source with its support already characterizes the reduced closure.
- The existing `CategoryTheory.IsPullback` and `Scheme.Hom` restriction notation
  express the generic-fibre and base-open conditions without any helper notion.

Proof-dependency imports are private: the recorded upstream
`SchemeTheoreticallyDominant` module (`IsClosedImmersion.exists_lift_of_isFractionRing`),
`Sheaf.AlgebraicGeometry.Morphisms.GenericDvrPropernessCriterion`
(`isProper_iff_generic_dvr_extensions`),
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
(`hProjective_properness`), and
`Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen`
(`exists_dense_open_isIso_of_separated_birational`).
The remaining proof leaves `IsProper.of_comp`,
`IsClosedImmersion.of_isPreimmersion`, and `IsClosedImmersion.comp` are already
available through the public Mathlib statement imports. No import cycle is introduced.

Edge cases checked mathematically: integral `S` and `R` exclude empty schemes
exactly as the node does; a point `m` excludes an empty ambient open. For a
zero-dimensional base `Spec K`, the generic-fibre hypothesis already makes `f`
an isomorphism, and the conclusion allows `U = ⊤`. Projective space dimension
zero is not excluded. DVRs remain genuine nonfield discrete valuation rings; no
additional DVR-existence assumption is imposed. An arbitrary characteristic,
non-normal integral base, nonaffine `R`, and nonproper `M` are allowed. The
ambient `M` need not equal `H`. All schemes and their canonical function fields
use the arbitrary explicit universe `u`; there is no independent too-small
universe in the quantification over valuation subrings.

Searches run on 2026-10-24:

- `msearch.py leanfinder`: “Reduced closure of a generic rational point in a
  quasi-projective scheme is projective and isomorphic over a dense open if the
  point extends along every discrete valuation subring”. Eight hits, including
  `Proj.valuativeCriterion_existence` and rational-map APIs; none states this
  closure criterion with all conclusions.
- `msearch.py loogle`: `"IsProper", "IsHProjective"`: zero hits.
- `msearch.py grep`: `reducedClosure|generic.*dvr|point.*closure|closure.*projectiv`
  in Mathlib `AlgebraicGeometry`: five hits about projective-spectrum topology
  and closed points; no exact theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and the same
  reduced-closure/generic-DVR/projectivity concepts: no declaration for this
  statement. The generic DVR criterion is already the recorded proof dependency;
  the resolution-strata reduced-closure ideal and unrelated point-closure
  constructions do not state this theorem.
- A direct name search of Mathlib, both project source trees and
  `dag/lean_names_upstream.json` found no collision for
  `quasiprojective_point_closure_projectivity`.

Validation: `scompile.py NS lem-sfb-quasiprojective-point-closure-projectivity`
compiled the file cleanly in both sandbox and library module modes on the server
(5.5 seconds each), with no unexpected warning. All variables and universe levels
are explicitly bound. No theorem is proved, no data definition contains `sorry`,
and the node's statement has not changed. No STATEMENT-DISPUTED issue was found.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
