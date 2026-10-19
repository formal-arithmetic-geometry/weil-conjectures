## Worker report

The main module `Sheaf.AlgebraicGeometry.NormalGeometricSpecializationConjugacy` states
`AlgebraicGeometry.Scheme.normal_geometric_specialization_conjugacy`, with `sorry`.
The node's statement, proof, and proof dependencies are unchanged. Its statement dependencies gain
`def-per-strict-localization-point-change`, supplying the canonical maps needed to interpret its
composition equations. No dependency record is replaced.

I read the node and its six proof steps, all six original statement-dependency statements and
records, and their source declarations. I checked ILO, Travaux de Gabber, Expose XVII,
printed pp. 277–278 (PDF pp. 283–284): the two conjugating-isomorphism diagrams in the proof of
3.5.8, and the generic and closed Galois invariance in 3.6.1. I also read the pointed-neighbourhood
construction in Stacks 04HX, `lemma-describe-etale-local-ring`, in `etale-cohomology.tex`.
The six-step natural-language proof is included in the theorem docstring, including the distinction
between algebraic closures and their relative separable closures, the intermediate fraction-field
argument, the unique henselian lift of the residue action, and different generic closures.

Hypotheses and clauses, with their Lean renderings:

| Node text | Lean |
| --- | --- |
| Scheme S | `(S : Scheme.{u})` |
| Local henselian scheme | `[IsAffine S] [HenselianLocalRing Γ(S, ⊤)]`; a local scheme means the spectrum of a local ring, and the latter class includes locality |
| Noetherian | `[IsNoetherian S]` |
| Excellent | `_hExcellent : IsExcellent Γ(S, ⊤)`; for this affine scheme, excellence is excellence of its coordinate ring |
| Integral | `[IsIntegral S]`, including nonemptiness |
| Normal | `_hNormal : ∀ (p : Ideal Γ(S, ⊤)) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`, exactly the dependency's recorded inline convention |
| Closed point s | `(s : S)` and `_hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)` |
| Generic point eta | `genericPoint S`; integrality supplies irreducibility and the canonical generic point |
| Chosen algebraic closures of the generic residue field | `Ωη₁`, `Ωη₂`, their field and algebraically closed structures, `Algebra (S.residueField (genericPoint S)) ...`, and the two `IsAlgClosure` instances |
| Chosen algebraic closure of the closed residue field | `Ωs`, its field and algebraically closed structures, `Algebra (S.residueField s) Ωs`, and `IsAlgClosure (S.residueField s) Ωs` |
| Geometric points over precisely eta and s | `barη₁`, `barη₂`, `barS`, with `_hη₁`, `_hη₂`, `_hS` identifying each map with the spectrum of its specified residue-field embedding followed by `fromSpecResidueField` |
| A geometric specialization is any S-map of the strict localizations | Each subtype consists of `t : strictHenselizationScheme barηᵢ ⟶ strictHenselizationScheme barS` with `t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barηᵢ` |
| Existence | The first two conjuncts are `Nonempty` of these subtypes, for both choices |
| Conjugacy for t,t' | Third conjunct quantifies over both specialization subtypes and produces `σ : Aut (Spec (.of Ωη₁))` with `hσ : σ.hom ≫ barη₁ = barη₁`, and the required equality |
| Eta-automorphism, rather than an arbitrary geometric automorphism | The equation `hσ` says it is over S; since the geometric map factors through its fixed residue-field point, this is equivalent to fixing that residue-field map, hence being over eta |
| Composition on strict localizations | `strictLocalizationPointChange ... σ hσ`, characterized by its structural and geometric-point equations, supplies the induced map; categorical `≫` has the reverse written order to conventional circle notation |
| Every closed automorphism and every t | Fourth conjunct quantifies over `τ : Aut (Spec (.of Ωs))`, its over-S equation `hτ`, and t; it produces σ with `t.val ≫ ... τ hτ = ... σ hσ ≫ t.val` |
| Two different chosen generic points | Fifth conjunct quantifies over `t₁,t₂` and produces `σ : Spec (.of Ωη₂) ≅ Spec (.of Ωη₁)` over S, with `t₂.val = ... σ hσ ≫ t₁.val` |
| Closed-automorphism compatibility with two choices | Sixth conjunct gives `t₂.val ≫ ... τ hτ = ... σ hσ ≫ t₁.val` for every τ, t₁ and t₂ |

The fixed-choice assertions for the second closure follow by swapping the universally quantified
closures; the two-closure assertions include equality of the choices, without requiring distinctness.
No hypothesis of finite dimension, positive dimension, perfectness, or separability of the entire
algebraic closure is added. The closure fields are in the scheme universe, as required by the
recorded geometric-point and strict-localization APIs. Algebraic closures of the residue fields
admit models in that universe.

Dependency declarations used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with `IsDomain`
  and `Localization.AtPrime` for the recorded normal-ring inline formula.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded terminology module,
  reexporting `HenselianLocalRing` (and containing `IsStrictlyHenselianLocalRing`).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`;
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` explains the
  residue-field presentation of the geometric-point binders.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme`, the
  recorded construction, reexported through the helper imports. Its ring is the existing
  pointed affine coordinate-ring colimit, not a new choice of strict henselization.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`. The local older upstream checkout lacks this
  module, so I read its current published source with `scompile.py --source`.
- `Sheaf.Paper.StrictHenselizationPointEvaluation`: `Scheme.strictHenselizationPointEvaluation`.
- The new module: `Scheme.strictLocalizationPointChange` and
  `Scheme.strictLocalizationPointChange_existsUnique`.

All stated proof dependencies are imported without `public`: relative separable closure
(`Mathlib.FieldTheory.SeparableClosure`), etale local ring triples, strict henselization triples,
strict henselization functoriality, etale colimit normal domain, ind-etale stability, weakly etale
field, finite etale field-product decomposition, existence/uniqueness of algebraic closures,
and map into a henselian colimit. There is no omitted import due to a cycle.

Edge cases checked: dimension zero (s=eta) is allowed; a strictly henselian base is allowed;
identical choices of closures, identical specializations, and identity automorphisms are allowed.
The empty scheme is excluded by the original integrality hypothesis. Imperfect residue fields
are allowed: no strict localization is identified with the spectrum of the entire algebraic
closure. The generic strict-local field in the proof is the relative separable closure.
Normality is not silently replaced by normality of the intermediate extension F/K.
The change-of-point helper also includes nonalgebraic geometric-point extensions and needs no
normality or Noetherian hypothesis.

Searches made with `msearch.py`, recorded in the sandbox search log:

- LeanFinder: `Geometric specializations of a normal henselian local scheme are conjugate under
  automorphisms of the geometric generic point`: eight residue-field/stalk-related results,
  including `Scheme.SpecToEquivOfField`; none states this theorem.
- Loogle: `"specialization", "Galois"`: zero hits.
- Mathlib grep: `speciali[sz].*(Galois|conjug)|Galois.*speciali[sz]`: zero hits.
- LeanSearch: the same plain-language main-statement query: eight results, including
  `IsConjRoot.exists_algEquiv`, ordinary topological specialization, and stalk specialization;
  none supplies the strict-localization statement or all its clauses.
- Source/project `rg`: the item id, proposed declaration names, and strict-localization
  change/repoint/map patterns in `WeilConjectures`, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing theorem or point-change definition. Base-change
  maps in the project refer to a different construction.

Validation: `scompile.py Q44 lem-per-normal-geometric-specialization-conjugacy` with both delivered
files compiled each separately in dependency order, including its library module identity.
Exit status 0; no errors or warnings. Both files satisfy the 100-character line limit and set
`autoImplicit false`. All theorem bodies are `sorry` as required for stage 2.
No STATEMENT-DISPUTED issue or source correction was found.

## New nodes

`def-per-strict-localization-point-change` defines the canonical map induced by a geometric-point
isomorphism over S, needed to give the item's composition equations an actual meaning. It is
characterized by BOTH the over-S equation and the geometric-point evaluation equation. Its named
existence-and-uniqueness theorem states exactly the existence/uniqueness included in this new node;
its docstring gives the pointed-neighbourhood limit construction and the uniqueness argument.
The definition uses `Classical.choose` of this unique universal property; its data is not `sorry`,
and it is not a choice from mere existence or an arbitrary map supplied as a hypothesis.
Source: ILO XVII 3.5.8, printed p. 277, and Stacks 04HX. This defines the action used by the main
statement without assuming the downstream conjugacy theorem.

The new node's searches were run before creating it: LeanSearch queries `An isomorphism of geometric
points over a scheme induces a canonical map between their strict localizations` and
`A geometric point isomorphism induces a uniquely pointed map between strict localizations`
returned eight stalk/ordinary-localization results apiece, not this map. LeanFinder's
`A geometric point isomorphism induces a uniquely pointed map between strict henselizations`
returned eight residue-field results. Loogle `"strictLocalization"` returned zero hits. Mathlib
grep `strictLocalization.*(Iso|iso|repoint)|strictHenselization.*(Iso|repoint)` returned zero hits,
including the targeted AlgebraicGeometry search. Direct source/project greps found the existing
strict-localization construction, structural map and evaluation, all reused, but no point-change map.
The JSON records these queries and actual results from the log. DAG search found no owning node.
`tools/blueprint_refs.py search 'strict localization'` found zero blueprint matches;
searching `geometric point` found 103 broader matches and no point-change definition.
`tools/blueprint_refs.py ancestor` identifies `lem-per-artin-gabber-affine-curve`; the new node
records that ancestor and the item's full via chain. No new statement node is needed.

The original six statement dependencies and all their declarations are retained. The helper's
four statement dependencies are the existing geometric-point, strict-localization, structural-map,
and point-evaluation definitions; no dependency is repaired or duplicated.

The first dry run found one signature-metadata mismatch: the preflight extracts the signature
from `def`, excluding the preceding `noncomputable` modifier. I corrected `lean.statement`
to that verbatim signature and reran the prescribed dry run.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
