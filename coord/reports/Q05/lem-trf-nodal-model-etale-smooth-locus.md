## Worker report

Delivery: `Sheaf.AlgebraicGeometry.NodalModelEtaleSmoothLocus`, declaration
`AlgebraicGeometry.nodal_model_etale_smooth_locus`. This is a stage-2 statement,
with one named theorem whose proof is `sorry`; no theorem is proved and no new
definition is introduced. Its docstring gives all five accepted DAG proof steps.

The source was read in the local Stacks checkout: morphisms.tex,
`lemma-smooth-at-point` (01V9), lines 7264 onward; `lemma-etale-over-field`
(02GL), lines 8175–8211; descent.tex,
`lemma-syntomic-smooth-etale-permanence` (02KM), lines 4423–4448;
etale-cohomology.tex, `lemma-geometric-lift-to-cover` (03PR), lines 3305–3338.
01V9 supplies the pointwise smoothness/Jacobian criterion and 02GL explains
why the prescribed etale fibre point has a residue-field embedding into the
original algebraically closed field. The existing proof's explicit square-zero
obstruction works in every characteristic. The source of the model construction
is curves.tex, section-etale-local-nodal / 0CBY, as recorded in the existing
`def-trf-universal-nodal-model`.

The current blueprint ancestor and proof were also read at
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality{,.proof}.md`.
As the accepted split already records, the newest ancestor uses contracting
correspondences; this is an existing historical nodal-chart auxiliary, not a
new claim about that updated proof. Its accepted statement and proof are preserved.

### Every hypothesis and clause

| Node text | Lean rendering |
| --- | --- |
| Schemes X,Y,V,U | `{X Y V U : Scheme.{u}}`, with explicit `universe u` |
| Morphism f:X→Y | `(f : X ⟶ Y)` |
| f flat | `[Flat f]` |
| f locally finitely presented | `[LocallyOfFinitePresentation f]` |
| b:V→Y etale | `(b : V ⟶ Y) [Etale b]` |
| q:U→X etale | `(q : U ⟶ X) [Etale q]` |
| p:U→V | `(p : U ⟶ V)` |
| f∘q=b∘p | `(hq : q ≫ f = p ≫ b)` |
| Global function h | `(h : Γ(V, ⊤))` |
| W=Spec_V O_V[u,v]/(uv-h), with its coefficient projection | `pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)`, with projection `pullback.snd ...` |
| Etale V-morphism e:U→W | `(e : U ⟶ pullback ...) [Etale e]` and `(he : e ≫ pullback.snd ... = p)` |
| Coordinate functions u,v | `MvPolynomial.X k`, `k : Fin 2`, mapped by `Ideal.Quotient.mk`, then `Scheme.ΓSpecIso.inv`, then `(pullback.fst ...).appTop` |
| Closed subscheme N=V(u,v) | `W.zeroLocusSubscheme (Set.range (fun k : Fin 2 ↦ ...))`; no reduction is applied |
| Projection identifies N with V(h) | `∃ i : N ≅ V.zeroLocusSubscheme {h}, i.hom ≫ V.zeroLocusSubschemeι {h} = W.zeroLocusSubschemeι ... ≫ pullback.snd ...` |
| Every point t∈U | `∀ t : U` in the second conjunct |
| f nonsmooth at q(t) | `¬ ∃ O : X.Opens, q t ∈ O ∧ Smooth (O.ι ≫ f)` |
| p nonsmooth at t | `¬ ∃ O : U.Opens, t ∈ O ∧ Smooth (O.ι ≫ p)` |
| W→V nonsmooth at e(t) | `¬ ∃ O : W.Opens, e t ∈ O ∧ Smooth (O.ι ≫ pullback.snd ...)` |
| e(t)∈N | `e t ∈ W.zeroLocus (Set.range (fun k : Fin 2 ↦ ...))`; `Scheme.range_zeroLocusSubschemeι` identifies this set with the image of the full zero subscheme |
| Four equivalent conditions | The three adjacent biconditionals `(A ↔ B) ∧ (B ↔ C) ∧ (C ↔ D)` |
| Every geometric point xbar | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (xbar : Spec (.of Ω) ⟶ X)` |
| Every t above its image | `(t : U), q t = xbar default → ...` |
| Lift over xbar, with image exactly t | `∃ tbar : Spec (.of Ω) ⟶ U, tbar ≫ q = xbar ∧ tbar default = t ∧ ...` |
| Nonsmooth xbar implies lift maps into N | The implication from `¬ ∃ O : X.Opens, xbar default ∈ O ∧ Smooth (O.ι ≫ f)` to `∃ nbar : Spec (.of Ω) ⟶ N, nbar ≫ N.ι = tbar ≫ e` |

Here `W`, `N`, `N.ι`, `A`–`D` and the ellipses are explanations in this report;
the Lean theorem writes every construction in full. There are no file-local
notations, hidden implicit variables, let binders, or additional hypotheses.
The geometric point keeps its field Ω in both the lift and the factorization.
All schemes and Ω live in the common arbitrary universe used by Mathlib's Spec
and scheme-morphism API. The statement does not select a fixed small universe.

### Dependency declarations and interfaces read

- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; its full affine-local signature and stalkwise docstring
  were read. It is the recorded stalk-flatness notion.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, affine-local finite presentation.
- `def-pc-scheme` and `def-weil-affine-spectrum`:
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`. The scheme structure, locally ringed space morphism
  signature, spectrum construction and contravariant ring-map signature were read.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, the exact affine-local etale-ring-map class.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding and surjective stalk maps.
  The existing upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` supplies
  `Scheme.zeroLocusSubscheme` and `Scheme.zeroLocusSubschemeι` (lines 218–229):
  `(IdealSheafData.ofIdealTop (Ideal.span s)).subscheme` and its inclusion.
  Thus N has precisely the ideal generated by its two functions.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`. Smoothness at a point is expressed using an open
  smooth neighbourhood, as in the recorded pointwise etale-source theorem;
  it needs no added local-finite-presentation instances for p or W→V.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed`, and `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.SpecToEquivOfField`; the field/morphism encoding and equivalence's full
  signature and docstring were read. We use the inline field/morphism encoding.
- Added statement dependency `def-trf-universal-nodal-model`, an already landed
  definition node: `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel`,
  `nodalInteger`, `nodalBaseRing`, `nodalPolynomialRing`, `nodalRelation`,
  `nodalModelRing`, `nodalModel`, `nodalBase`, `nodalModelBaseMap`,
  `nodalIntegerMap`, `nodalPolynomialMap`, `nodalBaseMap`. All explicit bodies
  and docstrings were read. The pullback along `a ↦ h` is precisely the relative
  nodal model for an arbitrary, possibly nonaffine base. This adds an existing
  definition node to stmt_deps under brief-stage2 §5; it changes no node statement.

All recorded modules for stated proof dependencies are imported. In particular:
`SchemeEtaleSourceTargetProperties.scheme_etale_source_target_properties` gives
the two square implications; `SmoothEtaleLocalSource.smooth_at_iff_of_etale`
gives pointwise open-neighbourhood smoothness; their full signatures/docstrings
were read. The Mathlib leaf for the lift is
`Scheme.exists_fac_of_etale_of_isSepClosed` in
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` (lines 37–41), whose conclusion
fixes both Ω and the specified image point. The remaining plan imports cover
standard smoothness and its implication to smoothness, the affine comparison,
open/localization maps, first order thickenings and formal smoothness. No private
copy or unusable dependency interface was needed.

### Edge cases checked before writing

- Empty V: W and N are empty, the isomorphism is the empty one, and all relevant
  point quantifiers are empty. Empty U makes the equivalence/lift clauses vacuous
  but does not remove the model's isomorphism clause.
- h a unit: both N and V(h) are empty, so the model is everywhere smooth and
  the nonsmooth antecedent of the lift-factorization implication never holds.
- h=0: N≅V as schemes, and the two crossing axes are nonsmooth exactly at their
  simultaneous zero; all other points are in D(u) or D(v).
- Nilpotent nonzero h and nonreduced bases: V(h) and N retain the quotient scheme
  structure. Replacing them with reduced induced schemes would lose information;
  the delivered theorem does not do that.
- Characteristic 2: the derivative/Jacobian and the square-zero obstruction use
  no division by 2 and still give the same nonsmooth locus.
- q need not be surjective: every lift is conditional on a specified t above xbar.
  The direct prescribed-point Mathlib theorem has exactly this hypothesis.
- Nonclosed t and geometric points with transcendental residue extensions are
  included: etaleness makes κ(t)/κ(q(t)) finite separable, which embeds in Ω over
  the given residue map. No closed-point or finite-type-over-a-field condition
  has been added.

### Searches actually run

- `msearch.py ... leansearch`: “For the scheme xy=h over a base scheme the smooth
  locus is the complement of x=y=0”. Eight hits, including `Algebra.smoothLocus`,
  its cotangent criterion and generic scheme `IsSmooth` facts; no exact statement.
- `msearch.py ... leanfinder`: “The nonsmooth locus of the relative nodal curve
  uv=h is the closed subscheme u=v=0 and geometric points lift through etale maps”.
  Eight hits, including generic smooth/etale loci and standard smooth charts;
  none gives this scheme identification, four-way equivalence and lift clause.
- `msearch.py ... loogle`: `"smoothLocus", "MvPolynomial"`; zero hits.
- `msearch.py ... grep`: `nodal|Nodal|zeroScheme|zeroSubscheme`, subdirectory
  AlgebraicGeometry; zero Mathlib hits.
- Direct `rg` of `lean/WeilConjectures` for the item id, `nodalModel`,
  `nodalBaseMap`, `nodalChartCoordinate`, and nodal/smoothness terminology, and
  searches in `dag/lean_names_upstream.json`: no exact item theorem or universal
  model under those upstream names. Related geometric nodes and unrelated
  nodal constructions do not give this conjunction.
- Direct `rg` of `lean/Sheaf` for the same names found the exact universal model
  and `nodalChartCoordinate` in the downstream `NodalChartBoundaryShrinking`
  module. Its coordinate body is the same canonical expression used inline here;
  no second coordinate definition is introduced. Importing that downstream
  theorem for a coordinate alias would create a proof-import cycle, so its
  coordinate expression is used directly. The two results are distinct:
  shrinking states a missed-node removal and unit assertion, not this item.
- DAG search found `def-trf-universal-nodal-model`; its complete node and all
  recorded definitions were read and reused. `tools/blueprint_refs.py search
  'nodal model'` returned zero blueprint matches, and `ancestor` identified
  `lem-trf-local-term-locality`. No new node was created.

No statement correction, disputed assertion, source error, new node or dependency
module is needed. Only the item's lean record and the addition of the existing
universal-model definition dependency change in the DAG.

Validation: the first scompile invocation typechecked but reported two long
lines; both were wrapped. The second prescribed server compile accepted both
the sandbox module and the final library module without errors or warnings
(7.4 s and 2.0 s). Auto-implicit binding is disabled in both modes.

## Second reading by Q05

A separate second pass by the assigned worker, with the final node and Lean file
open; the dispatcher prohibits starting another agent. The maintainer supplies
the independent delivery review. This is not represented as an independent
second worker's reading.

I rechecked the binders against each row above: all four schemes and all five
maps occur with their original roles, f alone has the given flat/lfp assumptions,
and exactly b,q,e have etaleness assumptions. The two equations express both
commuting triangles in the correct composition order. The universal model uses
the section-induced map a↦h, not an arbitrary base map. Both coordinates are the
images of X 0 and X 1 in the actual quotient and are pulled back along the first
projection. The zero-subscheme isomorphism is required to commute with the base
projection, so an abstract unrelated isomorphism would not satisfy the statement.
The three biconditionals really connect all four conditions, including p and the
model map separately. The set membership is exactly the underlying image of the
nonreduced zero subscheme. The lift is quantified for every geometric point and
every prescribed t, keeps Ω, satisfies both q∘tbar=xbar and image(tbar)=t, and
factors through N under the nonsmoothness assumption. No special point is chosen
by a default on U; `default` is only the unique point of the spectrum of a field.

The second pass found no mathematical mismatch or need for a statement_change.
It confirmed that the sole extra statement dependency is the already landed
universal-model definition node. The two formatting warnings found by the first
compile were repaired before the clean compile; no linter was disabled locally.
