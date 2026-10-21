## Worker report

Item: lem-sf-etale-chart-left-compositor. Module:
`Sheaf.AlgebraicGeometry.EtaleChartLeftCompositor`.

This delivery constructs the specified natural isomorphism with real data and states
its naturality and compactification-change compatibility in the single postponed theorem
`AlgebraicGeometry.Etale.etaleChartLeftCompositor_spec`. The node is unchanged except for
its lean record. No new nodes, dependency repairs, or statement corrections are needed.
The auxiliary definitions belong to this node's specified comparison, and are listed in
lean.declarations; none chooses an unspecified isomorphism from a mere existence theorem.

Hypotheses, clause by clause:

* The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the existing ordinary module-valued etale-sheaf encoding, with no independent
  small coefficient universe imposed. It includes the zero ring.
* The five schemes are `{X Y U V P : Scheme.{u}}`, each explicitly `[IsNoetherian ...]`.
  Mathlib's IsNoetherian is equivalent to a finite affine Noetherian-ring cover.
* The five displayed maps have exactly the source and target of the node:
  f:X→Y, s:U→X, v:V→Y, i:U→P, p:P→V. The immersion conditions are
  `[IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]`.
* The specified equality fs=vpi is `(h : s ≫ f = (i ≫ p) ≫ v)`.
  `etaleChartCompactSupportTransport A h csf cipv` eliminates this equality and then
  uses the canonical comparison of the two compactifications of the identical map.
  It does not insert an arbitrary isomorphism between unequal functors.
* Separatedness and finite type of f,p are `[IsSeparated ...] [LocallyOfFiniteType ...]
  [QuasiCompact ...]`. These conditions for s,v,i follow from the immersions and
  Noetherianity; they are stable under composition. Chosen compactifications are the
  explicit parameters cf,cs,cv,ci,cp,csf,cip,cipv, including the three composite values
  used by the formula. The other possible composites are compactifiable by the same
  separated finite-type Noetherian hypotheses, without additional chosen data used
  by this formula.
* The categories are `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  These are exactly `DerivedCategoryModule A T` of def-weil-pbc-derived-categories.
  `DerivedCategory.Plus` is the full subcategory of cohomologically bounded-below objects.
* The ambient source of `etaleChartLeftCompositor` is
  `Plus.ι ⋙ (openImmersionLowerShriek ... s).mapDerivedCategory ⋙
  rightDerivedLowerShriekOfCompactification ... cf`, namely Rf_! Ds_! on D+(U).
  Its target is `Plus.ι ⋙ (lowerStar ... i).mapDerivedCategory ⋙
  rightDerivedLowerShriekOfCompactification ... cp ⋙
  (openImmersionLowerShriek ... v).mapDerivedCategory`, namely Dv_! Rp_! Di_*.
  The return type is a natural isomorphism, not Nonempty, so components, inverses,
  and the actual natural transformation are all supplied.

The specified six-factor formula is the real body of `etaleChartLeftCompositorPlus`:

1. `isoWhiskerRight (etaleChartOpenNormalization A s cs).symm _` is Rf_!(n_s^-1).
2. `etaleChartCompactSupportCompositor A s f cs cf csf` is alpha_(f,s).
3. After `etaleChartCompactSupportTransport A h csf cipv`, the inverse of
   `etaleChartCompactSupportCompositor A (i ≫ p) v cip cv cipv` is alpha_(v,pi)^-1.
4. The inverse of `etaleChartCompactSupportCompositor A i p ci cp cip`, whiskered
   on the right by Rv_!, is Rv_!(alpha_(p,i)^-1).
5. `etaleChartClosedNormalization A i ci`, whiskered twice, is Rv_! Rp_!(n_i).
6. `isoWhiskerLeft (Di_* ⋙ Rp_!) (etaleChartOpenNormalization A v cv)` is n_v,
   evaluated precisely at Rp_! Di_* H.

Lean composition reads in order of application, opposite to the node's function-composition
notation. The helper normalizations are the recorded ambient normalizations transported
through the fully faithful inclusion of D+, using `Functor.fullyFaithfulCancelRight`.
The helper compositor conjugates the existing `rightDerivedLowerShriekPlusCompIso` by
canonical changes between explicit and globally selected compactifications. It is therefore
the same canonical compositor for those choices, not another composition law.
`etaleChartLeftCompositor` applies Plus.ι to this six-factor isomorphism and uses the
existing `rightDerivedLowerShriekOfCompactificationPlusCompatibility` at the endpoints.
The exact-functor inclusion compatibilities are definitionally identity. Consequently its
component is exactly the node's ambient formula under the existing inclusion identifications.

All intermediate values and normalization inputs lie in D+: every functor and isomorphism
in `etaleChartLeftCompositorPlus` has a D+ source and target, including Rp_! Di_* H before
n_v. The ambient compatibility isomorphisms identify these values with the unbounded
compact-support candidates. No comparison on a generally unbounded input is used.

The first conjunct of `etaleChartLeftCompositor_spec` is the requested equation for every
`H' H : DerivedCategory.Plus ...` and every `a : H' ⟶ H`, with both endpoint maps spelled
out as the nested ambient functor maps. The second conjunct quantifies over fresh choices
of ALL eight compactifications, and states `c0 ≫ gamma' = gamma ≫ c6` as an equality of
natural transformations. Here c0 is the canonical comparison for cf→cf' evaluated after
Ds_!, and c6 is the comparison for cp→cp' evaluated after Di_* and then mapped by Dv_!.
Changes to cs,cv,ci,csf,cip,cipv have no endpoint effect but are quantified without restriction.
Identity and successive-change coherence is inherited from the recorded canonical comparison
cocycles. No right adjoint, exceptional pullback, or Hom comparison is introduced.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
* Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
* Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion.
* Mathlib.AlgebraicGeometry.Morphisms.Proper and .Separated: IsProper, IsSeparated.
* Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact:
  LocallyOfFiniteType, QuasiCompact.
* Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing; the finite-affine-cover scheme
  form used here is Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian.
* WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule;
  Mathlib's DerivedCategory, DerivedCategory.Plus and Plus.ι.
* WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  AlgebraicGeometry.Etale.openImmersionLowerShriek; its exact descent is mapDerivedCategory
  and its D+ restriction is mapDerivedCategoryPlus (the upstream ExactFunctor module).
* WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: Etale.lowerStar;
  Derived.UpperLowerStarCoherence: rightDerivedLowerStarPlus.
* WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  rightDerivedLowerShriekOfCompactification, its Plus variant and PlusCompatibility.
* Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization:
  etaleOpenCompactSupportNormalization, etaleClosedCompactSupportNormalization,
  etaleImmersionShriekNormalization. Their full signatures and docstrings were read.
* Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons and its public upstream imports:
  rightDerivedLowerShriekOfCompactificationPlusIso, PlusιIso,
  rightDerivedLowerShriekPlusCompIso and its choice-independence/associativity statements.
* Proof-only imports include Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives:
  Scheme.etaleModule_enoughInjectives, and Mathlib.Algebra.Homology.DerivedCategory.
  DerivabilityStructureInjectives: DerivedCategory.Plus.exists_injective_nonempty_iso;
  CochainComplex.isKInjective_of_injective is in the imported KInjective source.
  The ModuleCat-valued sheaf category also has the usual Grothendieck enough-injectives
  instance; no incompatible SheafOfModules coefficient encoding is used in the statement.

Edge cases checked: empty U and empty schemes, zero H and zero coefficients, negative
cohomological lower bounds, identity s,v,i, p not proper, identical compactifications,
and simultaneous changes to all intermediate choices. None requires an extra nonempty,
nonzero, proper-p, dimension, boundedness-above, or cohomological-dimension assumption.
The chart equality is eliminated even when its two chosen compactifications differ, so
identity maps do not accidentally identify distinct compactification data by definitional
reduction. No disputed statement or source fault was found.

Searches performed (the launcher msearch records these queries):

* leanfinder: "Canonical natural chart comparison Rf shriek Ds extension zero to Dv
  extension zero Rp shriek Di direct image for equal factorizations". Eight unrelated
  differential-geometric chart hits (writtenInExtChartAt, extChartAt and relatives);
  no etale compact-support chart statement.
* loogle: `"isoWhiskerRight", "NatIso"`. Only
  CategoryTheory.NatIso.op_isoWhiskerRight; not this statement.
* msearch grep: `chartComparison|ChartComparison|chartLeftCompositor` in CategoryTheory:
  zero hits.
* rg in lean/WeilConjectures and lean/Sheaf for chart comparisons and compositors:
  unrelated affine, tensor, determinant and etale-section comparisons; no supplied
  left compact-support comparison. Exact node-id search, including dag/lean_names_upstream.json,
  gave no declaration. The compact-support API search found the dependency declarations
  used above, rather than an already constructed factored-chart comparison.

Sources opened: literature/stacks-project/more-etale.tex, lemma-shriek-composition
(Tag 0F7J), including its choice-independence discussion, and lemma-pseudo-functor
(Tag 0F7K); the current blueprint preservation proof's opening factorization and final
composition/open-locality paragraphs. The source assumptions agree with this specialization.

## Second reading by NH

A fresh clause-by-clause self-check was made with the node and final module open; this is
not a claim of an independent worker review. The dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent review after delivery.

The reading checked the order and variance of all six factors: the source normalization
is inverted, all three compositors have the prescribed direction, only the closed
normalization sits inside both Rp_! and Rv_!, and the last open normalization is evaluated
after both Di_* and Rp_!. Equality transport includes canonical comparison of the middle
choices. The ambient endpoints have exactly the specified order, while the construction
restricts inputs to D+. The naturality equation is in Lean's left-to-right composition
order. The change equation has endpoint comparisons only for f and p, and quantifies
over changes in all other compactifications as well. Inverse data is supplied by the
natural-isomorphism construction, not by an existence assertion.

One presentation issue was corrected on this reading: the final theorem now repeats its
full explicit telescope, including all five Noetherian hypotheses and finite-type data,
instead of relying on automatic section-variable inclusion. No mathematical node change
was made. The theorem has exactly one sorry; all six helper definitions contain real data.

Validation: the final explicit theorem telescope compiled cleanly through scompile.py.
After adding direct imports of the recorded statement-dependency modules, deliver2.py
--no-push passed the server preflight and the per-file sandbox and library compiles
(`OK (dry run)`, 2026-10-21). No compiler warnings remain apart from the permitted sorry.
