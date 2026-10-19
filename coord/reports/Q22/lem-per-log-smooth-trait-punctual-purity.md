## Worker report

`Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity` states
`AlgebraicGeometry.Etale.log_smooth_trait_punctual_purity`, with proof `sorry`.
It follows ILO, Expose XVI, Definition 3.6.1, Theorem 3.6.2, Proposition 3.6.3,
and the final reduction using Proposition 3.6.5, printed pp.252--253.
The natural-language statement is unchanged from the current base.

Hypothesis and clause correspondence:

* The prime is `(ℓ : ℕ) (hℓ : ℓ.Prime)`. The coefficient field is the existing
  `regularClassCoefficients ℓ 1`, namely `ULift (ZMod (ℓ ^ 1))`, used inside the
  existing punctual-purity predicate. There is no independent coefficient choice.
* The trait is `Spec (.of R)` for `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's DVR class is a local principal ideal
  domain which is not a field; hence it is Noetherian and has dimension one.
  `(π : R)` and `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}` specify any
  uniformizer. `hR : IsUnit (ℓ : R)` renders invertibility on the trait.
* The canonical log structure is `(M : EtaleLogStructure (Spec (.of R)))`,
  `hfs : M.IsFineSaturated`, and `hcanonical`. The latter is an isomorphism of
  its actual underlying monoid presheaf with `divisorialLogPresheaf` for the
  generic open `D(π)`, commuting with `divisorialStructuralMap` and `M.alpha`.
  Thus it identifies the structural map, not merely the underlying sheaf.
  The basic-open argument is the image of π under `(Scheme.ΓSpecIso (.of R)).inv`.
* `(V : FineSaturatedLogScheme.{u})` provides the source log structure and its fs
  charts. `[IsNoetherian V.scheme]` and `hV : IsRegularScheme V.scheme` are exactly
  the underlying scheme hypotheses. There is no assumption of log regularity.
* `f : EtaleLogHom V ⟨Spec (.of R), inferInstance, M, hfs⟩` is one global log
  morphism. Its relative-test-object section maps satisfy naturality and
  compatibility with regular functions by the existing `EtaleLogHom` fields.
* `hf : f.IsLogSmooth` uses the existing chart criterion. It gives compatible fs
  charts covering every source point, finite kernel and finite cokernel torsion
  of invertible orders, and smooth canonical comparison. Over the canonical log
  trait, XVI 3.6.3 refines these to the node's injective uniformizer charts. The
  general criterion does not itself require an injective group map; no report
  claim identifies these two presentations definitionally.
* The conclusion `IsPunctuallyPure ℓ hℓ V.scheme` is the landed predicate of
  `def-per-punctual-purity`. It quantifies over every ordinary point w and uses
  `Spec (W.presheaf.stalk w)`, `Spec.map (W.residue w)`, and the dimension equality
  `ringKrullDim (W.presheaf.stalk w) = (d : WithBot ℕ∞)`. Its class is the
  adjoint transpose of the level-one, untensored canonical supported Kummer
  class, through the actual closed-support adjunction and exact-direct-image
  comparison. `IsIso` is imposed on this map. Its D+ presentation agrees with the
  ordinary D formulation through the fully faithful inclusion. The local
  Noetherianity, codimension, and invertibility witnesses are precisely the
  evidence needed to evaluate that class on regular Noetherian schemes.
* Completeness, strict henselianity and mixed characteristic are terminology
  introduced for downstream applications, not hypotheses of this theorem;
  consequently no such binder occurs here.

The statement dependencies are used through these declarations:

* `Sheaf.AlgebraicGeometry.PunctualPurity`: `IsPunctuallyPure`,
  `IsPunctuallyPureAt`, `punctualPurityClassMap`, `regularImmersionClasses`.
* `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`:
  `regularClassCoefficients`, `regularClassTwist`, `regular_immersion_class_calculus`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, with Mathlib's derived-category
  and bounded-below infrastructure; the current source was read using
  `scompile.py --source` because it is absent from the older local checkout.
* `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateTwist`,
  as used by the signed twists in the existing class calculus.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
* Mathlib `AlgebraicGeometry.ResidueField` and affine spectra: `Scheme.residueField`,
  `Scheme.residue`, `Spec`, `Spec.map`; `RingTheory.KrullDimension.Basic`: `ringKrullDim`.
* `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure`, `EtaleLogStructure.IsFineSaturated`, `EtaleLogHom`.
* `Sheaf.AlgebraicGeometry.LogRegularPair`: `divisorialLogPresheaf`,
  `divisorialStructuralMap`, `IsFineSaturatedMonoid`.
* `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth`,
  `FSLogChart.IsSmoothChart`, `FSLogChart.comparison`, `groupMap`, `cokernel`;
  its smooth and etale morphism notions are Mathlib's.

The landed proof dependency `lem-per-regular-log-smooth-monomial-chart` has module
`Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart` and declaration
`AlgebraicGeometry.regular_logSmooth_monomial_chart`. It is imported without
`public`. Its canonical M, structural-map equation, and single `EtaleLogHom` are
exactly the interface followed here. Its stronger uniformizer-chart hypothesis is
obtained by XVI 3.6.3 before applying it. The other two proof dependencies,
`lem-per-monomial-trait-punctual-purity` and
`lem-per-punctual-purity-etale-locality`, have no Lean records on the current base.
Their proof roles remain in the theorem docstring.

Edge cases checked: empty V (the conclusion is vacuous), generic and nonclosed
points (their own local spectra), dimension zero at generic points, arbitrary
uniformizers, equal and mixed characteristic, and monomial ramification
multiplicities divisible by ℓ. No completeness, henselianity, excellence, or
residue-field assumption has entered. The explicit universe u is shared by the
trait and scheme, as in the existing log interfaces; auto-implicit binding is off.

Searches retained from the saved packet: LeanFinder, query “Regular fine saturated
log smooth scheme over a trait is punctually cohomologically pure for etale finite
coefficients”, returned ordinary etale/smooth declarations; Loogle, query
`"LogSmooth", "PunctuallyPure"`, returned no match; LeanSearch, query “Punctual
cohomological purity canonical Kummer class closed point regular local ring finite
etale coefficients”, returned local-ring and ordinary etale declarations. Grep
`LogSmooth|PunctuallyKummerPure|TraitLogSmooth` gave no Mathlib match. The saved
search log is `searches.jsonl`. Fresh `rg` searches of the upstream
`WeilConjectures`, project `lean/Sheaf`, and `dag/nodes` found no existing theorem,
but found the newly landed `def-per-punctual-purity`; its declaration and full
module were read and reused. Upstream punctual weight purity is a different notion.

## Second reading by Q22

This is a worker self-check; no additional agent was started. With the node, item
module, `FSLogSmoothEtale`, `LogRegularPair`, `RegularLogSmoothMonomialChart`, and
`PunctualPurity` open, I matched every binder and the conclusion as above against
ILO XVI 3.6.1--3.6.5. The saved report incorrectly described finite-kernel charts
as injective by definition; that description is corrected. The source explicitly
assumes a log morphism to the canonically logged trait, which the repaired
signature supplies. The original node already says this; its natural-language
statement did not require correction. The saved `statement_change` wrongly
attributed a defect of the previous Lean encoding to the mathematical statement
and has been removed. Only `lean` and the allowed added `stmt_deps` change.

## Return repairs

H3/H12/H4: removed `HasTraitLogSmoothCharts` and its definition node. The statement
uses the canonical M and hcanonical equation, one `EtaleLogHom`, and the existing
`f.IsLogSmooth`. Added the landed `def-per-fs-log-smooth-etale` and
`def-trf-log-regular-pair` to `stmt_deps`. Corrected the false claim that all proof
dependencies lack Lean records, and imported the recorded monomial-chart module.

H2: removed both `lem-asd-etale-finite-twist-pullback` and
`lem-per-regular-immersion-class-calculus` records and modules from the packet.
Their live records and module bytes are used without edits or re-delivery.

Live-base duplicate check: Q03 has now landed `def-per-punctual-purity`, the same
notion as this packet's formerly new `def-per-punctual-kummer-purity`. Removed the
latter node and its `PunctualKummerPurity` module, imported `PunctualPurity`, and
added the landed `def-per-punctual-purity` to `stmt_deps`. No new definition or
dependency module is delivered. The source statement and proof route are unchanged.

## Validation

The prescribed initial dry run of the saved packet passed, commit d3bce311a7.
After removing the dependency re-deliveries, `scompile.py` compiled the then two
consumer modules without errors or warnings (10.2 s and 5.1 s for sandbox checks).
The final item compiled against the landed punctual-purity definition without
errors or warnings: sandbox check 6.0 s, library check 5.3 s. The final
`deliver2.py --no-push` passed preflight and compilation at commit 668e70a646,
listing exactly the report, item node, and item module. The clause-by-clause
self-check and final signature/record, line-width, sorry-only, and file-scope
checks passed before push.
