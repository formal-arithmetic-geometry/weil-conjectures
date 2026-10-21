## Worker report

The module `Sheaf.Paper.SfCbcDirectImageReductionUnit` states
`AlgebraicGeometry.ProEtale.StrictTower.DirectImageReduction.directImageReductionUnit`
with a sorry proof. Its five helper definitions contain actual categorical composites.
No node statement, dependency list or dependency record has changed. There are no
new independent notions or dependency modules and no disputed statement.

The mathematical sources read were `proetale.tex`, lemma-pushforward-Noetherian-case
(Tag 099N), especially (3) and (4); `sites-cohomology.tex`,
lemma-Rf-commutes-with-Rlim (Tag 0A07); and the current blueprint's
`sec-six-functors-basics/sk-prop-sf-cbc/fix-lem-exchanges.proof.md`, Step 5.
The node explicitly supplies the strict-diagram refinement and its five proof steps;
these are carried into the theorem's proof docstring. No proof is filled.

Hypotheses and setup correspond as follows:

| Node clause | Lean rendering |
| --- | --- |
| Commutative Noetherian ring A | `{A : Type (u + 1)} [CommRing A]`, `d : CompleteCoefficientDatum A`, field `d.noetherian` |
| Finitely generated ideal I | `d.ideal`, field `d.finitelyGenerated` |
| A/I additive torsion | field `d.quotientTorsion`, positive integer annihilator for each element |
| P_n perfect for every positive n | field `d.quotientPerfect`; `adicQuotientPerfect` is the actual quotient in degree zero |
| P_n finite as a set | `_hfinite : ∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))` |
| Arbitrary scheme morphism u:U→V | `{U V : Scheme.{u}} (f : U ⟶ V)`, without geometric finiteness assumptions |
| Original small pro-etale sites and constant coefficient sheaves | `StrictTower.coefficients A T`, the actual `constantSheaf (Scheme.ProEt.topology T)` |
| Module sheaves and ordinary unbounded derived category | `Modules A T`, `DerivedCategory (Modules A T)` |
| Strict tower category, positive index, diagonal | `Towers A T = ℕᵒᵖ ⥤ Modules A T`; `ConstantNormalization.delta`; index n means exponent n+1 |
| Rlim and diagram tensor reduction | existing `L A T` and `reduction d.ideal T`, the universal K-flat-normalized derived quotient tower |
| Completion C=L R | `completion d.ideal T := reduction d.ideal T ⋙ L A T` |
| Quotient-tensor map i and its specified completion unit | existing `augmentation d.ideal T`; `unit` is `(deltaLimit A T).inv` followed by L of this augmentation |
| Canonical derived direct images P and Q | existing `push A f` and `R A f`, both total right derived actual module direct image |
| Constant comparison chi | existing `chi A f`, incorporated in the normalization of `projection` |
| Counit-tensor diagram projection h | existing `(projection d.ideal f).app F`, defined as the mate of the K-flat-characterized `reductionPull` |
| Underived-composite normalized comparison b | existing `limitPush A f`, the conjugate of the identity-component ordinary square |
| rho=b inverse after L(h) | `comparison d.ideal f`, with associators and whiskering giving exactly that composite |

The conclusions correspond as follows:

| Node clause | Lean rendering |
| --- | --- |
| rho eta=P(eta), for every F | First conjunct, `(unit ... V).app (push.obj F) ≫ comparison.app F = push.map (unit.app F)` |
| rho is natural | `comparison` has type natural transformation; second conjunct writes its square for every `t : F ⟶ F'` |
| h natural, in particular on complete K | Third conjunct writes the projection naturality square for every `t : F ⟶ F'` |
| Complete means the specified unit invertible | `IsIso ((unit d.ideal U).app K)` in the final universally quantified conjunct |
| For complete K, h is an isomorphism of strict derived towers | `IsIso ((projection d.ideal f).app K)` |
| Evaluation is the canonical perfect-P_n projection formula map | `(ev A V n).map (projection.app K) ≫ (evalR A f n).app (reduction.obj K) = (finiteProjection d.ideal f n).app K` |
| This finite projection map is invertible | `∀ n : ℕ, IsIso ((finiteProjection d.ideal f n).app K)` |
| L(h) eta=b P(eta), as specified maps | Last equality in the final conjunct, with `L.map projection` and `(limitPush A f).hom.app (reduction.obj K)` |
| Equalities before evaluation and no uniform bounds | The first and last equations are in `DerivedCategory (Modules A V)` after applying the functor from strict derived towers; h itself is a strict derived-tower morphism. No bound, constructibility or exact-products binder occurs. |

`finiteTensorPull` evaluates the existing K-flat-normalized tensor-pullback comparison,
using `evalG` and associators. Thus it is the actual constant-quotient tensor balancing
map. `finiteProjection` is its mate under the existing canonical ordinary derived
adjunction; expanding `mateEquiv` gives pullback-tensor followed by counit tensor identity.
It is not an arbitrary map or isomorphism. Its evaluated source and target are canonical
models of the finite derived tensors. The displayed evaluation equation uses the actual
K-injective-normalized `evalR`, retaining the precise normalization requested by the node.
The helpers merely give names to the composites specified in this node, rather than
redefining sheaves, inverse systems, derived tensors or direct images.

Dependency declarations read and used:

- `Sheaf.Paper.CompleteCoefficientDatum`: `AlgebraicGeometry.Scheme.CompleteCoefficientDatum`
  and `adicQuotientPerfect`, including all fields of the coefficient datum.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparent
  to `SheafOfModules`; `Modules` uses that same module-sheaf category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `HasDerivedCategory.standard`, the ordinary localization of complexes at quasi-isomorphisms.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `CategoryTheory.Functor.ofOpSequence`,
  the strict inverse sequences used in the existing reduction module construction.
- `Sheaf.CategoryTheory.DiagramSiteRealization`: `CategoryTheory.exists_diagramSite_realization`,
  the diagram-site interpretation; the statement uses its strict functor-category model.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`; actual limit
  functor used via `L = completedRlim`, retaining the original pro-etale site universes.
- `Sheaf.Paper.CompletedPullbackAdjunction`:
  `CategoryTheory.ConstantCompletion.completedPullbackAdjunction`, whose completion unit
  is the quotient-tower unit. This item uses the explicitly stipulated normalization L(i)
  rather than introducing a second completion adjunction or an arbitrary unit.
- `Sheaf.Paper.ConstantTowerDirectImageNormalization`:
  `AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.{delta,push,pull,L,
  deltaLimit,chi,limitPush,reduction,augmentation,reductionPull,projection,
  constantTowerDirectImageNormalization}`. Their full definitions and normalization
  statements were read. In particular reduction has its universal derived counit and
  K-flat computation, and reductionPull has its representative characterization.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`; the
  existing normalized projection is this counit-tensor mate, not a chosen projection iso.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`; `limitPush` is its canonical
  constant-coefficient realization, constructed directly on the original site through
  the adjunctions, so no equality of site object and morphism universes is imposed.
- Additional directly imported proof dependencies: `Sheaf.Paper.RingedSitePerfectProjectionFormula`,
  `SheafOfModules.ringedSitePerfectProjectionFormula`;
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`, `CategoryTheory.Abelian.functorCategoryAbelian`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, `DerivedCategory.isIso_iff`.
  The finite-free constant-module and augmented-diagram proof nodes have no recorded Lean
  declaration in the read snapshot; their future statements are referenced by node id in
  the proof docstring. They are not additional assumptions of this statement.

Edge cases checked before writing: n=0 denotes P_1, never P_0; I=0 gives the identity
reduction/completion diagram; I=top gives zero quotient tensors and zero completion,
with complete objects precisely those with invertible zero unit. The zero ring and
empty scheme impose no extra nontriviality or inhabitedness hypothesis. Zero complexes,
unbounded complexes and arbitrary scheme morphisms are included. Each perfect quotient
has its own finite interval, with no common bound. A lies in the chosen coefficient
universe u+1 and schemes in u, so the small pro-etale site retains object universe u+1
and morphism universe u; no small-category specialization has replaced the original site.

Searches for an existing statement (2026-10-21):

- `msearch.py ... leanfinder "Derived direct image commutes with strict adic reduction towers and respects the completion unit"`:
  eight results about ordinary `AdicCompletion`, including
  `AdicCompletion.transitionMap_comp_reduceModIdeal` and `IsAdicComplete.of_comp_lift`;
  none state strict derived-tower projection or its completion-unit normalization.
- `msearch.py ... leansearch "Derived direct image of constant module sheaves commutes with adic completion and preserves its canonical unit on strict inverse sequences"`:
  eight results on ordinary adic completion, including `IsAdicComplete.of_lift`,
  `AdicCompletion.module`, `AdicCompletion.map_mk`, `AdicCompletion.of`; no match.
- `msearch.py ... loogle "CategoryTheory.Functor.rightDerived, CategoryTheory.Adjunction"`:
  zero hits.
- `msearch.py ... grep "completion.*[Pp]ush|[Pp]ush.*completion|[Pp]rojection[Ff]ormula" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `directImageReduction`,
  `direct_image_reduction`, `completionUnit`, `completion.*[Pp]ush`, `[Pp]ush.*completion`:
  found ordinary formal-completion results and multiple coefficient completion models.
  Read `CompletedDirectImageLimits` and its `towerProjection_properties`: this concerns
  `AdicCoefficientDatum` and completed coefficient sheaves, not this arbitrary constant A
  datum and the strict diagram maps requested here. It is not an exact existing match.
- `grep -rn "lem-sf-cbc-direct-image-reduction-unit" lean/WeilConjectures`: no hits.
- `rg` for `StrictTower.DirectImageReduction|SfCbcDirectImageReductionUnit` in both project
  source trees and `dag/lean_names_upstream.json`: no preexisting declarations.

Validation: the prescribed `scompile.py Q25 lem-sf-cbc-direct-image-reduction-unit ...`
compiled the sandbox file and its actual library module separately, cleanly, in 5.6 and
7.7 seconds. No global build or direct git command was run. Only the sandbox was edited.

## Second reading by Q25

The dispatcher explicitly forbids other agents; this is a separate second pass by the
same worker, with both the node and complete module open. The maintainer's independent
review remains the independent reading. I checked every row above against the actual
signature, especially the separate finite-set hypothesis absent from CompleteCoefficientDatum,
positive exponent shift, direction of b inverse, orientation of both unit equations,
completeness as invertibility of this precise unit, and the evalR normalization in the
finite projection equation. No mathematical mismatch was found. During compilation I
removed two invalid `.hom` field projections on inverse associator natural transformations;
these were syntax fixes and did not change the specified categorical composites.
There are no extra boundedness, finiteness-of-the-morphism or coefficient-flatness assumptions.
