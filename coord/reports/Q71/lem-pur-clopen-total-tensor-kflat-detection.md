## Worker report

Item: `lem-pur-clopen-total-tensor-kflat-detection`, group Q71, stage 2.

The module `Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection` states
`AlgebraicGeometry.Scheme.ProEt.clopen_total_tensor_kflat_detection`. Its sole postponed
proof is `sorry`. All helper definitions contain actual constructions or references to
published constructions, and the helper instances use existing witnesses. The original
natural-language statement and proof are unchanged. No new nodes or dependency repairs
are needed. The existing, landed `def-coef-ringed-tensor-hom-model` is added to `stmt_deps`
for its `WeilConjectures.coefficientTotalTensor` constructor. That constructor is precisely
the recorded `mapBifunctor` signed direct-sum totalization. Its dependency closure contains
208 nodes and does not reach this item.

Sources read: `literature/stacks-project/sites-modules.tex`, lemma
`lemma-sheafification-tensor` (0GMW) and its following Bilin universal-property display;
`sites-cohomology.tex`, `definition-K-flat` (06YN), and
`lemma-symmetric-monoidal-cat-complexes` (0FPQ). The theorem docstring carries all eight
steps of the accepted node proof, including zero-insertion testing and the degenerate cases.

Hypothesis and clause correspondence:

- Scheme and finite index set: `X : Scheme.{t}`, `I : Type w`, `[Finite I]`. There is no
  `Nonempty I` requirement and no imposed relationship between `w` and the other universes.
- Components and immersions: `Y : I → Scheme.{t}`, `j : ∀ i, Y i ⟶ X`, and both
  `[∀ i, IsOpenImmersion (j i)]` and `[∀ i, IsClosedImmersion (j i)]`.
- Disjointness: `hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i))
  (Set.range (j k))))`. Covering: `hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i)`.
- Ring sheaf: `R : Sheaf (topology X) CommRingCat.{max u (t + 1)}`. The recorded
  `Scheme.ProEt` has object universe `t+1` and arrow universe `t`; these remain distinct.
  The fixed module/coefficient universe contains the site. No ring nontriviality assumption
  occurs. `CommRingCat` packages exactly the commutativity of the node's ring sheaf.
- `R_i`: `(clopenTensorRings (j i)).obj R`, restriction along the exact composition
  functor used by `clopenRingRestriction`. Forgetting commutativity commutes definitionally
  with this restriction. The `clopenTensorModules` abbreviation is `ringedSiteModules`,
  hence Mathlib's `SheafOfModules`; it constructs no replacement category.
- `r_i`: `clopenTensorRestriction (j i) R` is exactly the recorded
  `clopenModuleRestriction` on the underlying ring sheaf, with its actual scalar actions.
  `clopenTensorComplexRestriction` is its `mapHomologicalComplex (.up ℤ)`.
- The ordinary comparison is `clopenTensorComparison ... h F H`, the inverse of the
  monoidal tensorator of the existential `h : (clopenTensorRestriction ...).Braided`.
  `Functor.Braided` extends `Functor.Monoidal`: it includes naturality, associativity,
  invertible unit comparison, both unitor equations, and preservation of symmetry.
  `clopenTensorUnitComparison` explicitly exposes the inverse unit isomorphism, from
  restricted global ring unit to the component ring unit. These are the existing sheaf
  tensor units representing `R` and `R_i`, respectively.
- The first condition on `h,b` quantifies over `F,H,U,x,y` and says that this comparison
  sends `clopenTensorPure R F H _ x y` to the component's `clopenTensorPure ... x y`.
  `clopenTensorPure` is the literal sectionwise `TensorProduct.tmul`, followed by the
  sheafification unit and `tensorObjIsoSheafification.inv`. Since restriction evaluates on
  the same test object over the component, `x,y` on the right are exactly `r_i x,r_i y`.
- The total comparison `b` is an isomorphism of bifunctors on pairs of arbitrary
  `CochainComplex ... ℤ`. Thus its components are chain isomorphisms and its naturality
  applies to all chain maps in both variables; there is no boundedness assumption.
- For every `P,Q,p,q,n,hpq`, the second condition is the equality of module morphisms
  `r_i.map (clopenTotalTensorSummand ...) ≫ b.f n = a.hom ≫ ιTensorObj ...`.
  This is the entire direct-sum summand equation, not merely an unspecified isomorphism
  of totals or an equation on cohomology.
- The third condition composes that summand inclusion with the actual total differential
  and then `b.f (n+1)`. Its right-hand side is `a.hom` followed by the sum of the restricted
  `P.d ▷ Q.X` inclusion and `p.negOnePow` times the `P.X ◁ Q.d` inclusion. Consequently it
  is exactly `r_i(dx) ⊗ r_i y + (-1)^p r_i x ⊗ r_i(dy)`. The arithmetic witnesses `hp,hq`
  only type the indicated summands and are quantified, not added mathematical hypotheses.
- The fourth condition is the signed-symmetry square tested on every direct-sum
  summand: restrict `(p*q).negOnePow • (β_ (P.X p) (Q.X q)).hom ≫ ιTensorObj Q P`,
  then apply `b(Q,P)`, or first apply `a(P^p,Q^q)` and the component signed exchange.
  `CochainComplex.Monoidal.ι_braiding_hom` is exactly this defining summand formula.
  Coproduct extensionality makes these equations equivalent to compatibility of the
  chain symmetries themselves, for positive and negative degrees. This presentation
  avoids expensive synthesis of the full monoidal structure on all complexes.
- Coproduct preservation: `∀ i (K : Type (max u (t+1))), PreservesColimitsOfShape
  (Discrete K) (clopenTensorRestriction ... )`, including empty coproducts.
- Adjunction to zero insertion: the final clause quantifies over every `e` with
  `e ⋙ r_i ≅ 𝟭` and `IsZero ((e ⋙ r_k).obj N)` for `k ≠ i`, and concludes
  `Nonempty (r_i ⊣ e)`. In particular this applies to the recorded insertion obtained by
  gluing the tuple with `N` at `i` and zero elsewhere. This formulation does not choose a
  different gluing inverse: those component conditions uniquely characterize that
  insertion up to natural isomorphism because the recorded global restriction is an
  equivalence. It also covers every choice supplied by the dependency's existential data.
- Flat detection is the first equivalence, using the recorded `IsFlatOnSite` on both sides.
  It quantifies over every module sheaf and has the defining order test module tensor `F`.
- K-flat detection is the second equivalence, using the recorded
  `IsKFlatIndependentCoefficients` on both sides and every integer-indexed complex. That
  predicate tests every acyclic complex with `Tot(test ⊗ P)`. No flat-term hypothesis or
  bound occurs.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` supplies continuous site maps.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`:
  `clopenRingRestriction`, `clopenModuleRestriction`, `clopenModuleRestriction_additive`,
  and the normalization and insertion clauses of `clopen_ringed_module_gluing`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, `cochainModulesSymmetric`, `cochainModulesPreadditive`, and
  the tensor colimit instances, on the existing localization tensor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`; the objects needed
  here are the underlying `CochainComplex ... ℤ`, with no derived localization chosen.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `Mathlib.Algebra.Homology.Monoidal`: `HomologicalComplex.ιTensorObj`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `WeilConjectures.coefficientTotalTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, with the actual tensor and acyclicity.
- Proof imports: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`tensor_bilinear_universal`); `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`
  (`totalTensor_signed_coherence` and the signed formulas);
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` (`HomologicalComplex.Acyclic`).
  The specialized bilinear-universality theorem is imported for its proof route, not used
  to identify different site universes. Its same-universe statement does not constrain
  the present statement; the underlying sheafification universal property gives the
  indicated bilinear characterization on this site as in the source.

Edge cases checked before finalizing: empty `I` (the cover forces `X` empty); a nonempty
partition containing an empty component; a singleton partition with its identity immersion;
zero ring sheaves; zero module/complex; complexes with infinitely many nonzero positive and
negative degrees; degrees `p=-1`, `q=-2` for the differential and symmetry signs; and the
empty coproduct. None requires an extra nonemptiness, nonzero, boundedness, or flat-term
assumption. The three nonfinite conditions are on genuine arbitrary input complexes and
module sheaves, not on a chosen resolution.

Searches actually run, retained in the dispatcher's `searches.jsonl`:

- LeanFinder: "Restriction of module sheaves to clopen proetale components commutes with
  total tensor and detects K-flatness". Eight hits concern condensed monoidal structure
  and projectivity, not this normalized clopen assertion.
- LeanSearch: "Restriction to clopen components of a ringed site preserves tensor products
  and detects flat sheaves and K-flat complexes". Eight hits concern ordinary flat modules
  or scheme restriction, not the assertion (log from the interrupted work).
- Loogle: "Functor.Monoidal, CochainComplex.mapBifunctor, PreservesColimitsOfShape" returned
  no hits with an unknown-identifier note; this is not evidence of nonexistence.
  The fully qualified follow-up "CategoryTheory.Functor.Braided,
  CategoryTheory.Functor.Monoidal.μIso" returned zero hits.
- `msearch.py ... grep 'clopen.*tensor|tensor.*clopen|kFlat.*iff'`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` for clopen/tensor and K-flat patterns, and `grep -rn` for
  this node id: no matching declaration. `rg` of `lean/Sheaf` finds the parent
  `ProEtaleFiniteClopenTensorCalculus` and several derived or coefficient-specific results.
  The parent is broader in its derived conclusion but omits the explicit summand
  differential, signed-symmetry square, and universal coproduct/adjunction clauses of this
  item. It is downstream of this item in the DAG and is not an exact existing match.
  The present transparent abbreviations expose the same recorded constructions without
  importing that downstream theorem or defining another tensor, flatness or K-flatness.

No statement fault or mathematical dispute was found.

## Second reading by Q71

This is a second self-audit with the final node and module open; no other worker was
started, as required by the dispatch brief. The maintainer's independent delivery review
remains independent of this self-audit.

The first draft failed because it left additivity implicit, allowed ambiguous universe
inference through a raw sheafified pure-tensor expression, and contained an overlong line.
The file now exposes the recorded additivity instance, gives explicit universe arguments
and the actual pure-tensor construction, and respects the 100-character limit. No mathematical
hypothesis or conclusion was changed to fix elaboration. The ordinary unit isomorphism is
exposed explicitly. The total bifunctor uses the existing `coefficientTotalTensor`
constructor. The differential and signed-symmetry assertions are morphism equalities
on every actual direct-sum summand, so their content is unchanged while avoiding
repeated synthesis of the full monoidal structure on complexes. I rechecked the orientations of the inverse tensorator, unit comparison,
chain comparison, summand square, differential equation, and braiding square. The equations
have exactly the source and target in the node. The insertion normalization tests all other
components against zero and retains the natural identity comparison at its own component.
The signed differential uses the first-factor degree; the complex braiding uses the product
of the two degrees. This reading also checked that the new API dependency does not produce
a dependency cycle and that no definition contains `sorry` or arbitrary map choices.

The helper `clopenTotalTensorSummand` is the existing `ιMapBifunctor` inclusion
with its codomain stated through `coefficientTotalTensor`. It adds no data or axiom;
its explicit type prevents repeated unfolding of the entire total complex.
