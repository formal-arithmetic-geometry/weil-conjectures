## Worker report

The module `Sheaf.RingTheory.PolynomialDifferentialBaseChange` states
`Algebra.CotangentResolution.polynomial_differential_base_change`. The only theorem
has proof `sorry`. No definitions, instances, new nodes, or dependency repairs are added.
The node statement is unchanged. Its statement dependencies gain the already landed
`lem-pur-derived-change-of-rings`, because the signature explicitly uses its ordinary
universal derived scalar-extension functor and counit.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Four commutative rings and their commutative square | `f g : Arrow CommRingCat.{u}` and `q : f ⟶ g`; `f.left=A`, `f.right=C`, `g.left=A'`, `g.right=C'`; `q.left` and `q.right` are the vertical arrows and `q.w` is the square equation. |
| Augmented simplicial A-algebra P | `P : Augmentation f`, using the recorded simplicial algebra, base natural transformation, augmentation natural transformation and triangle. |
| Polynomial terms on arbitrary sets | `hpolynomial`, with `I : Type u`, polynomial ring isomorphism `e`, and the equation on every coefficient making it an A-algebra isomorphism. No finiteness condition on I. |
| P' is P tensor_A A', with induced operators | `P' : Augmentation g`, `h : AugmentedMap q P P'` and `hbase` asserting `CategoryTheory.IsPushout` termwise. A tensor product of commutative algebras is exactly this ring pushout. The naturality of `h.map` and the base maps makes its operators the induced tensor-product operators. The result is invariant under the unique isomorphism between realizations of this pushout; no arbitrary substitute for tensor product is assumed. |
| Augmentation p tensor a' maps to f(epsilon(p))a' | `h.augmentation` fixes it on `h.map` (the p tensor 1 inclusion), and `P'.triangle` fixes it on the A' inclusion. The pushout property uniquely determines the ring map from those values. Multiplicativity gives the displayed pure-tensor formula. |
| Alternating cochain convention and actual differential modules K, K' | `D : DifferentialModel P`, `D' : DifferentialModel P'`, and `differentialComplex D`, `differentialComplex D'`. These are the recorded models, whose terms are canonically identified with the actual differential tensor modules and whose operators have the prescribed generator formula. `negativeComplex` is the alternating-face complex extended by zero to cohomological degree -n. Existence of these models is the recorded `Coherence.differentials`; a model is coordinate data, not an extra mathematical hypothesis. |
| Every term of K is flat, including positive zero terms | First conjunct `∀ i : ℤ, Module.Flat f.right ((differentialComplex D).X i)`. |
| K is K-flat | Second conjunct, `(HomologicalComplex.quasiIso ... (.up ℤ)).kFlat (differentialComplex D)`, exactly the recorded ordinary-module predicate. |
| Canonical K-flat computation isomorphism c_K | Third conjunct says the counit at K of `ordinaryDerivedChangeOfRings q.right.hom` is an isomorphism. This counit has source derived scalar extension of QK and target Q of termwise ordinary scalar extension. Thus `asIso` of it is precisely c_K, not an arbitrary comparison. |
| Isomorphism theta of the ordinary scalar-extended complexes | Existential `θ`, with source `extendScalars.mapHomologicalComplex.obj K` and target K'. |
| theta sends (dp tensor c) tensor b' to d(p tensor 1) tensor f(c)b' | Second generator clause: `θ.hom.f (-n)` sends `b' tensor complexGenerator D n c p` to `complexGenerator D' n (q.right c * b') (h.map.app ... p)`. Existing scalar-extension conventions place the coefficient tensor factor first; symmetry of tensor factors converts this verbatim to the source convention. |
| Component maps commute with every face and degeneracy | Existential simplicial isomorphism `s : D.module ⋙ extendScalars ... ≅ D'.module`, with the identical formula in actual term coordinates in the first generator clause. A natural transformation commutes with every simplex operator. Both `s` and `θ` are fixed by the same spanning generators, so these are the components of the same comparison. |
| Canonical isomorphism Theta in D(C') | Existential `Θ`, using `ordinaryDerivedExtendScalars` and `DerivedCategory.Q`. |
| Theta = Q(theta)c_K | Final equality `Θ.hom = counit.app K ≫ DerivedCategory.Q.map θ.hom`. Lean composition order is left-to-right. |
| No resolution condition and no flatness hypothesis on the maps | No `IsPolynomialResolution`, augmentation surjectivity, quasi-isomorphism, or `RingHom.Flat` hypothesis appears. |

Dependencies read and used:

- `Mathlib.Algebra.MvPolynomial.Basic` / `MvPolynomial`, `MvPolynomial.algHom_ext`,
  and `Mathlib.Algebra.MvPolynomial.Eval` / `MvPolynomial.aeval`: actual polynomial algebra.
- `Sheaf.RingTheory.CotangentResolutionCoherence` /
  `Algebra.CotangentResolution.Augmentation`, `AugmentedMap`, `DifferentialModel`,
  `differentialTerm`, `differentialGenerator`, `negativeComplex`,
  `differentialComplex`, `complexGenerator` (full signatures and docstrings read).
- `Mathlib.RingTheory.Kaehler.Basic` / `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`, and
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic` /
  `CommRingCat.KaehlerDifferential`: used by those recorded differential terms.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` /
  `CategoryTheory.MorphismProperty.kFlat` applied to ordinary cochain quasi-isomorphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` /
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.TraceFormula.OnePointDerivedRingIdentification` /
  `CategoryTheory.OnePointDerivedRingIdentification`,
  `CategoryTheory.one_point_derived_ring_identification`: records the specified
  interpretation of ordinary derived scalar extension through singleton-site evaluation.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `Basic`, `Map` /
  `TensorProduct`, `TensorProduct.lift`, `LinearMap.rTensor`, and
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` / `ModuleCat.extendScalars`.
- `Mathlib.RingTheory.RingHom.Flat` / `RingHom.Flat`, and
  `Mathlib.RingTheory.Flat.Basic` / `Module.Flat` (the latter is used directly).
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic` /
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` /
  `ModuleCat.OrdinaryDerivedChangeOfRings`, `ordinaryDerivedChangeOfRings`,
  `ordinaryDerivedExtendScalars`: the universal pair and its K-flat counit.
- Proof imports: `Mathlib.RingTheory.Kaehler.Polynomial` /
  `KaehlerDifferential.mvPolynomialBasis`, and
  `WeilConjectures.Algebra.Homology.BoundedFlatKFlat` /
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`.
  The proof-only node `lem-trf-simplicial-differential-base-change` has no recorded
  declaration in the read clone; it is referenced in the proof docstring and no
  invented import or declaration is substituted. It supplies no missing notion
  in this signature, so no dependency module is needed to state this item.

Edge cases checked before drafting: I_n empty (P_n=A, relative differentials zero);
infinite I_n (only finite-support tensor expressions are used); zero rings C or C';
identity ring maps; nonflat maps such as Z to Z/2; and arbitrary augmented polynomial
simplicial algebras whose augmentation is not surjective or not a quasi-isomorphism.
The polynomial and pushout hypotheses do not exclude any of these cases. Positive
cochain degrees are zero by the recorded extension-by-zero construction. The
single arbitrary universe u permits arbitrary sets and rings after common lifting;
there is no finite/countable index restriction or separate smaller test universe.

Searches made using `batch2/msearch.py Q57 lem-trf-polynomial-differential-base-change`:

- LeanFinder: “An augmented simplicial polynomial algebra has a K-flat differential
  complex whose derived scalar extension is its base changed differential complex”.
  Eight hits, including `KaehlerDifferential.moduleBaseChange'`,
  `tensorKaehlerEquiv`-related constructions and presentation cotangent base-change
  equalities. None states this full simplicial/K-flat/derived assertion.
- Loogle: `"tensorKaehlerEquiv"`. Eleven hits, notably `tensorKaehlerEquiv`,
  `tensorKaehlerEquivBase` and their generator formulas; module-level results only.
- grep: `tensorKaehlerEquiv|cotangentComplexBaseChange` in `RingTheory/Kaehler`.
  Five hits in `TensorProduct.lean`, none giving this statement. Read its tensor
  equivalences and generator formulas.
- LeanSearch: “The differential complex of an augmented simplicial polynomial
  algebra is K-flat and its derived base change equals the base changed differential
  complex”. Eight hits: augmentation, differential module base change, and the
  presentation cotangent map; no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `polynomial.differential|PolynomialDifferential|DifferentialBaseChange|differentialBaseChange|lem-trf-polynomial-differential-base-change`:
  found related polynomial differential constructions and the cotangent base-change
  consumer, but no declaration of this statement. Read
  `Sheaf.RingTheory.CotangentFlatBaseChange` to confirm its theorem concerns the
  cotangent complex under derived Tor-independence, not this arbitrary differential
  complex. Its proof uses exactly the comparison stated here.

Source checked directly: `literature/stacks-project/cotangent.tex`,
`lemma-flat-base-change-cotangent-complex`, proof (Tag 08QQ). The item isolates
its differential-flatness and scalar-extension identification, and does not copy
that lemma's separate hypothesis needed for comparison to the actual cotangent
complex of the target ring. No statement dispute or node fault was found.

## Second reading by Q57

Separate in-thread rereading of the complete node and the delivered signature;
the dispatcher prohibits starting another agent, and the maintainer supplies the
independent review. Checked that the square's right map is used on c, its left map
is used only for algebra pushouts, and P' has the correct augmentation. Checked
that `hpolynomial` retains coefficient compatibility but imposes no resolution
condition. Checked both formulas against tensor-factor symmetry and that the
counit has the correct direction for c_K. Checked that `s` is an isomorphism of
simplicial objects, not just unrelated isomorphisms in each degree. Its generator
formula and theta's formula determine the identical component comparison.
The derived equality fixes Theta rather than allowing an arbitrary isomorphism.
The compiler's first diagnostic exposed namespace resolution of `IsPushout` to
`Algebra.IsPushout`; it was corrected to `CategoryTheory.IsPushout`, which takes
actual bundled ring maps. No mathematical hypothesis or conclusion changed.
