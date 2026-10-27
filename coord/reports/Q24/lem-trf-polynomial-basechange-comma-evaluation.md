## Worker report

Item: `lem-trf-polynomial-basechange-comma-evaluation`. The main module is
`Sheaf.RingTheory.PolynomialBaseChangeCommaEvaluation`; its theorem is
`Algebra.PolynomialPresentation.polynomial_baseChange_comma_evaluation`.
There is one postponed theorem, with `sorry`, and no proof work. Its auxiliary record
`PolynomialCommaEvaluation` spells out the whole existence assertion, without choosing
objects from a mere existence theorem. All category and functor definitions have actual data.
The source is Stacks `cotangent.tex`, Tag 08QW, case i=3, with the polynomial-target
computation in Tag 08QV. I read both source statements and proofs. The printed reference
C_{H/C} is interpreted as C_{H/B}, exactly as the DAG requests.

Hypotheses and clauses, matched to Lean:

- A → B → C, commutative rings: `(I A B C : Type u)`, `[CommRing A]`,
  `[CommRing B]`, `[CommRing C]`, `[Algebra A B]`, `[Algebra B C]` in the explicit
  section binders. No unrelated A-algebra structure on C is imposed.
- Common infinite bound: `[Infinite I]` and `Nonempty (A ↪ I)`, `Nonempty (B ↪ I)`,
  `Nonempty (C ↪ I)` in the theorem. All variable sets, including `E`, are subsets of I.
  All presentation categories are `SmallCategory` in universe u, and the bar system uses
  modules in that universe and the standard u+1 localization universe. A polynomial ring
  on a subset of I over B also fits the bound, since I is infinite and B embeds in I.
  The coefficient ring R is arbitrary in the module universe, as in the recorded bar and
  polynomial-top dependencies. Larger inputs are handled by the size convention.
- E_C: `(ArbitraryTarget.Pair I A B C)ᵒᵖ`; an object gives lower variables S,
  upper variables T, lower augmentation A[S] → B, and the upper-variable values in C.
  `Pair.augmentation` is the induced compatible map Q=A[S][T] → C.
  `PairHom` has the lower and upper algebra maps, the two augmentation conditions,
  `upperBase`, and the uniquely determined base-change map with `baseSquare`.
- D_C: `(ArbitraryTarget.Target I B C)ᵒᵖ`, with `Target.augmentation` equal to aeval,
  and augmentation-preserving B-algebra maps as morphisms before taking opposites.
- u: `(ArbitraryTarget.baseChange I A B C).op`. In polynomial coordinates the
  pushout Q tensor_P B is B[T], and `Pair.specialize` is q ↦ q tensor 1 in this model.
  B-linearity and the square on specialization fix its action on morphisms uniquely.
- V=(H → C), H polynomial: `E : Set I`, `δ : MvPolynomial E B →ₐ[B] C`,
  `commaTarget I B C E δ`. Writing H=B[E] is the source's bounded polynomial model;
  it does not assert that C is polynomial. Its augmentation sends X_e to δ(X_e).
- E_H and D_H: the existing `(Pair I A B E)ᵒᵖ` and `(Target I B E)ᵒᵖ` from the
  recorded polynomial-top dependency, not new copies. v is `(baseChange I A B E).op`.
- j: `(postcomposeTarget I B C E δ).op`. It composes augmentation with δ and preserves
  the underlying polynomial B-algebra and algebra map.
- Identity-cover topology: the category bar model is by definition on the bottom topology;
  `CategoryColimitBarModel.point` includes its constant-ring sheaf and module-presheaf
  identification. Thus no separate sheaf hypothesis or stronger covering structure is needed.
- The actual comma category: `PolynomialComma` is Mathlib's `StructuredArrow (op V) u`.
  `PolynomialCommaEvaluation.equivalence` is an equivalence from this category to E_H.
- Forward object formula: `forwardObject` keeps lowerVars, upperVars and lower, and takes
  the upper variable to `Z.hom.unop.val (MvPolynomial.X i)`. `forwardAugmentation` spells
  out γ=α∘specialize on the entire Q, not only variables.
- Inverse formula: `inverseObject` composes the upper-variable values with δ and keeps the
  same P,Q. `inverseArrow` is the full B-algebra map `W.target.augmentation : B[T] → H`.
  In this pushout model its value on specialize(q)*C(b) is γ(q)*b, so it is precisely
  the required α(q tensor b), not an arbitrary lifting map.
- Morphisms: `forwardLower`, `forwardUpper`, `inverseLower`, `inverseUpper` identify the
  underlying pair of maps in both directions. HEq compares these exact maps across equal
  coordinate fibres; the object fields fix those fibres. The equivalence supplies identity,
  composition, unit and counit laws.
- R and K: the fields quantify `(R : Type u) [CommRing R]` and every
  `K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R`.
- G=j⁻¹K and v⁻¹G: `polynomialRestriction` is precomposition by v.op ⋙ j.op,
  with the double opposites accounting for presheaves on the opposite algebra categories.
- F_V: `commaRestriction` is precomposition by `(StructuredArrow.proj V u ⋙ u).op`;
  at Z it is exactly K(u(Z.right)).
- Coefficient identification: `coefficient` is an isomorphism F_V ≅ e.op ⋙ v⁻¹G.
  `coefficientIdentity` requires its value on each coefficient element to be that same
  element, using HEq only to transport through the equal augmented-algebra objects.
- Derived colimits: the source and target of `comparison` are the two dependency bar
  functors followed by `DerivedCategory.Q`. Their canonical identification with Lπ_!
  is part of `CategoryColimitBarModel.model`. This is a natural isomorphism in D(R),
  rather than a per-degree homology assertion.
- Canonical direction/reindexing: `represented` requires its hom component to be exactly
  `DerivedCategory.Q.map (system.map equivalence.functor (RingHom.id R) coefficient.hom)`.
  The dependency's `formula` is the required chain reindexing and coefficient identity.
- Evaluation object: `commaEvaluation` evaluates K at the double opposite of V, then
  applies `CochainComplex.singleFunctor _ 0`. By the definition of j and `topTarget`,
  this is also G(H → H)[0], with no arbitrary object isomorphism.
- Comma augmentation: `commaAugmentation` is a natural transformation to this evaluation
  functor; `commaFormula` uses the recorded `IsEvaluationAugmentation` and restrictions
  `fun Z ↦ K.map Z.hom.op`. It sends (Z,x) to K(a)x in degree zero and is zero in every
  nonzero degree, exactly as that predicate specifies.
- Polynomial-target augmentation: `polynomialAugmentation` is also a natural transformation.
  `polynomialFormula` fixes its values to restriction along `j(toTop W.target)` on every
  zero-degree generator and zero in every other degree. These are precisely the specified
  maps of `polynomial_top_evaluation`, with F=G. The generator prescription uniquely fixes
  the entire augmentation, including the cited reindexing-to-D_H factorization.
- Compatibility: `augmentationCompatibility` states equality of chain maps, with the comma
  map equal to canonical reindexing by e followed by that polynomial augmentation.
- Quasi-isomorphism and naturality: `augmentationIso` states `IsIso (Q.map εComma)`;
  this is quasi-isomorphism of that particular specified augmentation. `comparison` is a
  natural isomorphism and both augmentations are natural transformations in K.
- No polynomiality of C or flatness of either given ring map appears in any binder.

Dependency declarations read and used:

1. `def-weil-size-convention` is a metatheoretic convention (its lean record has no declaration).
   Its explicit universe and small-model requirements are implemented as described above.
2. `Sheaf.CategoryTheory.SiteCoveringAxioms`,
   `CategoryTheory.Precoverage.IsSiteForCoverings`: read the full declaration/docstring.
   For these identity-cover sites the dependency bar model already uses the bottom topology.
3. `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
   read its full abbreviation/docstring; the bar model's constant coefficient point uses
   this exact module-sheaf identification with ordinary ModuleCat-valued presheaves.
4. `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `HasDerivedCategory`,
   `DerivedCategory.Q`: read their signatures/docstrings. The instances are the recorded
   `categoryBarModuleDerived` instances provided by the bar dependency.
5. `Sheaf.CategoryTheory.DerivedColimitBar`, `CategoryColimitBarModel`,
   `CategoryColimitBarSystem`, `CategoryColimitBarModel.generator`:
   read the entire module, including models, maps, generator formula, comparison and
   natural-transformation homotopy clause. The item is parametrized by the actual system,
   as is the polynomial-top theorem; `categoryColimitBarSystem_exists` provides existence.
6. `Sheaf.RingTheory.CotangentLowerShriekPolynomialTop`,
   `Algebra.PolynomialPresentation.IsEvaluationAugmentation`, `polynomial_top_evaluation`:
   read the full signatures and docstrings. The original Pair/Target/baseChange/toTop
   from `Sheaf.RingTheory.PolynomialPresentationPairCategories` are retained for H.
7. Proof dependency `lem-weil-pbc-algebra-tensor-pushout-universal-property` has a Mathlib
   match, not a lean record. Read `Algebra.TensorProduct.includeLeft`, `includeRight`,
   `ext` in Basic and `productMap`, `productMap_apply_tmul`, `productMap_left`,
   `productMap_right` in Maps. Maps is a plain proof import.
8. The new definition node supplies arbitrary-target bounded categories. Its module is a
   public statement import, as are the polynomial-top and StructuredArrow modules.

Edge cases checked before writing: C arbitrary and non-polynomial, nonflat A → B and B → C,
E empty (H=B), empty lower and upper variable sets, infinite variable sets within the bound,
identity δ, noninjective/nonsurjective δ, zero rings (with only their possible unital maps),
zero coefficient ring and zero presheaf, and degree-zero/nonzero-degree augmentation formulas.
No freeness of a map of augmentations, finite-presentation, surjectivity, or nonempty
variable-set hypothesis occurs. For the empty upper set, B[T]=B and the universal property
still gives the unique compatible α; empty lower variables similarly give P=A.

Searches: ran the prescribed msearch.py calls for leanfinder (comma/base-change/evaluation
query), loogle (`"MvPolynomial", "TensorProduct"`), Mathlib grep
(`(polynomial|cotangent).*(comma|shriek)|(comma|shriek).*(polynomial|tensor)`), and leansearch
(small augmented polynomial pairs over an arbitrary algebra). The first found eight algebra
presentation tensor-model/base-change declarations, the second only the unrelated integral
closure lemma, grep four unrelated hits, and leansearch eight general algebra/base-change
APIs. None states this equivalence with its coefficients and augmentation. Searches of
`lean/WeilConjectures` for the item id and polynomial/comma patterns found no exact match;
`lean/Sheaf` found the existing polynomial-target categories/theorem and the coordinate-free
CotangentSites interface, which I read. `dag/lean_names_upstream.json` has no proposed name.
A DAG scan found no bounded arbitrary-target category node. `tools/blueprint_refs.py search
"polynomial presentation"` found only the unrelated algebraic-groups unit sk-d-geometry.
The exact search results also appear in the new node's mathlib_searches.

No STATEMENT-DISPUTED issue or statement correction. The item node changes only lean and
adds the new definition node to stmt_deps. No dependency record is replaced.

Validation: scompile.py compiled both files in module mode, separately in dependency order,
against the live published library. The main module compiled without errors or warnings;
the definition module also compiled cleanly. All variables/universes are explicitly bound.
Delivery dry run and final delivery are recorded below after running the prescribed wrapper.

## New nodes

`def-trf-polynomial-presentation-arbitrary-target` introduces the bounded coordinate
categories Target and Pair with arbitrary target C, their augmentation-preserving morphisms,
their category instances and canonical baseChange functor. The source is the construction
before Stacks 08QU and the arbitrary-C comma computation in 08QW. The existing bounded
coordinate node fixes C=B[E], so it cannot represent the present E_C and D_C. The existing
CotangentSites model uses coordinate-free rings of object universe u+1 and arbitrary
polynomial witnesses; it does not provide this common bounded coordinate interface to the
already recorded polynomial-target theorem. This is the missing general-target extension,
not a replacement of those existing categories. Over H the item uses the original modules.
Searches and their outputs are recorded above and in the node. No new theorem or unproved
definition is introduced by the node; category laws are the structural proofs of the data.

## Second reading by Q24

The dispatcher explicitly forbids subagents and supplies maintainer independent review.
This section is a separate in-thread rereading, not a claim that another worker reviewed it.
I reopened the node and both delivered files and checked every clause against the matching
list above. The object and morphism formulas fix both directions of the equivalence, rather
than merely asserting equivalent unnamed categories. The specified bar comparison is an
actual natural isomorphism in D(R) with its hom fixed to system.map. Both augmentations are
natural in K and fixed on all generators/nonzero degrees, and their equality is at chain
level. The new category has arbitrary target C and the old category remains in use over H.
No discrepancy requiring a statement_change was found. During compilation I corrected the
orientation of AlgHom.comp_assoc and removed an erroneous unop in the comma generator
formula; the final clean compile checks those exact formulas. Default module mode and
explicit universe binders are present. There is one named sorry, the assigned theorem.

The prescribed `deliver2.py ... --no-push` dry run printed OK: commit 9e763c2c6ac
passed server preflight and compiled both delivered modules. Nothing was pushed by that run.
