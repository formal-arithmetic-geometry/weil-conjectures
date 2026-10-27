## Worker report

The module `Sheaf.Algebra.Homology.DoubleEvaluationSignedDerivedModel` states the
signed double-evaluation chain map and its canonical derived representative. Its
only postponed proofs are
`DerivedCategory.doubleEvaluationSign_identities` and
`DerivedCategory.doubleEvaluation_signed_derived_model`; both state clauses of
this item, and both docstrings give the corresponding full natural-language proof.
All definitions contain actual terms. Nothing is proved in this delivery.

Source read: Stacks `more-algebra.tex`, lemma-evaluate-and-more (0A60), including
both differential equations and its finite-support construction;
remark-sign-explanation (0A61), identifying the sign with the middle-factor swap;
and lemma-internal-hom-evaluate (0A67), choosing K-flat P and K-injective J,I.
The item is an auxiliary node, not its blueprint unit's own statement.
There is no statement correction, disputed statement, or dependency-module repair.

Hypotheses and clauses, matched to the Lean:

- A commutative ring is `(R : Type u) [CommRing R]`, with explicit universe `u`.
  As the node specifies, ordinary modules are presented on the existing
  `CochainComplex.onePointRingSheaf R` with bottom topology on
  `Discrete PUnit.{u + 1}`. `RingSiteModules R` is its existing module category.
  The site has one object and only its identity, and bottom topology imposes no
  further sheaf condition. This presents arbitrary R-modules, without any
  finiteness, topology, action, or descent data added to the mathematical objects.
- The three arbitrary complexes are
  `(P J I : CochainComplex (RingSiteModules R) ℤ)`. K-flatness is exactly the
  recorded predicate
  `(HomologicalComplex.quasiIso (RingSiteModules R) (.up ℤ)).kFlat P`.
  The assumptions on J and I are `[J.IsKInjective] [I.IsKInjective]`.
  `HasDerivedCategory.{u} (RingSiteModules R)` specifies the chosen localization
  and small Hom universe already used by the dependency's canonical-map API;
  it is not a boundedness or finiteness hypothesis on these complexes.
- `homComplex` on this one-object site is the product-total Hom in the node,
  with the recorded projection differential `d_target f - (-1)^n f d_source`.
  `signedDoubleEvaluationSource` is precisely the recorded
  `coefficientTotalTensor` of `homComplex J I` and P; its definition uses
  `CochainComplex.mapBifunctor` with the sheaf tensor bifunctor, giving the
  direct-sum total tensor and sign `(-1)^h` on the P differential.
  `signedDoubleEvaluationTarget` is precisely `homComplex (homComplex P J) I`.
  These are abbreviations of existing constructions, not replacement products
  or tensors. The one-object-site presentation uses the existing ringed
  `homComplex`; the ordinary ModuleCat interface is retained only as a plain
  proof-plan import for `def-sc-module-total-hom-complex`.
- The existential E has type source `⟶` target in the category of complexes,
  hence its differential compatibility is part of its type.
  `SignedDoubleEvaluationFormula` quantifies over all integers h,s,n,k,a,b,
  all sections g,x,f and the actual one-point object U. It applies the actual
  `coefficientTensorGenerator` to g,x and the actual
  `coefficientHomComponent` projections to E, g, and f. The equality is exactly
  `(-1)^(k*s) • g^a (f^s x)`. The index equations are `h+s=n`, `s+k=a`,
  `a+h=b`, `k+n=b`, so the value is in `I^(h+s+k)`, after the explicit degree
  identifications. They cover every h,s,k: take n=h+s, a=s+k, b=a+h.
  These are typing equalities, not restrictions on homogeneous elements.
- The pure generator enters an actual direct-sum total complex and E is linear,
  so the formula extends over every finite-support input. The Hom sections are
  unrestricted product sections; no exchange of infinite products with tensor
  or infinite sum of coordinates is asserted. The pure formula determines E
  since pure tensor summands and Hom-product projections determine maps.
- `doubleEvaluationSign p r s : ℤˣ` is explicitly `(s*(r+1)).negOnePow`.
  The first conjunct of `doubleEvaluationSign_identities` identifies the
  homogeneous sign at k=-r-s with this coefficient. The remaining three
  conjuncts are, in order, the p-independence, the r-1 recurrence with factor
  `s.negOnePow`, and the s+1 recurrence with factor `(r+1).negOnePow`.
  Integer units encode the universal signs and act on every R-module, including
  characteristic two and the zero ring.
- `Q` is the recorded derived localization. The existential isomorphisms a,b,c
  identify QH with RHom(QJ,QI), QA with RHom(QP,QJ), and QB with RHom(QA,QI).
  Their hom maps are each required to equal the EXISTING
  `ringedHomRepresentativeMap`, defined by postcomposition with the fixed
  K-injective augmentation and the inverse fixed localization-factorization
  comparison. They are thus fixed canonical comparisons, not arbitrary
  isomorphisms obtained from `Nonempty` or a stronger assumption.
- The isomorphism t identifies QT with QH tensor QP. Its inverse is fixed as
  the native `Functor.LaxMonoidal.μ Q H P` followed by Q of the inverse
  `SignedRingedHom.totalTensorNativeIso`. This is exactly the native
  one-K-flat tensor comparison, valid with P on the right and H arbitrary.
  The source isomorphism in the node is t followed by `a tensor 1`.
  The target isomorphism is c followed by `RHom(b.inv,1)`.
- The final equation is Q(E) followed by that target comparison, equal to the
  source comparison followed by the verbatim right-tensor adjunction transpose
  formula of `derived_evaluation_canonical_map`. Its composite uses the
  associator, swaps QP with RHom(QP,QJ), and applies the two counits in order.
  It therefore identifies exactly the map e with its specified normalization.
  Only a,b,c,t are isomorphisms; neither E nor Q(E) is asserted invertible.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, the recorded two-sided
  quasi-isomorphism-preserving predicate.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, homotopy-to-zero for every acyclic source.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex` (plain proof import):
  `CochainComplex.moduleHomComplex`, the ordinary-module product Hom used by
  proof dependency `def-sc-module-total-hom-complex`.
- `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, underlying the existing total tensor.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex`, the recorded ringed product-total Hom.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `WeilConjectures.coefficientHomComponent`, the actual product projections
  owned by `def-coef-hom-representative-evaluation`; also the fixed replacement
  `coefficientHomResolution` and factorization `coefficientHomResolutionIso`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, specialized by the existing
  `SignedRingedHom.homFunctor` and `SignedRingedHom.hom`.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` (plain proof import):
  `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` and its right-hand analogue
  `QObjTensorQObjIsoOfKFlatRight`. The normalization in the statement is the
  equivalent native lax tensor comparison; this fixes its map, not just type.
  This import is retained for proof dependency
  `lem-pc-source-kflat-module-tensor-model`, not as a public statement import.
- `Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap`:
  `DerivedCategory.derived_evaluation_canonical_map`,
  `evaluationDerivedCategory`; its transpose expression is copied verbatim.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.coefficientTotalTensor` and `coefficientTensorGenerator`;
  these access the actual sheafification unit and total summand inclusions.
- `Sheaf.Algebra.Homology.RingedHomCompositionModel`:
  `CategoryTheory.ringedHomRepresentativeMap`, with its fixed augmentation.

The additional statement dependencies are `def-pur-hom-complex` for the ringed
Hom, `def-coef-ringed-tensor-hom-model` for the tensor generators,
`def-coef-hom-representative-evaluation` for the product projections, and the new
`def-trf-ringed-hom-representative-comparison` for the fixed augmentation and
comparison maps. The theorem `lem-sfb-ringed-hom-composition-model` is removed
from stmt_deps: neither plain definition is selected from its theorem.
The existing `RingedHomCompositionModel` module remains publicly imported
because it contains these definitions; none of its definitions are copied.

The stated proof-dependency modules are imported, including the ordinary
currying API `TensorProduct.lift.equiv`, quasi-isomorphism invariance, K-flat
resolution, native tensor and complex constraints, and closed derived structure.
`lem-trf-module-one-kflat-uncurry-normalization` and
`lem-trf-closed-evaluation-naturality` have no recorded Lean declaration in the
read DAG, so there is no corresponding import to add. Their mathematical use
is explained explicitly in proof steps 7 and 8 of the theorem docstring.

Edge checks performed before finalizing:

- Zero complexes and the zero ring: evaluations vanish, all displayed
  comparisons remain canonical, and no nonzero or faithful assumption appears.
- Degree-zero complexes: all signs are 1 and the formula is ordinary
  double evaluation `g(f(x))`.
- Odd x and odd f: the sign is -1. If either degree is even it is +1.
  The conversion k=-r-s gives exactly s(r+1) modulo two, including negative
  integers. The three recurrences were checked by their exponent differences.
- Characteristic two: the unit signs act identically, so no division by two
  or characteristic exclusion occurs.
- Unbounded inputs and infinite-rank terms: only the total tensor has finite
  support; the individual Hom-product coordinates are projected, never summed.
  No K-injectivity of A=Hom(P,J) is requested: it is a Hom SOURCE.
- No inference that E or Q(E) is invertible is present. No perfectness,
  boundedness, termwise-flatness or finite-generation assumption was added.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: “The Koszul signed double evaluation map Hom(J,I)
  tensor P to Hom(Hom(P,J),I) represents the canonical derived evaluation”.
  Eight results, including `ModuleCat.ihom_ev_app`, ordinary FG-module
  evaluations and currying; none supplies the chain-level plus normalized
  derived-model statement.
- `msearch.py`, Loogle: `"HomComplex", "eval"`. Three unrelated number-field
  HomComplex-name matches; no statement match.
- `msearch.py`, grep: `evaluation|evaluate|tensorHom` in Mathlib
  `Algebra/Homology`. Twenty-two infrastructure hits (tensor morphisms,
  homology evaluation, graded totalization), no double-evaluation model.
- `msearch.py`, LeanSearch: “Double evaluation chain map Hom(J,I) tensor P
  to Hom(Hom(P,J),I) with Koszul signs”. Eight infrastructure matches,
  including `HomologicalComplex.tensorHom` and graded commutativity, none exact.
- `rg` over both project source roots for double evaluation, signed evaluation,
  and this blueprint id. Existing finite-injective and pseudo-coherent
  derived-evaluation theorems concern invertibility with stronger hypotheses;
  the canonical-map module supplies the derived transpose but does not state
  the homogeneous formula, sign recurrences, or its fixed comparison equation.
  No exact existing declaration was found. The supplied CompactObject example
  is now a withdrawn empty module; the current canonical-map module supplied
  the active public-module/header conventions instead.

Validation: the complete module is compiled through `scompile.py`, with explicit
universes (including the coefficient/site universe parameters at construction
calls), `autoImplicit false`, and no diagnostic commands or file-local notation.
The first compile exposed universe inference defaulting to zero; explicit
universe applications repaired this without constraining u. The comparison
bifunctor map needed explicit source and target pairs; these now make its
contravariant direction `b.inv.op` visible. Line-length warnings were repaired.
The dry-run and final delivery results are recorded by the delivery wrapper.

## New nodes

`def-trf-ringed-hom-representative-comparison` owns the already published
`CategoryTheory.ringedHomAugmentation` and
`CategoryTheory.ringedHomRepresentativeMap` in
`Sheaf.Algebra.Homology.RingedHomCompositionModel`, with `existing: true`.
The first is exactly the fixed `toKInjectiveResolution` component; the second
is `Q.map` of postcomposition with this component, followed by the inverse of
`coefficientHomResolutionIso`. Source: Stacks sites-cohomology.tex, the Tag 0A95
construction, and injectives.tex Tag 079P; these are the comparisons used in
more-algebra.tex Tag 0A67. The node preserves the full independent object,
arrow, coefficient and derived-Hom universes and the two sheafification
hypotheses of the published signature. Its objects are arbitrary complexes;
it does not assert a comparison is invertible without a K-injective target.
No module, definition, data or existing docstring is changed.

The new LeanSearch query “Canonical comparison from a Hom complex to derived
internal Hom by functorial K injective augmentation and localization
factorization” found eight generic localization and K-injective declarations,
including `Functor.mapDerivedCategoryFactorsh_hom_app`, `DerivedCategory.Q`
and `CochainComplex.IsKInjective.Qh_map_bijective`. LeanFinder on the same
query returned eight generic localization/right-derived declarations, including
`Functor.toRightDerivedZero`, `DerivedCategory.right_fac` and `left_fac`.
The Mathlib Algebra/Homology grep
`ringedHomRepresentativeMap|ringedHomAugmentation|toKInjectiveResolution`
had zero hits. The source-root rg found the exact existing definitions only in
`RingedHomCompositionModel`, and DAG rg found only the two theorem records
`lem-sfb-ringed-hom-composition-model` and
`lem-sfb-ringed-ordinary-evaluation-localization`.
`blueprint_refs.py search 'Hom representative'` returned zero blueprint nodes.
The existing definition node `def-coef-hom-representative-evaluation` owns
the replacement and factorization but not these two composite definitions.
Thus this delivery supplies their missing definition ownership, as the
review explicitly requested, without defining a second notion. The search
responses are copied into the new node's `mathlib_searches`.

## Second reading by Q63

Repair self-check performed by this worker, with the saved node, the Lean
module, the new definition node and the two published defining modules open;
no separate agent was started, as the dispatcher forbids it. The maintainer's
independent review is the returned-head review quoted in the brief.

Returned head `2bf8faae97c8` was checked through the retained packet and the
review's exact named defects. Before repair the saved packet passed
`deliver2.py --no-push` as commit `ec592a3fbef`; that mechanical success did not
resolve the missing ownership records. Against the current read-clone item,
only `lean` and `stmt_deps` differ, and every mathematical statement and proof
field remains unchanged. The live defining module was also read with
`scompile.py --source Sheaf.Algebra.Homology.RingedHomCompositionModel`.

H2, representative comparison: the new definition node owns the exact existing
`ringedHomAugmentation` and `ringedHomRepresentativeMap`. Its signature is
verbatim from `def` through the return type. The three equalities fixing a,
b,c use this definition, and the composition theorem dependency was removed.
H2, projections: `SignedDoubleEvaluationFormula` has three uses of
`coefficientHomComponent`; each is owned by the newly cited
`def-coef-hom-representative-evaluation`, not by the HomComplex module. The
report attribution and the explicit public import now agree with that owner.
H9: the two unused public imports `ModuleHomComplex` and `FlatModel` became
plain proof imports, retained because the unchanged proof_deps list contains
`def-sc-module-total-hom-complex` and
`lem-pc-source-kflat-module-tensor-model`, respectively. Public imports expose
only the statement's construction interfaces.

Clause check after repair: the explicit CommRing R and arbitrary P,J,I
binders, kFlat P, IsKInjective J,I and chosen derived category are unchanged.
The source and target remain the direct-sum tensor and double product Hom.
The generator formula still uses indices h+s=n, s+k=a, a+h=b, k+n=b and the
sign `(k*s).negOnePow`; its three projections land in the asserted degrees.
The integer sign and all four identities are unchanged. The a,b,c comparisons
remain pinned to the fixed Hom map, and t.inv remains pinned to the native
localization tensorator followed by the inverse total-tensor identification.
The final equation still uses `(b.inv.op, 1)` and precisely the canonical e
transpose, with no invertibility conclusion. Both theorem proofs remain
`sorry`; all definitions still have their original data. Zero complexes,
characteristic two, degree zero, negative indices and unbounded complexes
remain admitted. The new definition's zero and non-K-injective target cases
are also well typed: it defines a morphism without claiming it is an iso.
No mathematical statement correction or disputed statement is needed.
