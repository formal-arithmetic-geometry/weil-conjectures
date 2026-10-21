## Worker report

Item: lem-pur-derived-tensor-additive-constraints. Module:
`Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`.
Namespace: `SheafOfModules.DerivedTensorConstraints`.
Four theorem statements, all proved only by `sorry`, jointly state the node.
There is no correction, disputed statement, new DAG node or dependency replacement.
All auxiliary definitions contain real data or existing named proofs of membership.

### Hypotheses and objects

- A ringed site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`
  and `R : Sheaf J CommRingCat.{r}`. Commutativity is in `CommRingCat`.
- Smallness relative to the ordinary module-sheaf universe is exactly
  `[EssentiallySmall.{r} C]`. Site object and morphism universes remain independent.
  Sheafification and the locally-bijective criterion are inherited from the published
  coefficient-universe instances; neither is an additional hypothesis.
- `Modules R` is `KFlatFixedTensor.Modules R`, transparently the recorded
  `CategoryTheory.ringedSiteModules` of the underlying ring sheaf, with ordinary modules
  in universe r. No second module category or abelian structure is constructed.
- `Complex R = CochainComplex (Modules R) ℤ`: arbitrary integer-indexed cochain complexes.
  The standard shifts have E[a]^p = E^(p+a) and differential (-1)^a d.
- `[HasDerivedCategory.{w} (Modules R)]` chooses the morphism-size universe as in the
  recorded abstract derived-category definition. It imposes no equality on u, v, r, w.
  `D R` abbreviates precisely this `DerivedCategory`.
- Ordinary total tensor is the existing `⊗` of cochain complexes. Its objects are direct
  sums along p+q=n, with second differential sign (-1)^p, not direct-product totals.
- `resolvingComplex` is the conjunction of the recorded
  `IsKFlatIndependentCoefficients` and `∀ n, IsFlatOnSite (E.X n)`.
  `Model R` is its full subcategory of chain representatives;
  `resolvingHomotopy R` is the same property on the actual homotopy category via `.as`.
  The latter is the full homotopy subcategory P in the node.
- `localization R` is `(resolvingHomotopy R).ι ⋙ DerivedCategory.Qh`, exactly q restricted
  to P. `tensor R` abbreviates the published `siteDerivedTensorIndependentCoefficients`.
  `representative` is exactly `KFlatFixedTensor.representativeIso` on the bundled
  models. It has orientation qT(E,F) ≅ tensor(qE,qF); no arbitrary comparison is chosen.

### Every assertion and normalization

1. `derived_tensor_model_closure` states closure under tensor, every integer shift,
   and finite sums (families `Fin n`, for every natural n). This is all finite sums,
   including n=0; arbitrary finite index types may be reindexed by their cardinality.
   Its next clause says every flat P gives a resolving degree-zero complex.
   Its last clause says P⊗Q is flat whenever P and Q are flat, and provides a chain
   isomorphism c from the total of P[0], Q[0] to (P⊗Q)[0]. The summand inclusion in
   degree (0,0), composed with c and `singleObjXSelf`, equals the tensor of the two
   `singleObjXSelf` maps. Thus c is the ordinary, unsigned identification, not an
   unspecified isomorphism. The derived isomorphism d is explicitly required to equal
   `representative.symm ≪≫ DerivedCategory.Q.mapIso c`. This is the comparison induced
   by r in the node. The proof binders hP, hQ only provide membership to `representative`;
   the preceding clause establishes that membership for every flat P, Q.
2. `totalModel` and `shiftModel` have the actual total and shifted complex as their
   object fields. Their membership proofs refer to the recorded total-model and
   fixed-tensor theorems. They introduce no existential object choices.
3. `chainShift E F a b` composes `mapBifunctorShift₂Iso (E⟦a⟧) F ... b`, the b-shift of
   `mapBifunctorShift₁Iso E F ... a`, and the inverse standard `shiftFunctorAdd`.
   The first map has sign (-1)^(bp) on shifted first degree p; the second is unsigned.
   The resulting direction is T(E[a],F[b]) → T(E,F)[a+b], exactly as specified.
4. `shiftedSource`, `shiftedTarget`, `leftAssociated`, `rightAssociated` and `swapped`
   are compositions/products of the existing tensor, shifts and Cartesian product
   functors. In particular α has a common domain `(D×D)×D`, with the Cartesian
   associator explicitly reindexing its right-associated target.
5. `shiftRepresentative` spells out all five factors in the node's shift formula:
   tensor of inverse Q shift comparisons, inverse r for shifted models,
   Q(chainShift), the Q shift comparison for the total, and the shifted r.
6. `leftRepresentative` is r_(T(E,F),G) followed by tensor(r_(E,F),id).
   `rightRepresentative` is r_(E,T(F,G)) followed by tensor(id,r_(F,G)).
   The associativity clause of `IsNormalized` is leftRepresentative inverse,
   Q(unsigned chain associator), rightRepresentative, in that order.
7. The symmetry clause of `IsNormalized` is inverse r_(E,F), then Q of the existing
   `CochainComplex.Monoidal.braiding E.obj F.obj`, then r_(F,E). Its upstream
   `ι_braiding_hom` formula is exactly (-1)^(pq) times ordinary sheaf symmetry.
8. `existsUnique_derived_tensor_constraints` is `∃!` on a tuple consisting of the
   entire integer-indexed family of natural shift isomorphisms, the ternary natural
   associator, and the binary natural symmetry. Its property is `IsNormalized`.
   Therefore uniqueness concerns natural isomorphisms having those representative
   squares, not independent objectwise isomorphisms. The square formulas are imposed
   on every flat-term K-flat chain representative; these represent exactly the
   resolving homotopy objects used in the restriction theorem.
9. `derived_tensor_restriction_fully_faithful` quantifies over every `I : Type i`
   with `[Finite I]`, and every `E : Type e` with `[Category.{z} E]`. Its first clause
   is `Nonempty ... FullyFaithful` for precomposition along
   `Functor.pi (fun _ : I ↦ localization R)`. Its second clause gives the equality
   test verbatim: η=θ iff their components agree on every resolving tuple. It applies
   to arbitrary functors, hence in particular to all tensor/shift composites,
   ternary associativity, and binary signed symmetry, with the preceding
   representative comparisons substituted. Fullness also asserts extension of
   every natural transformation on the restriction, not just equality detection.
10. `derived_tensor_additive` quantifies over every derived H, and supplies proofs of
    Additive for both fixed-variable functors of the already published curried tensor.
    Its next clause sends each actual `BinaryBicone X Y` with `IsBilimit` to an
    `IsBilimit` under `mapBinaryBicone` in both orders. The mapped bicone retains the
    actual images of all four arrows. The existential Additive proofs bind the
    zero-map-preservation instances needed to form these mapped bicones; they are
    conclusions, not hypotheses. The last two clauses explicitly give map(f+g) =
    map(f)+map(g) in both orders for arbitrary parallel derived maps.
    There is no boundedness, K-flatness, flatness or cohomological restriction on
    H, X, Y or f, g.

### Recorded dependency declarations used

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh` and their shifts.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso` and their summand formulas.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients` (via the public fixed-tensor import).
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`:
  `SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`, `Modules`,
  `ordinaryTensor`, `derivedTensor`, and the actual `representativeIso`.
- Proof import `Sheaf.Algebra.Homology.KFlatTelescopeClosure`:
  `CochainComplex.kFlat_closure`. Its old equal-universe presentation is not imposed
  on the consumer: the present theorem states finite closure in the required
  independent universes; the proof plan uses the same site-transport argument as
  the published coefficient-universe modules. No new assumption is added.
- Proof imports `Mathlib.CategoryTheory.Localization.Predicate`,
  `Mathlib.CategoryTheory.Localization.Pi` and
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Localization.lift`,
  `Localization.fullyFaithfulWhiskeringLeft`, `Functor.IsLocalization.pi`, and
  `Pretriangulated` (the recorded Mathlib matches, which need no lean attachment).
- The proof dependency `lem-pur-total-tensor-signed-coherence` has no recorded Lean
  module at inspection, so there is no module to import yet. The statement uses the
  actual existing chain maps directly: Mathlib's unsigned associator and two shift
  comparisons, plus the upstream Koszul braiding from
  `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` (publicly imported by the
  cochain-universes dependency). No dependency notion is replaced or assumed.

### Edge cases and source checks

Read Stacks sites-cohomology.tex at lemma-symmetric-monoidal-derived (0FPT),
lemma-symmetric-monoidal-cat-complexes, and more-algebra.tex item-shift-tensor and
item-flip-tensor-product. These identify unsigned reassociation and Koszul symmetry.
The node further fixes its explicit right-then-left shift-extraction convention.
Checked negative a,b,p,q: the Mathlib integer shift maps use `Int.negOnePow` and
require no positivity. At a=b=0 the extraction is the standard zero-shift identity.
Checked the sign order: extracting left first would introduce a different global
(-1)^(ab), so the implemented order is essential. Symmetry has the sign of the
unshifted degrees p,q, whereas shift extraction uses the shifted first-factor p.
The zero complex, zero flat module, zero coefficient ring, empty site and empty
index family are not excluded. Fin 0 gives the empty direct sum; I may be empty in
full faithfulness. All complexes may be unbounded in both directions. All five
size choices (site objects/maps, coefficients, derived morphisms, target category)
are independent; i also independently sizes the finite index type.

### Searches for existing declarations

All wrapper searches used group Q104 and this item.

- msearch leansearch: `Derived tensor product of sheaves is additive separately and
  has unique signed shift associativity symmetry constraints on K flat resolutions`.
  Eight hits: generic tensorLeft/tensorRight additivity, additive derived shifts,
  ordinary tensor and sheaf additivity; no normalized derived constraint statement.
- msearch leanfinder: `Derived tensor of module sheaves is separately additive with
  unique signed shift associativity and symmetry constraints normalized on K-flat
  representatives`. Eight hits: generic good tensor/trifunctor hypotheses and Tor.
  No match for the fixed tensor and all representative normalizations.
- msearch loogle: `"fullyFaithfulWhiskeringLeft", "Additive"`: zero hits.
- msearch grep: `mapBifunctorShift|fullyFaithfulWhiskeringLeft|tensor.*[Aa]dditive`:
  25 hits including Mathlib's actual chain shifts, generic localization full
  faithfulness, and generic monoidal additivity. Reused these interfaces.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for this item id: no declaration.
  Additional name/concept searches for derived additive tensor, normalized
  constraints, signed shifts and the proposed namespace found no duplicate.
  `RingedDerivedClosedSymmetricMonoidal` concerns another closed tensor structure
  and its own comparisons; it does not state the normalized unique constraints,
  arbitrary finite-variable restriction and additivity for this fixed tensor.
  `KFlatFixedTensorTriangulated` gives the fixed tensor and its exactness and
  comparison, which are reused, but does not contain the present full statement.
- Read the recorded declarations and Mathlib signatures/docstrings for every
  statement dependency, including Mathlib leaves, before writing the module.

Validation: scompile.py compiled both the sandbox and final library module cleanly
under the default 60-second per-file limit. Delivery preflight and its final compile
are recorded by deliver2.py. All four theorem bodies remain exactly `sorry`.

## Second reading by Q104

A second source-to-statement pass was performed in this worker session. The dispatcher
brief prohibits starting another agent; the maintainer supplies independent review.
The pass checked the node and final module together, clause by clause as numbered
above. In particular it checked the actual representativeIso rather than an arbitrary
isomorphism, both nested comparison orientations, shift-extraction order, natural
rather than objectwise uniqueness, the empty-product case, binary bicone arrow images,
and both sum identities on arbitrary derived maps. The binder repair for mapped
bicones puts Additive proofs in the conclusion, so it does not assume additivity.
The finite-sum and normalized degree-zero clauses were included explicitly; none is
left as an informal consequence of an unrelated theorem. No mathematical mismatch
or source-based statement correction was found. Every helper is a specialization or
composition of existing notions, so no independent definition node was introduced.
