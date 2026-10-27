## Worker report

The module `Sheaf.Paper.FiniteDerivedComparisonNormalization` states the simultaneous
normalization as five named theorems, all with `sorry`. Its definitions contain real data.
The primary declaration is
`CategoryTheory.FiniteDerivedComparison.finiteDerivedComparisonNormalization`.
The other four statements are `tensorComparison_coherence`,
`tensorComparison_composition`, `tensorComparison_coefficients`, and
`coefficientComparison_identity_successive` in the same namespace. All carry the item's
blueprint tag and a natural-language proof identifying the DAG tools to use in stage 3.

Hypotheses and objects:

- Small sites and commutative coefficient sheaves are the published
  `CategoryTheory.RingedDerivedComparisons.Site.{u,w}`. Its fields are the site, topology,
  `A : Sheaf J CommRingCat.{u}`, derived-category size witness, and the existing derived
  tensor with its signed-total representative model and coherence. The tensor is not
  replaced by a new construction. Its module category is Mathlib's `SheafOfModules`,
  through `ringedSiteModules` and `CochainPullback.Modules`.
- The ringed geometric morphism and its ordinary pullback are the published
  `CochainPullback.RingedPullback`. The inverse/direct-image adjunction and finite-limit
  preservation concern sheaves of sets; `AlgebraicInverseImage`, `coefficient`, `hobj`,
  and `hmap` identify the module functor with actual scalar extension. Thus this is a
  presentation of a ringed geometric morphism, with no functor between sites required.
  `Comparison f` is the ordinary comparison normalized on generalized pure tensors,
  not an arbitrary tensorator hypothesis.
- `Pullback f` packages only the given derived functor `F`, its cochain counit `epsilon`,
  and `F.IsLeftDerivedFunctor epsilon` at quasi-isomorphisms. In particular none of the
  monoidal equations being asserted is an input. All complexes have index type `ℤ`.
- `Resolving X P` abbreviates the already published
  `RingedKFlatWord.Resolving (wordSite X) P`; its two conditions are the recorded
  `CochainComplex.IsKFlatIndependentCoefficients` and termwise `IsFlatOnSite`.
  `wordSite` changes only the packaging of the same site, coefficient sheaf, and
  derived-category instance.

Conclusions, clause by clause:

- The first conjunct of `finiteDerivedComparisonNormalization` states that `P ⊗ Q`
  and its termwise pullback are resolving. This tensor is the existing signed direct-sum
  total tensor of cochain complexes. The existential preservation witnesses in
  `Normalized` also state that the individual pullbacks of P and Q are resolving.
- Its second conjunct is `∃! nu : Y.closed.tensor ⋙ d.F ≅
  (d.F.prod d.F) ⋙ X.closed.tensor, Normalized f k d nu`. The natural isomorphism is
  bifunctorial on the entire unbounded derived category, including arbitrary localized
  morphisms. `Normalized` states the representative square using the actual `epsilon`
  and the site's `model.iso`. Its right route is `epsilon.app (P ⊗ Q)`, followed by
  `DerivedCategory.Q.map (CochainPullback.comparison f k P Q).hom`, then the target
  representative isomorphism. The published `comparison` is the inverse of
  `k.totalIso`: its formula inserts 1 in the second factor and its inverse multiplies
  the two scalars. Hence both balanced chain formulas in the node are retained.
  Uniqueness specifies independence of resolutions and identification with the
  representative-normalized comparison of the recorded tensor-pullback dependency.
- `tensorComparison` chooses exactly that unique normalized isomorphism; it does not
  choose from bare unspecified existence. `unitMap` is the actual localized ordinary
  unit comparison conjugated by the two recorded site unit isomorphisms.
- `tensorComparison_coherence` asserts invertibility of `unitMap`, the associator
  equation, the left action-unit equation, the right action-unit equation, and the
  symmetry equation. The braiding is the site's recorded `symmetry`, whose
  `coherence.symmetry_model` uses the signed total-complex braiding, with sign
  `(-1)^(p*q)` on bidegree `(p,q)`.
- `tensorComparison_composition` quantifies over three ringed pullbacks and their
  published `CompositePresentation`, which fixes the ordinary compositor by scalar
  association and adjunction. It gives a unique `c : dh.F ≅ df.F ⋙ dg.F`, characterized
  on every resolving P by its counit square and `CochainPullback.composition`.
  The second conjunct is exactly the node's equation: tensor comparison for h,
  followed by tensor of c_M,c_N, equals c at the source tensor followed by
  dg.F applied to the comparison for f and the comparison for g.
- `tensorComparison_coefficients` uses the published `CoefficientSquare f`:
  `sourceMap : R ⟶ R'`, `targetMap : S ⟶ S'`, and `coefficient' : RI' ⟶ S'`, with
  `inverseImageMap_graph` and `square` expressing compatibility. `changed f a` is u'.
  `extensionPullback a.sourceMap` and `extensionPullback a.targetMap` are the actual
  identity-topos scalar extensions. Their derived functors are dR.F and dS.F.
- That theorem supplies nu, nu', epsR, epsS and `b : dR.F ⋙ df'.F ≅ df.F ⋙ dS.F`.
  All four tensor arrows satisfy the published `PullbackTensorCanonical.IsNormalized`
  predicate, in its published `canonicalDerivedTensor` presentation. The counit equation
  for b fixes it by `CochainPullback.kappa f k a k' P`, the ordinary balanced
  scalar-association map, for every resolving P. The final conjunct proves uniqueness
  from this normalization. Thus b is the specified kappa, rather than a free isomorphism.
- The remaining conjunct, universally quantified over M,N in D(R), is the requested
  coefficient square in Lean's left-to-right composition notation: F'(epsR), then nu',
  then tensor of b_M,b_N, equals b at the source tensor, then E_S(nu), then epsS.
  The four arrows use the fixed published tensor at their four corners. No flatness of
  either ring map is a binder.
- `coefficientComparison_identity_successive` uses existing finite words with their
  parenthesizations, ordinary functors, actual composite universal counits and normalized
  descent `Word.cell`. It states preservation of the identity ordinary comparison and
  of a composite of ordinary comparisons. The coefficient kappa and its successive
  scalar-association maps are precisely these cells by their representative equations
  and uniqueness. Specializing to coefficient squares proves the identity and successive
  clauses; their tensor squares paste by the preceding universally quantified equation.
  `[Finite I]` concerns the finite diagram of these comparisons, not the degrees of the
  complexes or the coefficients. Empty diagrams are permitted.

Dependency declarations used (source signatures and docstrings inspected):

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  signed total tensor inherited by the cochain monoidal structure.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  This is the generic unique representative-normalized comparison; the new statement
  additionally records simultaneous monoidal, compositor and coefficient equations.
- `Sheaf.SixFunctors.RingedDerivedComparisonData`:
  `CategoryTheory.RingedDerivedComparisons.Site` and its existing tensor model/coherence.
- `Sheaf.SecSmoothPurity.CochainTensorCoherenceData`:
  `RingedPullback`, `Comparison`, `comparison`, `unit`, `CompositePresentation`,
  and `composition` in `CategoryTheory.CochainPullback`.
- `Sheaf.SecSmoothPurity.CochainCoefficientArrows`: `CoefficientSquare`, `changed`,
  `extensionPullback`, `extensionComparison`, `extend`, and `kappa` in that namespace.
- `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`:
  `SheafOfModules.PullbackTensorCanonical.Phi`, `Psi`, `IsNormalized`,
  `canonicalDerivedTensor`, and `canonicalRepresentativeIso`, owned by
  `def-pur-derived-tensor-pullback-normalization`. The theorem
  `pullback_tensor_canonical_shift_unit` is retained only as a proof dependency.
- `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`:
  `CategoryTheory.RingedKFlatWord.Site`, `Resolving`, `Word`, and `Word.cell`.
  The published `word_comparison_descent` supplies normalized identity and pasting laws.

The statement dependencies include the published site, cochain, normalization-definition,
and finite-word interfaces used explicitly in signatures. The plain normalization
definitions are cited through `def-pur-derived-tensor-pullback-normalization`; the
canonical-shift-unit theorem is used only by the proof plan. The finite-word descent
theorem remains a statement dependency because `Word.cell` chooses from its uniquely
normalized descent theorem. All seven original proof-dependency modules are imported, including KFlatTotalTensorModel,
KFlatRingedToposPullback, CochainPullbackTensorCoherence,
RingedDerivedMonoidalComparisons, and SiteDerivedTensorDescentIndependentCoefficients.
No dependency module or new definition node is needed.

Edge cases checked against the statements and balanced maps: empty sites and zero
coefficient sheaves are not excluded; zero complexes and the ring in degree zero use
ordinary unit maps; the index ℤ and direct-sum total tensor impose no upper/lower
boundedness. Identity coefficient maps specialize scalar association to multiplication.
Successive changes retain their actual word counits. Quotients such as ℤ → ℤ/2 and
ℤ/4 → ℤ/2 are allowed because no flat-map condition is present. Arbitrary geometric
morphisms, rather than only site-induced ones, are permitted by RingedPullback.
The site and module universes match the recorded small-site convention, while the
localization morphism universe w is explicit and independent. No nonzero-ring condition
or characteristic condition was introduced.

Searches from the persisted searches.jsonl and source searches:

- LeanFinder: "Unbounded derived pullback tensor comparison normalized on K flat
  complexes compatible with scalar change" returned ordinary pullback composition,
  Tor, and ordinary module flatness results, not this simultaneous derived statement.
- Loogle: "CategoryTheory.Functor.Monoidal, SheafOfModules" returned no match;
  '"LeftDerived", "tensor"' also returned no match.
- Mathlib grep: `derived.*[Tt]ensor.*[Pp]ullback|[Pp]ullback.*[Tt]ensor.*[Cc]omparison`
  returned no match through msearch.py.
- LeanSearch: "Derived pullback tensor comparison coherent with change of coefficients
  on K flat representatives" returned ordinary pullback, scalar extension, flatness and
  algebraic tensor comparison hits; none states the unbounded normalized square.
- LeanFinder: "Canonical K-flat derived pullback tensor comparison compatible with
  extension of scalars and composition" returned ordinary pullback composition and Tor
  hits. The existing generic project comparison was read and reused via its module.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, namespace and main theorem
  found no existing statement. The similarly named private adicFiniteDerivedComparison
  in AdicConstructibleFiniteReductions concerns adic comparison, not this assertion.
  The relevant ordinary comparisons, site tensor model and finite-word descent were
  found in the project and are reused, not redefined.

Source read: literature/stacks-project/sites-cohomology.tex, lemma-pullback-K-flat
(Tag 0G7E) and lemma-pullback-tensor-product (Tag 07A4), including its proof by the
ordinary total-complex comparison. The coefficient calculations follow the accepted
node proof and the published cochain coefficient square. No statement correction or
STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the original draft cleanly in sandbox and library
module modes. The final file and delivery are rechecked by deliver2.py; only expected
sorry warnings are permitted. No global build or direct Git command was run.

## Returned-delivery repair

Repair of immutable head `f22979a487f9`, C1/H2: replaced
`lem-weil-pbc-pullback-tensor-canonical-shift-unit` in `stmt_deps` with the already
landed definition owner `def-pur-derived-tensor-pullback-normalization`. Its
`existing: true` record owns exactly the existing `Phi`, `Psi`, `IsNormalized`,
`canonicalDerivedTensor` and `canonicalRepresentativeIso` definitions in
`Sheaf.Paper.PullbackTensorCanonicalShiftUnit`. Their definitions and docstrings
were reread: they construct the actual composites and representative-square
predicate, without choosing from the canonical-shift-unit theorem. That theorem
remains in `proof_deps`, unchanged. The legitimate statement dependency
`lem-trf-ringed-kflat-word-comparison-descent` is retained: `Word.cell` is
`Classical.choose (descent_existsUnique S E A t)`.

Compared the saved packet with the current main node: only `lean` and the permitted
statement-dependency additions differ. The accepted mathematical statement, proof,
proof dependencies and all eleven Lean declarations are retained. The Lean source
is byte-for-byte unchanged from the saved returned packet, as requested by the
review. This is a worker re-delivery because changing `stmt_deps` cannot be a
reviewer's stage-2 FIX. No new definition or dependency module is needed.

The review's A1-A3 are recorded as advisories: the final theorem gives generic
finite-word identity/pasting laws to specialize to coefficient comparisons; the
coefficient clause uses the fixed published tensor presentation, whereas the
preceding clauses use the site's representative-normalized presentation; and the
public canonical-tensor-pullback import is retained with the accepted source.
The requested repair leaves Lean unchanged.

Repair validation (2026-10-23 UTC): `scompile.py Q64
lem-pur-finite-derived-comparison-normalization` compiled the unchanged module
cleanly in sandbox mode (25.9 s) and library mode (22.6 s). The primary signature
is verbatim in `lean.statement`; all eleven recorded declarations are present;
the current main comparison changes only `lean` and `stmt_deps`. Lean SHA256:
`a20c58d6d865ce25ebaa6beb23250edc9d228355e2602244701a177c6a3d3c4a`.

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
