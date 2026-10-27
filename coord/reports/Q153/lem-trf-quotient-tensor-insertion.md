## Worker report

Group Q153, stage 2, lem-trf-quotient-tensor-insertion, 2026-10-22.
Module: `Sheaf.Paper.QuotientTensorInsertion`; namespace:
`WeilConjectures.QuotientTensor`; main theorem: `quotient_tensor_insertion`.
This delivery changes only the item's `lean` record and adds its module and report.
No statement correction, new node, dependency repair, or disputed statement is needed.
The three postponed theorems are `insertion_existsUnique`,
`transition_existsUnique`, and `quotient_tensor_insertion`. Their proof bodies are
exactly `by sorry`; each has a source and complete proof plan in its docstring.
They state the construction/linearity and compatibility clauses of this one node.
Every definition has actual data. The two choices are from uniqueness statements
fixing the map by its section formula, not from uncharacterized existence.

The prior worker's supersession diagnosis was mistaken: the live Q24 review and
ledger entry at 07:48 UTC are a stage-1 split, not a Lean statement delivery.
The live node has `reviewed` but no `lean` or `reviewed_lean` record. No repair note
exists for this item. This packet preserves Q24's statement and six-step proof
verbatim and formalizes them for stage 2, as dispatched.

Hypotheses and objects, individually:

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The recorded `Padic` constructions supply the
  extending absolute value, valuation ring, chosen uniformizer, ideals and
  quotient rings; none is redefined.
* Positive exponents: the library's `n : ℕ` means the paper's exponent `n+1`.
  Thus the first term is A_1, not A_0, and all positive levels are covered.
* Isomorphism of schemes: `{X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]`.
  There is no finite-field, finite-type or nonemptiness restriction on X or Y.
* Ell invertible on both schemes: `_hX` and `_hY`, each `∀ x, IsUnit
  (l : _.presheaf.stalk x)`. These retain the node's assumptions even though
  the purely algebraic construction does not need them.
* Small pro-etale sites: the existing `X.ProEt`, `Y.ProEt`, and `ProEt.topology`.
  Site object size is t+1, Hom size t. Coefficients and module sections have size
  `max u (t+1)`. The two universes are independent.
* S_W,n, quotient reductions and R_W: the imported
  `integralCoefficientSheaf`, `integralCoefficientSheafTransition`,
  `integralCoefficientSheafSystem`, and
  `completedIntegralCoefficientSheafUnrestricted`. R is the limit ring sheaf,
  not the discrete constant valuation ring.
* G and coefficient structure maps: imported `isoSectionwiseInverseImage`,
  `inverseImageFiniteCoefficientMap`, `inverseImageCompletedCoefficientMap`,
  and `inverseImageIntegralModules`. The last transports the action through
  c_R inverse. The completed map is the limit lift of its finite components,
  giving exactly the required projection square.
* Unbounded complexes: every occurrence is `CochainComplex _ ℤ`. No condition
  on support, flatness, constructibility, cartesianness or K-flatness is present.
* Strict system: `M : ∀ n, CochainComplex (integralOperationsFiniteModules l E Y n) ℤ`
  and `w n`, a chain map between the two complexes after completed scalar
  restriction. `hw n : IsReductionLinear ...` explicitly imposes rho_Y,n
  semilinearity on every section in every degree. A rho-linear map gives this
  completed-linear map because rho pi_(n+1)=pi_n; conversely the predicate
  retains the full semilinearity condition. Thus `w` is not an arbitrary map
  of completed modules. The family-and-successor-maps presentation is exactly
  `def-weil-inverse-system`/`Functor.ofOpSequence`, without imposing extra data.

Constructions and clauses, individually:

* C_n is `(target l E g n).obj (M n)`. The definition uses the existing
  `integralOperationsLevelPullback` termwise and then
  `integralOperationsRestrict`. This is the recorded finite tensor pullback
  from def-weil-inverse-image-pullback-comparison (a), with its actual
  unit-normalized section generators; it is not a separately chosen complex.
* The R_X-module source of insertion is `(source l E g n).obj (M n)`:
  restrict M_n by pi_Y,n, apply G and transport by c_R inverse. This gives the
  node's action through G(pi_Y,n)c_R inverse. No equality of differently
  encoded module structures is silently assumed.
* The actual x tensor b is `tensorSection ... b x`. This multiplies the
  published `integralOperationsPullbackGenerator` by b after restricting along
  `proEtaleIsoCommaArrow`. The generator is the sheafified tensor unit in the
  canonical inverse-image model, exactly as specified in the dependency's
  `inverseImageFiniteComparison_existsUnique`. It does not assume that tensor
  products commute with sections.
* j_n is `insertion ...`. Its uniquely defining theorem has the formula
  `(j.f i).val.app (op U) x = tensorSection ... 1 x` for every i, U and x.
  Its morphism type asserts both R_X-linearity and the chain property.
* v_n is `transition ... (w n) (hw n)`. Its uniquely defining theorem asserts,
  on every tensor x tensor b, precisely G(w_n)(x) tensor rho_X,n(b).
  It quantifies over arbitrary b, not just insertion sections. Its morphism
  type asserts completed linearity, sheaf restrictions and the chain property.
  Balancing and compatibility with restrictions are the construction proof
  in its docstring, using the original six-step split, not extra assumptions.
* The first conjunct of `quotient_tensor_insertion` is
  `insertion_(n+1) ≫ transition_n = G.map (w n) ≫ insertion_n`.
  Lean's composition order is left-to-right; this is v_n j_(n+1)=j_n G(w_n).
* For any second system N,w',hw' and every `f : ∀ n, M n ⟶ N n`, the
  second conjunct assumes exactly the system-map equation
  `Res.map f_(n+1) ≫ w'_n = w_n ≫ Res.map f_n`.
  Its first conclusion says `target.map f_(n+1) ≫ v'_n = v_n ≫ target.map f_n`.
  Here `target.map` is the canonical G(f_n) tensor 1 in the published tensor
  pullback, restricted by pi_X,n. The second conclusion is naturality of j:
  `source.map f_n ≫ j'_n = j_n ≫ target.map f_n`.
* The final conjunct quantifies over every completed-coefficient complex P and
  all R_Y-linear chain maps `r n : P ⟶ Res (M n)`, with exactly the condition
  `r (n+1) ≫ w n = r n`. The actual `augmentation` definition is G(r_n)
  followed by j_n, with the node's transported source action. Its morphism
  type asserts completed linearity and the chain property. The conclusion
  `augmentation_(n+1) ≫ v_n = augmentation_n` is v_n theta_(n+1)=theta_n.
* Every equality is in `CochainComplex (integralTowerModules ...) ℤ`, before
  localization. No per-degree surrogate for a derived isomorphism is involved:
  this node expressly concerns strict chain-map equalities and no derived
  comparison is claimed or replaced.

Dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the publicly imported
  `Padic.coefficientExtensionRing`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal` and `coefficientExtensionTransition` constructions.
* `def-weil-scheme-morphism-properties` is explicitly a convention-only node;
  `Scheme`, scheme isomorphism and the stalk-unit expression render its uses.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  the recorded constant-quotient interface and its public completed-ring,
  coefficient-system and limit-projection declarations, including
  `integralConstantToCompletionOfUniverses` and
  `completedIntegralCoefficientSheafUnrestricted`.
* `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its public import
  `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageCompletedCoefficientMap`, `inverseImageFiniteCoefficientMap`,
  `inverseImageIntegralModules`, `inverseImageFiniteModules`, and
  `inverseImageFiniteComparison_existsUnique`. The derived evaluation is not
  used in place of the original finite tensor construction.
* `Sheaf.Paper.IntegralOperationsWellDefined` (publicly imported above):
  `integralOperationsFiniteModules`, `integralOperationsRestrict`,
  `integralOperationsLevelPullback`, `integralOperationsPullbackGenerator`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the recorded derived-category
  node publicly supplies the complex framework; the statement uses its ordinary
  `CochainComplex` and chain-map interface, not localization.
* `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`,
  `NatTrans.ofOpSequence`. Families of adjacent maps and commuting squares are
  retained directly, the equivalent presentation in the dependency's statement.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  sheaf tensor framework, publicly imported. The finite change-of-rings and
  generators are the existing normalized construction, not a new tensor.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, already used in `integralOperationsRestrict`.
* Proof dependency `lem-weil-proetale-isomorphism-inverse-image` is available
  through the public `IsoSectionwiseInverseImage` import, including the original
  coefficient naturality and the independent-universe sectionwise model.
* Proof dependency `lem-pc-sites-module-sheafification-interface` has status
  `mathlib`, so no Lean record repair is required. Its recorded matches in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` are imported for
  stage 3: `PresheafOfModules.sheafification`, `sheafificationCompToSheaf`,
  `sheafificationAdjunction`, and
  `toPresheaf_map_sheafificationAdjunction_unit_app`; the scalar-action
  uniqueness is `Subsingleton (PresheafOfModules.Sheafify.SMulCandidate ...)`.

Edge cases checked before and after drafting: g=id gives the ordinary tensor-unit
insertion; the first Lean level n=0 is the paper's n=1; zero systems, zero
augmentations and zero system maps satisfy the same formulas. The empty scheme
adds no nonemptiness assumption. Nonflat modules, nonsurjective w_n, arbitrary
unbounded complexes, and independent t,u all remain admissible. Because v is
specified for every b and every x before sheafification and equality is strict,
neither a generator-lifting assumption nor quotient flatness is hidden in the
conclusion. The unique maps are fixed by genuine section formulas; none is an
unconstrained comparison supplied by the caller.

Searches (full machine results are in `searches.jsonl`):

* msearch LeanFinder, "Tensor insertion for inverse image of sheaves commutes
  with quotient coefficient transitions and system maps": eight hits on free
  presentations and module pullback, no exact quotient-tower insertion theorem.
* msearch Loogle, `SheafOfModules.pullback, SheafOfModules.restrictScalars`:
  successful query, zero hits.
* msearch grep, `tensorUnit|tensorSection`, `Algebra/Category/ModuleCat`:
  three hits in presheaf and ordinary module monoidal files; no exact statement.
* msearch LeanSearch, "Inverse image sheaf tensor insertion is natural under
  semilinear changes of quotient coefficients": eight ordinary tensor quotient,
  tensor map, open immersion and pushforward hits; no exact theorem.
* rg of `quotient.tensor.insertion|quotientTensorInsertion` in `lean/Sheaf`
  and `lean/WeilConjectures`, and grep of the node id in `WeilConjectures`:
  no existing statement. Broader `tensor.*insertion|insertion.*tensor` searches
  found the recorded inverse-image comparison, `PointSystemTransportDescent`,
  `ConstantCompletionEquivalence`, and `LatticePullback`; their relevant full
  signatures and docstrings were read. The first supplies the canonical finite
  unit used here; the others specialize to a point/Frobenius, abstract completion
  equivalences, or lattices and do not state this arbitrary strict-system result.

Read the complete current blueprint proof at the node's source, especially
clause (3), and Stacks `sites-modules.tex` labels `section-tensor-product` (03EK)
and `lemma-sheafification-presheaf-modules` (03CY). The statement and proof agree
with those constructions. No mathematical defect or unit-level fault was found.

Validation: prescribed server scompile.py compiled the full module both as the
sandbox entry and under `Sheaf.Paper.QuotientTensorInsertion`, in 4.6 s and 5.1 s,
respectively, with no errors or non-sorry warnings. The first exploratory compile
found a scalar-action inference problem in `IsReductionLinear`; explicitly naming
the original finite target section type fixed it without changing any hypothesis.
All universes and variables are declared, and every source line is at most 100
characters. The independent review is the maintainer's delivery review, as the
dispatched brief directs; this report does not claim an independent self-review.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
