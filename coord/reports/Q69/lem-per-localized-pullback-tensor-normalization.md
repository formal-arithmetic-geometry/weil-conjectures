## Worker report

The module `Sheaf.Paper.LocalizedPullbackTensorNormalization` states
`CategoryTheory.LocalizedPullbackTensor.localizedPullbackTensorNormalization`, with one
postponed theorem and no proved theorem. The node's statement, proof and proof dependencies
are unchanged. Three already landed statement interfaces are added to `stmt_deps`:
`def-weil-pbc-algebraic-inverse-image`, `def-weil-pbc-successive-derived-quotient-data`, and
`lem-sfb-successive-derived-quotient-normalization`. A traversal of their statement and proof
dependencies found no path back to this item. No new DAG node or dependency repair is needed.

Source read: `literature/stacks-project/sites-cohomology.tex`, the statements and proofs at
labels `lemma-pullback-K-flat` (0G7E, line 3508), `lemma-derived-base-change` (06YY, line 3585),
and `lemma-derived-pullback-composition` (0D6D, line 3658), with the resolution input
`lemma-K-flat-resolution` (06YS, line 3207). The current blueprint's
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.proof.md` was also
read. The seven-step proof docstring follows the accepted DAG split, including both balancing
calculations, the zero-divisor fraction relation, degree-zero differentials and descent.

Hypotheses and clauses, with the Lean rendering:

- Both presented topoi: independent `C : Type uC`, `D : Type uD`, `Category.{vC}`,
  `Category.{vD}`, and `EssentiallySmall.{r}`. The sheafification and locally-bijective
  instances are the standard module and ring sheafification interfaces on these sites.
  There is no equality between the object, morphism, and coefficient universes. `hDC` and
  `hDD` give the chosen derived morphism universe `w` for the rings under consideration.
- Geometric morphism: `L`, `Lstar`, `adj : L ⊣ Lstar`, and `hL : PreservesFiniteLimits L`.
  `include adj ht hs hIt hL` retains the geometric and normalization hypotheses in the
  elaborated theorem even where the displayed conclusion only mentions their data.
  This is the decomposition of the recorded ringed-topos morphism into its inverse-image
  adjunction and structural map, rather than a requirement that a site functor induce g.
- Coefficients B, R = g inverse B, S, and arbitrary c: `B`, `R`, `S`,
  `I : SheafOfModules.AlgebraicInverseImage L B R`, and `c : R ⟶ S`. The recorded algebraic
  inverse-image interface fixes the ring operations and the module functor by generalized
  elements and its natural underlying-sheaf isomorphism.
- Global t, its inverse image t prime, and its c image s: `t`, `t'`, `s`,
  `ht : IsInverseImageSection I t t'`, and `hs W : s.val W = c_W (t'.val W)`.
- V, R_t and U: everywhere the exact existing `ringedLocalizationRingOfUniverses B t`,
  `ringedLocalizationRingOfUniverses R t'`, and `ringedLocalizationRingOfUniverses S s`.
  Their maps are `ringedLocalizationRingUnitOfUniverses`, not arbitrary ring maps.
- The canonical identification g inverse V = R_t is expressed by `It`, an algebraic
  inverse image over that ring, and `hIt : UnitNormalized ... It`. The latter is exactly
  the localization-unit equation in `existsUnique_localizationInverseImageRing` after
  transporting the coefficient ring by its unique normalized isomorphism. In particular
  it excludes twisting the identification. This is data presenting the same inverse
  image, not a different construction or an assumption that it commutes with localization.
- Exactness instances on `I.modules` and `It.modules` are their forced exactness, supplied
  by the recorded `localization_inverseImage_exact`. They are not assumptions of flatness
  on c. No invertibility, monomorphism, flatness, or epimorphism instance on c occurs.
- `presentation a` specializes the already existing `Presentation a`, whose ordinary
  object and map equations are precisely sheafified `changeOfRings a` and whose derived
  functor has its universal left-derived counit. `normalization` specializes the existing
  `Normalization` witness. Selection uses the already proved
  `successive_derived_quotient_normalization`, with the universal property fixing the
  derived objects up to the unique comparison used here. No data comes from a new sorry.
- The map R_t to U is the existential `e` with the equality witness `he`. Its local
  fraction normalization is the first quantified clause: `e(fraction R t' r m)` equals
  `fraction S s (c r) m`. Here `fraction` is a real sectionwise Localization.Away numerator
  times `invSelf` to the mth power, followed by the actual ring sheafification unit.
  Thus fraction relations are built into its input type. The formula is c(r)s^(-m),
  including zero divisors, rather than a new symbol for an unspecified fraction.
- Pullback of V tensor T is identified with R_t tensor N by `gamma`, an ordinary natural
  isomorphism. Its generalized pure-tensor equation tests every sheaf T and every triple
  v,x,y with y = v tensor x, then applies the recorded inverse-image identifications.
  It therefore fixes the whole sheafified map; it does not assert that all sections are
  global pure tensors. Its inverse on the displayed pure tensors is forced by that
  equation and `gamma`'s inverse identities.
- The main natural isomorphism `a` has source g inverse, then derived R-to-S extension,
  then derived S-to-U extension, and target g inverse followed by derived R-to-U
  extension. This is exactly the first displayed isomorphism in D(U).
- `b` has source derived B-to-V extension, exact localized inverse image, then derived
  R_t-to-U extension, and the same target as a. The unit normalization of It identifies
  this with the second displayed isomorphism over g inverse V.
- Both are `NatIso`s between functors on all of D(B); hence their components exist for
  every K and are natural for every derived morphism, including inverse quasi-isomorphisms.
- `FlatK` is only the conjunction of `IsKFlatIndependentCoefficients` and
  `∀ n, IsFlatOnSite (T.X n)`. The eight conclusions for every FlatK T give flat terms
  and K-flatness of V tensor T, N, S tensor N, R_t tensor N, U tensor N,
  U tensor_S (S tensor N), U tensor_R_t (R_t tensor N), and g inverse (V tensor T).
- The final two equations identify a and b at Q(T) through the canonical derived
  computation counits and exact-functor factorization isomorphisms. The ordinary maps
  used there are precisely `(normalization).ordinary`, whose `ordinary_hom` field is
  u tensor (v tensor n) mapped to b(v)u tensor n and whose `ordinary_inv` inserts one.
  Commutativity gives the node's uv ordering. The second map uses e, so its fraction
  equation makes this u c(r)s^(-m) tensor n; its inverse also inserts one, with gamma
  transporting the canonical pulled-back localization. These formulas are encoded by
  the existing Normalization definition, not replaced by bare existence of isomorphisms.
  `mapHomotopyCategoryCompIso` sends these actual ordinary natural isomorphisms termwise
  to complexes and then to homotopy categories. Their complex maps commute with all
  differentials by construction. The universal computation counits are invertible here:
  this follows from `normalization.computed`, `intermediate_computed`, and the asserted
  preservation of FlatK. Thus these are actual computation comparisons.
- The equations hold for every flat-term K-flat T, without choosing a particular
  resolution. Naturality of a and b transports these equations along every resolution
  T to K; the resulting comparison is the same fixed a_K or b_K for every resolution.
  No boundedness, constructibility, functorial resolution, or restriction on K occurs.

Dependency declarations read and used:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its resolution predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the canonical tensor
  instances; the ordinary scalar tensors are the recorded change-of-rings construction
  exported through `DerivedChangeOfRingsIndependentCoefficients`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, and the homotopy quotient.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `ringedLocalizationRingOfUniverses`, its unit, and its actual localization presheaf.
  The current source was also read using `scompile.py --source` while checking elaboration.
- `Sheaf.CategoryTheory.RingedToposMorphism`: the geometric adjunction, left exactness and
  structural-map signature; the theorem spells these data out at independent universes.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, used by `Modules`.
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`:
  `IsInverseImageSection`, `localizationModuleSets`, `localization_inverseImage_exact`,
  `existsUnique_localizationInverseImage`, `existsUnique_localizationInverseImageRing`.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`:
  `ringedTopoiDerivedPullbackIndependent`, its universal counit computation and resolution
  comparison normalization; the displayed equations use precisely these universal pairs.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` publicly retains the recorded
  equal coefficient/module-universe `AlgebraicInverseImage` used here; coefficient and
  module universes are both r, while the site universes remain independent.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData`: `Modules`, `Presentation`,
  `Normalization`, `sectionTensor`; `SuccessiveDerivedQuotientNormalization` supplies
  `successive_derived_quotient_normalization`. Both declarations and full field signatures
  were read. The proof-dependency modules are also imported with plain imports as required.

Edge cases checked mathematically before writing: zero complex; zero ring sheaves; t=1;
t=0 or nilpotent t, so U and R_t may be zero; c nonflat, for example Z to Z/2 with t=3;
identity geometric morphism and identity coefficient map; empty sites/empty site objects;
unbounded T in both directions. Tensor balancing and the fraction identity are valid
in all these cases. No nonzero, nonempty or boundedness condition was added. Independent
site universes preserve the small pro-etale convention. No statement dispute or correction.

Searches actually run:

- msearch LeanFinder: `Derived pullback commutes with localization of coefficient sheaves
  with balanced tensor flattening on K flat resolutions`: eight hits, led by
  `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, `pullbackComp`, and
  `pullbackIso`; ordinary site-functor pullbacks, not the full statement here.
- msearch Loogle: `SheafOfModules.pullbackComp`: five ordinary pullback composition,
  identity, associativity, and conjugation hits, not localization-normalized unbounded
  derived comparisons with the resolving-class assertions.
- msearch grep: `pullbackComp|localization.*tensor` in `Algebra/Category/ModuleCat`:
  ten hits on ordinary sheaf and presheaf pullback composition.
- msearch LeanSearch: `Derived tensor extension of coefficient sheaves along ring maps
  is associative on K flat resolutions`: eight hits including
  `ModuleCat.extendScalars_assoc`, `SheafOfModules.pushforward_assoc` and ordinary tensor
  associators; no exact match for this item.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for the item id and the proposed
  declaration name: no exact declaration. Related-name searches found the existing
  `RingedDerivedMonoidalComparisons` and `SuccessiveDerivedQuotientNormalization` modules.
  Their signatures and the latter's `SuccessiveDerivedQuotientData` were read. The former
  is a general monoidal system; the latter gives the scalar flattenings reused here,
  but neither alone states this geometric/localization pair with its fraction and FlatK
  clauses. A further fraction-helper search in the localization modules found no public
  existing fraction helper to reuse.

Validation: `scompile.py Q69 lem-per-localized-pullback-tensor-normalization` checked the
single delivered module both as sandbox and as `Sheaf.Paper.LocalizedPullbackTensorNormalization`;
both passed with no errors or warnings. Initial compiler failures were namespace collisions
and inference in the fraction helper; qualifying names and the coefficient types resolved
these without changing the mathematical statement. Dry-run and delivery results follow.

## Second reading by Q69

No second reading by another worker: this dispatcher assignment explicitly forbids starting
agents and delivers directly. The maintainer's independent review is the independent reading.

Dry run: `deliver2.py Q69 lem-per-localized-pullback-tensor-normalization --no-push`
returned `OK (dry run)` for commit `fdd8300b3b4`: maintainer preflight and both compile
passes succeeded. No files outside the single module, item node and report are delivered.
