## Worker report

Item: `lem-a1-mixed-direct-summand`; group Q48; stage 2.
The node's statement, statement dependencies, proof and proof dependencies are unchanged.
The current blueprint text (main-20261015, order 3155) agrees with the node.

The delivery uses a mixed declaration record: existing upstream declarations supply the
four sheaf clauses. The new module `Sheaf.Paper.MixedWeightsStability` supplies a
conjunction of the four Frobenius-module closure assertions. Its only new theorem has
a `sorry` proof and a source/proof-plan docstring. There are no new definitions.

Hypotheses and clauses:

- The four existing sheaf declarations are in the live module
  `WeilConjectures.DeligneLaumon.Reduction.Weights`. Their context binds
  `{k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]`,
  `[Fact (ringChar k₀ ≠ l)]`, `{X : Scheme.{u}}`,
  `[X.Over (Spec (CommRingCat.of k₀))]` and
  `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]`.
  Thus every finite-type base scheme in the node is covered, with no separatedness.
  They work even without quasi-compactness; this is existing generality, not a new
  strengthened statement in the delivery. The real upper bound is `{w : ℝ}`.
  `{ι : PadicAlgCl l →+* ℂ}` receives the underlying ring homomorphism of the
  fixed field isomorphism. Mathlib `PadicAlgCl l = AlgebraicClosure ℚ_[l]` is the
  fixed closure of this recorded punctual-weight interface.
- Clause 1, subsheaves: `...IsMixedOfWeightsAtMost.of_mono` takes
  `(i : G ⟶ F) [Mono i] (h : F.IsMixedOfWeightsAtMost ι w)` and concludes
  `G.IsMixedOfWeightsAtMost ι w`.
- Clause 1, quotients: `...of_epi` takes `(p : F ⟶ G) [Epi p]` and mixedness
  of F, and concludes mixedness of G.
- Clause 2: `...of_shortExact` takes `{S : ShortComplex (WeilSheaf k₀ l X)}`,
  `(hS : S.ShortExact)`, and mixedness of S.X₁ and S.X₃, concluding mixedness
  of S.X₂. This is exactly the node's short exact sequence assertion.
- Clause 3: `...of_retract` takes `(h : Retract G F)` and mixedness of F,
  and concludes mixedness of G. `Retract` means Weil morphisms i and r with
  `i ≫ r = 𝟙 G`. In an abelian category this is a direct summand, with
  complement ker r. No direct-summand case is omitted. All four morphism clauses
  are in the concrete Weil category and therefore impose Weil equivariance.
- Frobenius modules use exactly `FrobeniusModule.IsMixedOfWeightsAtMost` from
  `Sheaf.LinearAlgebra.FrobeniusModuleWeights`, not upstream `HasWeightsAtMost`.
  The parameters `p a ell`, `[Fact p.Prime]`, `ha : 1 ≤ a`, `[Fact ell.Prime]`,
  `hellp : ell ≠ p`, an algebraic closure `Qlb` of ℚ_[ell], its field isomorphism
  `iota : Qlb ≃+* ℂ`, and the real bound w are explicitly bound. The predicate
  uses the fixed prime power p^a. Module carrier universes u₁, u₂, u₃ and
  coefficient universe v are independent and explicitly declared.
- First module conjunct: an injective equivariant linear map A → B and mixedness of
  B imply mixedness of A. This expresses every Frobenius-stable subobject, not only
  inclusions whose carrier is literally a subtype.
- Second module conjunct: a surjective equivariant linear map A → B and mixedness
  of A imply mixedness of B, expressing all stable quotients.
- Third module conjunct: equivariant linear maps A → B → C with
  `Function.Injective f`, `Function.Exact f g`, and `Function.Surjective g`
  express `0 → A → B → C → 0`. Mixedness of A and C concludes mixedness of B.
- Fourth module conjunct: both i and r are Frobenius-equivariant, and
  `r.comp i = LinearMap.id` says that A is a direct summand of B as a Frobenius
  module. Mixedness of B implies mixedness of A.

Dependency declarations read and used:

- `WeilConjectures.DeligneLaumon.Reduction.Weights`:
  `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost`, the finite filtration with
  zero first term, terminal term isomorphic to F, mono transitions, and cokernels
  punctually pure of real weights ≤ w. Its `of_mono`, `of_epi`, `of_shortExact`, `of_retract` already
  give all four sheaf clauses (live source read through scompile.py --source). Purity is defined in `WeilConjectures.WeilSheaf.Stalk` by
  local geometric Frobenius at all finite/closed points, with residue cardinality q_y.
- `WeilConjectures.WeilSheaf.Category`: `AlgebraicGeometry.WeilSheaf` is concretely
  the full constructible subcategory of pro-etale sheaves with a Frobenius-pullback
  isomorphism. `WeilConjectures.WeilSheaf.StalkFunctor` supplies exact equivariant stalks.
- `Sheaf.Paper.SfWeilSheafComplex`: the recorded `WeilConjectures.sfWeilComplex`,
  `sfWeilSheaf`, and `sfCommonStageWeilSheaf` are fixed pairs and their full
  heart-carrier subcategories. `Sheaf.Paper.SfConstructibleHeart` supplies the
  recorded rational and common-stage heart definitions. Both dependency modules
  are public imports. The sheaf clauses retain the concrete sheaf presentation
  mandated by the recorded punctual-weight predicate; they never use
  `AlgebraicGeometry.WeilComplex`, the upstream derived category of Weil sheaves.
  This delivery does not claim a new comparison between the two presentations.
- `Sheaf.LinearAlgebra.FrobeniusModuleWeights`:
  `FrobeniusModule.IsMixedOfWeightsAtMost` is the existing finite stable-filtration
  predicate, including its specified induced quotient Frobenius.
- Proof-only imports: `Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient`,
  `FrobeniusModule.IsMixedOfWeightsAtMost.subquotient`; and
  `Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds`,
  `FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact`. Their full signatures
  and docstrings were read. They give exactly the two proof dependencies named
  in the node. They are imported without `public`.
- `CategoryTheory.Retract`, imported by the upstream weight module, supplies
  the direct-summand datum without a private predicate.

Edge cases checked before writing: the zero sheaf/module admits the length-zero
filtration; a zero graded piece is pure of every weight vacuously. Thus kernels,
zero quotients, identity maps and the zero retract are all covered. Empty schemes
and arbitrary real w are allowed. Nonsemisimple Jordan blocks are allowed: only
stable filtrations are required, not stable complements. Finite type includes
nonseparated schemes. No scheme or module carrier is assumed nonempty/nonzero.
In module extensions, the carrier universes need not agree.

Searches (full service results also saved in sandbox searches.jsonl):

- msearch.py leanfinder: “Mixed Weil sheaves closed under subobjects quotients
  extensions direct summands” returned eight general category results, chiefly
  `CategoryTheory.ObjectProperty.IsSerreClass`; no weight-specific theorem.
- msearch.py loogle: “IsMixedOfWeightsAtMost, of_retract, of_mono” returned no
  hits, unknown identifier IsMixedOfWeightsAtMost.
- msearch.py grep: `IsMixedOfWeightsAtMost|IsPunctuallyPureOfWeight` returned zero
  Mathlib hits.
- msearch.py leansearch: “Mixed Weil sheaves are stable under subobjects quotients
  extensions and direct summands” returned eight general sheaf/Serre-class results,
  with no weight-specific declaration.
- rg over the entire upstream WeilConjectures tree found the existing sheaf
  filtration predicate and `of_mono`, `of_epi`, `of_exact`, which are reused in
  the mixed record. The local snapshot lacks of_shortExact and of_retract, but
  the canonical live source read with scompile.py --source contains both. Their
  full signatures/docstrings were read and all four live sheaf declarations are reused.
- rg over project lean/Sheaf found the current module-filtration definition,
  mixed-subquotient and extension theorems, and punctual-bound-to-mixed theorem.
  None supplies the whole module stability statement, and no new predicate is made.
- rg for the exact blueprint id in the upstream tree returned no hits.
- rg of the upstream tree, Mathlib and project for the new stability theorem name
  found no collision.

No statement correction, new node or dependency module is made. No mathematical
counterexample was found and no STATEMENT-DISPUTED flag is raised.

## Second reading by Q48

This is a separate rereading by the assigned worker, not a claim of an independent
agent review: the dispatcher explicitly prohibits starting another agent and assigns
independent review to the maintainer after delivery.

Reread the node and the final module together. The initial draft repeated the sheaf
mono/epi/extension assertions in a conjunction; removed that repetition and recorded
the exact existing declarations instead. A subsequent compile detected an already
declared of_retract; scompile.py --source revealed the newer live source and the
redundant new retract theorem was removed. The mixed record now reuses the exact
of_shortExact theorem as well. Confirmed w is real and the retract is in the Weil
category; the module iota is a field isomorphism. The sheaf theorems accept its
underlying ring homomorphism and therefore include the fixed-isomorphism case. The module mixedness predicate is the current
filtration predicate; it has not been replaced by a pointwise eigenvalue inequality.
The injection/surjection clauses require actual Frobenius equivariance; the exact
sequence has all three endpoint/exactness hypotheses; the retraction equation has
the correct order r after i and both maps are equivariant. Every closure conclusion
keeps w unchanged. No added semisimplicity or separatedness assumptions.

Validation: the final scompile.py invocation passed with no errors or warnings.
It checked the sandbox file (12.1 s) and named library module (24.6 s), under the
normal 60 s per-file limit. No direct compiler invocation or global build was run.
