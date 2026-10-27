## Worker report

Item: `lem-sfb-resolved-total-augmentation-square`. Module:
`Sheaf.CategoryTheory.ResolvedTotalAugmentationSquare`. Main statement:
`CategoryTheory.resolved_total_augmentation_square`. The only postponed theorem is
that statement; its proof is `sorry` and its docstring gives the six-step DAG proof.
No statement correction, new node, or dependency-record repair is needed.

The theorem asserts `Nonempty (ResolvedTotalAugmentationSquare F)`. The auxiliary
structures package this node's canonical maps and equations. This is not an arbitrary
comparison: `augmentation_component` determines each augmentation component,
`beta_summand` determines beta on every finite summand, and `rho_inverse` specifies
rho's inverse as the existing derived unit, including its extension-by-zero transport.
These equations uniquely determine the morphism data. The three helper definitions
are actual composites of this normalized data, with no choice and no postponed proof.

Hypothesis and clause correspondence:

- Grothendieck abelian categories are the explicit `C : Type u`, `D : Type u'`,
  independent `Category.{v}`, `Category.{v'}`, `Abelian` and
  `IsGrothendieckAbelian.{v}`, `IsGrothendieckAbelian.{v'}` binders. Independent
  `HasDerivedCategory.{w}` and `HasDerivedCategory.{w'}` binders select ordinary
  unbounded localization models. K-injective resolutions are inferred from the
  Grothendieck instances, rather than imposed as an extra hypothesis.
- Left exact additive F is `(F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]`.
  The structure has no left-exactness binder because its fields are meaningful for
  additive F; the existence theorem imposes exactly the node's hypothesis.
- Delta is Mathlib `SimplexCategory`, including all nonempty finite ordinals and all
  order-preserving maps. Strict diagrams and strict maps are functors and natural
  transformations `CosimplicialObject (CochainComplex C ℕ)` and `K ⟶ J`.
- Nonnegative complexes use `CochainComplex C ℕ`. T is the existing alternating
  coface complex followed by `HomologicalComplex₂.totalFunctor` with all three
  shapes `ComplexShape.up ℕ`. Thus its differential is delta + (-1)^n d_C and its
  summands have n+q=r, with no infinite sum in a fixed degree. Some object terms use
  the definitionally identical `HomologicalComplex₂.total` application directly.
- Ordinary Q on these complexes is exactly
  `ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q` (and D).
  Extending by zero realizes these as objects of the unbounded derived category.
- The fields `square`, `columns`, and `lifts` quantify over the actual complexes A,B,
  diagrams K,J, augmentations b,c, and maps v,u. `QuasiIso v` and
  `∀ n, QuasiIso (u.app n)` retain precisely both quasi-isomorphism hypotheses.
  `hB : ∀ q, Injective (B.X q)` and `hJ : ∀ n q, Injective ((J.obj n).X q)` retain
  both termwise injectivity hypotheses. Compatibility is
  `b.app n ≫ u.app n = v ≫ c.app n`, which is u_n b_n = c_n v in usual notation.
- `augmentation b` and `augmentation c` are actual chain maps. Their components are
  exactly b_0 or c_0 followed by `ιTotal ... 0 r r (zero_add r)`; equality with this
  inclusion encodes zero in every other cosimplicial summand, not an unspecified
  map with the right cohomology. `augmentation_naturality`, specialized to h=v,
  f=u, is a_J v = T(u) a.
- `beta` is an isomorphism F(TJ) ≅ T(FJ); `beta_summand` gives its canonical finite
  biproduct normalization for every n,q,r with n+q=r. `beta_naturality` retains
  compatibility with every strict map. `totalInjective` records injectivity of
  the finite diagonal, allowing rho at T(J).
- `rho E hE` is an isomorphism RF(QE) ≅ QF(E). Its inverse is
  `Q.map (E.mapExtendIso ... F).inv ≫ F.rightDerivedFunctorUnitQ (E.extend ...)`.
  This is the ordinary inverse derived unit after the canonical zero-extension
  identification. It includes B, every J_n, and T(J).
- `sourceComparison v hB` is RF(Qv) followed by rho_B, the node's c_v.
  `totalComparison u hJ` is RF(QT(u)), then rho_T(J), then Q(beta_J), exactly chi_u.
  `comparison_isIso` ensures these normalized composites are isomorphisms whenever
  v and every column of u are quasi-isomorphisms.
- `mappedAugmentation c` is the explicit chain-map composite F(a_J) ≫ beta_J.
  `square` is RF(Qa) ≫ chi_u = c_v ≫ Q(beta_J F(a_J)), exactly the displayed node
  equality, in Lean's diagrammatic composition order. This is equality of maps of
  whole ordinary derived objects, not merely of cohomology maps.
- `mapped_component` identifies that composite with F(c_0) followed by the
  degree-zero inclusion. Thus its other cosimplicial components vanish.
- `columns` states RF(Qb_n) ≫ c_(u_n) = c_v ≫ QF(c_n). The column comparison is
  the same `sourceComparison (u.app n) (hJ n)` definition, hence exactly
  RF(Qu_n) followed by rho_(J_n).
- For strict augmented (h,f), `augmentation_naturality` gives the strict total
  augmentation square without requiring an injective replacement at all. The same
  field with h=ht and f=g gives the square on injective replacements.
- `lifts` quantifies over two entire replacement diagrams and *arbitrary* h,f,ht,g.
  It retains both augmentation compatibilities, both strict augmented-map
  compatibilities, and u ≫ g = f ≫ u', v ≫ ht = h ≫ v'. Its four conclusions are:
  the mapped strict square m T(Fg)=F(ht)m'; naturality of c_v; naturality of chi_u;
  and the common localized augmentation-square composite. Combining its last
  equality with `square` for the primed diagram gives the final expression
  chi_u' RF(Qa') RF(Qh) in the DAG proof. No preferred lift is chosen and none is
  assumed to exist beyond the node's conditional statement.
- Every field quantifies universally over its diagrams and compatible replacements;
  the existence assertion constructs one family of the uniquely normalized maps.
  It therefore states the result for every replacement, not merely one resolution.

Dependency declarations read and used:

- `def-sp-double-complex-total`: `WeilConjectures.CategoryTheory.DoubleComplexTotal`
  and its existing Mathlib `HomologicalComplex₂.total`, `totalFunctor`, `ιTotal` and
  `ComplexShape` sign convention. `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`
  supplies the finite nonnegative diagonal instance.
- `def-sp-grothendieck-abelian`: Mathlib
  `CategoryTheory.IsGrothendieckAbelian`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `def-sp-injective-resolutions`: Mathlib `CategoryTheory.Injective`, imported by
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. The node concerns
  quasi-isomorphic replacements of whole complexes, so its hypotheses use termwise
  `Injective` and `QuasiIso`, rather than `InjectiveResolution` of a single object.
- `def-sp-left-exact-additive`: Mathlib `Functor.Additive`, `PreservesFiniteLimits`;
  `Mathlib.CategoryTheory.Preadditive.LeftExact` gives their abelian left-exact meaning.
- `sk-def-sfb-derived-categories`: `DerivedCategory`, `DerivedCategory.Q`, the
  ordinary K-injective `Functor.rightDerivedFunctor` and `rightDerivedFunctorUnitQ`.
  Its recorded note explicitly permits the canonical upstream K-injective convention
  on Grothendieck categories. The generalized recorded module
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` is also imported.
  The unit normalization uses
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`;
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` supplies
  Grothendieck resolution instances. No alternative RF is defined here.
- Proof dependency `def-sfb-right-derived-functor` is imported from its recorded
  module. Proof dependency `lem-sfb-injective-finite-total-derived-comparison` has no
  Lean record or module in the read repository; its mathematical statement was read,
  and the proof docstring explicitly invokes it. Its undeveloped proof is not a
  missing notion needed to type the present statement, so no dependency is restated.

Sources read: current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`
paragraph (3); Stacks `derived.tex` lemma-functorial-injective-resolutions and
remark-match (0141), lemma-two-ss-complex-functor (015J). The source uses genuine
injective replacements, finite totals, and compatible strict maps. The node spells
out the formal augmentation and inverse-unit naturality calculations beyond that text.

Edge cases checked: total degree zero has only (0,0); no empty diagonal occurs in
nonnegative total degrees. Zero complexes and zero augmentations satisfy the component
formulas. The identity replacement and identity strict lift give the unit-normalized
identity squares. Arbitrary non-monomorphic quasi-isomorphisms remain permitted: no
Mono or chosen-resolution binder is added. All simplex operators, including
codegeneracies, are retained through functors and natural transformations. All object,
hom, and localization universes are explicit and independent for C and D; no accidental
identification of site object and morphism universes occurs.

Searches performed (2026-10-24):

- `msearch.py ... leanfinder "Strict cosimplicial augmentation map to the nonnegative
  total complex commutes with right derived functor injective replacement comparisons"`:
  8 hits, including `InjectiveResolution.toRightDerivedZero_eq`,
  `toRightDerivedZero'_naturality`, `rightDerived_app_eq`,
  `Functor.rightDerived_map_eq`, and `isoRightDerivedObj_hom_naturality_assoc`.
  These concern individual-object resolutions and do not state this augmentation
  square of whole ordinary derived objects.
- `msearch.py ... loogle '"alternatingCofaceMapComplex", "augmentation"'`: 0 hits.
- `msearch.py ... grep
  '(cosimplicial|Cosimplicial).*(augment|Augment)|(augment|Augment).*(cosimplicial|Cosimplicial)'`:
  15 hits, in augmented simplex/simplicial-object and Cech-conerve definitions;
  no normalized finite-total derived augmentation square.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for cosimplicial totals, augmentation, and the proposed declaration names found
  no existing declaration of this node. The existing downstream
  `NonnegativeDerivedTotalization.lean` bundles a related augmentation conclusion
  into a larger theorem, but has no column-augmentation or compatible-lift clauses
  equivalent to this node. Its aliases were read; the present file directly applies
  their existing Mathlib constituents and defines no second total or localization.
  Importing that downstream theorem would create a proof-import cycle.
- Exact-ID search in `lean/WeilConjectures` found no occurrence. A source-wrapper
  probe for `Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison` reported
  unavailable, consistent with the proof dependency's missing Lean record.

No STATEMENT-DISPUTED issue was found. Only `lean` changes in the copied item node.
The final module is checked by `scompile.py`, separately in sandbox and module mode.

## Second reading by Q97

A second in-thread audit matched the node against every field and helper above.
It removed an initial definitional tautology from the column clause, checked the
order of all four lift equations, and checked that rho is fixed by the actual unit,
not an arbitrary isomorphism. The audit also removed the import of the downstream
totalization theorem to avoid a future proof-import cycle. Independent maintainer
review is the delivery's independent reading under the dispatcher brief; no separate
agent was launched and this section does not claim an independent worker review.
