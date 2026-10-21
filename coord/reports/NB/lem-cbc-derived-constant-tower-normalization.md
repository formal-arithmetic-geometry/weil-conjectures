## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization` states
`CategoryTheory.RingedToposMorphism.existsUnique_derivedConstantTowerComparison`.
Its proof is `sorry`. Six auxiliary definitions spell out existing canonical
identifications and their representative normalization. The maps are compositions
of Mathlib natural transformations and isomorphisms; the predicate is the
explicit counit equation together with its inverse formula. There is no new axiom, tensor, module category, derived category,
resolution choice, or arbitrary comparison morphism.

Source read: `literature/stacks-project/derived.tex`, Tag 06XN,
`lemma-find-existence-computes`, including the dual left-derived clauses and proof;
the item's six proof steps; and the current blueprint proof
`sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`.
The latter invokes completed pullback and its reduction compatibilities; the item
expands the constant-tower portion. No statement correction is needed.

Hypothesis and clause correspondence:

- The two small sites are `{C D : Type u} [SmallCategory C] [SmallCategory D]`
  and `T`, `T'`. The commutative coefficient sheaves are `R`, `S`.
- The geometric adjunction, left exact inverse image, structural ring map and
  its induced module direct image are the fields of `f : RingedToposMorphism`.
  Its source is the S-site and target is the R-site, so pullback goes R to S.
- `E` with `[E.Additive]` and `adj : E ⊣ f.modules` represents precisely
  inverse image followed by extension of scalars, using the interface of
  `CochainComplex.diagram_pullback_quasiIso`. A left adjoint to this specified
  direct image is unique up to its canonical adjunction-compatible isomorphism.
  This neither assumes E is exact nor replaces pullback by an arbitrary functor.
- `ringedSiteModules` is the recorded module category; `DerivedCategory` and
  `DerivedCategory.Q` are the recorded derived localizations. The four
  `HasDerivedCategory` choices have independent morphism universes.
- Strict towers are the functor categories `ℕᵒᵖ ⥤ ringedSiteModules ...`.
  This is exactly the recorded inverse-system convention after shifting the
  paper's positive index by one. The tower pullback is
  `(Functor.whiskeringRight ℕᵒᵖ _ _).obj E`, applied degreewise to complexes.
- The chosen ordinary pair is `(L, ε)` with
  `L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))`.
  The arbitrary tower pair is `(Lt, τ)` with the analogous universal property.
  No chosen replacements, computational isomorphisms, or pointwise properties
  of the pairs are assumed in addition to universality.
- `Functor.const ℕᵒᵖ` and its `mapDerivedCategory` are the exact constant-tower
  functors on modules and derived categories. The `∃! b` inside
  `HasUniqueConstantTowerNormalizedComparison`
  states existence and uniqueness of the required natural isomorphism.
- `Functor.HasUniqueConstantTowerNormalizedComparison E L ε Lt τ W` expands to
  `∃! b : ConstantTowerDerivedComparison L Lt, ∀ P, W P →
  IsConstantTowerRepresentativeNormalized E L ε Lt τ b P`.
  The main statement supplies `W P := P.IsAcyclicTensorKFlat ∧
  ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)`, exactly the original two
  representative hypotheses. This is a fully defined transparent proposition,
  with the same comparison maps and no additional choices.
- Every representative `P` is quantified; `P.IsAcyclicTensorKFlat` and
  `∀ q : ℤ, SheafOfModules.IsFlat (P.X q)` select exactly the K-flat flat-term
  representatives, with no boundedness restriction.
- `constantTowerComplexComparison` is
  `NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ E) ...`.
  It identifies the constant complex of E(P) with E of the constant complex;
  its degreewise component at every tower level is the identity.
- Write δ for `Functor.const ℕᵒᵖ`, δK for its complex functor, δD for its
  derived functor, and ρ for `δ.mapDerivedCategoryFactors`. The helper
  `constantTowerDerivedSourceCounit E L ε` has component
  `δ'D.map (ε.app P) ≫ ρ'.hom.app (EK.obj P) ≫ Q.map (comparison.hom.app P)`.
  This is exactly Δ'(ε_P), with all canonical identifications inserted.
- `constantTowerDerivedTargetCounit E Lt τ` has component
  `Lt.map (ρ.hom.app P) ≫ τ.app (δK.obj P)`.
  Thus the displayed equality `b.hom.app (Q.obj P) ≫ target.app P = source.app P`
  is exactly the node's normalization τ_(ΔP) b_(QP) = Δ'(ε_P), in Lean's
  left-to-right composition order and the common strict-tower target.
- `Functor.ConstantTowerDerivedComparison L Lt` is transparently the displayed
  natural-isomorphism type `L ⋙ Δ'_D ≅ Δ_D ⋙ Lt`. It avoids re-elaborating
  concrete exact-functor instance data at every occurrence.
- `Functor.IsConstantTowerRepresentativeNormalized E L ε Lt τ b P` transparently
  packages the displayed counit equation and the following inverse formula. It
  introduces no assumption or chosen morphism and is defined over general
  abelian categories so elaboration need not unfold sheaf categories repeatedly.
- The final `∃ t : ... ≅ ...` with `t.hom = target.app P` asserts the
  invertibility already used in the node's inverse formula. The equation
  `b.hom.app (Q.obj P) = source.app P ≫ t.inv` is that formula. The specified
  forward map determines t and its inverse uniquely; no isomorphism is left
  arbitrary. Adding this consequence to the normalization predicate preserves
  uniqueness and records the node's last sentence explicitly.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the transparent general-site abbreviation for Mathlib `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, the recorded
  `SheafOfModules.cochainModulesMonoidal` and its related structures; no new tensor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `Qh`, and `quotientCompQhIso`.
  Universal pairs are stated on complexes, which the node explicitly allows;
  its proof can pass through the canonical homotopy quotient when using fractions.
- `Mathlib.CategoryTheory.Functor.OfSequence`, `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`, for the recorded strict-tower convention.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`,
  `CategoryTheory.Functor.leftDerived_from_resolvingClass`: the universal and
  representative-computation theorem. It is imported for the proof plan.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`,
  `CochainComplex.exists_diagram_isKFlatResolution` and
  `CochainComplex.diagram_pullback_quasiIso`; read both full signatures and
  docstrings. These supply resolutions and invariance for the same E/adj interface.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`,
  `CategoryTheory.Abelian.functorCategoryAbelian`, and the evaluation preservation
  instances in `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`: tower
  categories and exactness are the existing levelwise structures.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactors`:
  exact constant-functor localization and its canonical comparison.
- Proof-only imports: `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
  (left/right calculi); `WeilConjectures.CategoryTheory.NatTransFromResolvingClass`,
  `CategoryTheory.exists_natTrans_from_resolvingClass`; localization's
  `Localization.liftNatIso` and `Localization.natTrans_ext` (read in
  `Mathlib.CategoryTheory.Localization.Predicate`, already imported by the
  universal-derived-pair API).
- `Mathlib.CategoryTheory.Sites.Abelian` supplies the existing additive instance
  for the constant functor, so no duplicate exactness/additivity declaration is needed.

Edge cases checked: zero complex and zero coefficient ring are admitted; an empty
site is admitted; the positive tower's first level is Lean index zero, so it is
not discarded; complexes may be unbounded in either direction; there is no
assumption that E preserves quasi-isomorphisms outside the resolving class.
All sites and coefficients may be placed in a common containing universe, as in
the recorded small-site diagram dependency, and all four derived morphism
universes remain independent. There is no finite/infinite-index substitution:
the full strict countable tower is retained. Normalization is imposed only on
the flat-term K-flat class, not on all complexes.

Searches actually run:

- msearch LeanFinder: "Unique constant tower comparison of left derived ringed
  topos pullback normalized on K flat counits". Eight hits concerning ordinary
  sheaf pullback, pullback composition, and sheafification; none states this
  derived strict-tower normalization.
- msearch Loogle: `CategoryTheory.Functor.leftDerivedUnique`. One hit, the
  generic uniqueness theorem for two derived pairs of the same functor. Its
  full definition and context were read; it does not supply the tower comparison.
- msearch grep: `leftDerived.*[Cc]onstant|[Cc]onstant.*leftDerived|mapHomologicalComplex.*const`.
  Zero hits.
- msearch LeanSearch: "Constant tower and total left derived module pullback
  unique counit normalized natural isomorphism". Eight hits on generic derived
  uniqueness, counits, and ordinary projective resolutions; no exact match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id, constantTower,
  constant_tower, and constant/derived patterns. Results include unrelated
  constant sheaf/twist results and `PbcIntrinsicTowerComplete`, whose
  `constantTower` is coefficient-datum-specific, not this comparison.
- rg in Mathlib located `Functor.compConstIso`, `NatIso.mapHomologicalComplex`,
  the constant-functor limit and colimit preservation instances, and the existing
  additive constant-functor instance. These are used rather than recreated.
- Exact proposed declaration names were searched in `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`; none already exists.

Only the item's `lean` record changes. There are no new definition nodes,
dependency repairs, statement corrections, or statement disputes.

## Second reading by NB

Final reading by the author, under the dispatcher's explicit single-worker/no-agent
instruction. Independent review is left to the maintainer's delivery reader;
this section does not claim a separate worker performed it.

Reopened the node and module and checked the direction of f, the order R to S of E,
the arbitrary choices of both universal pairs, the strict `ℕᵒᵖ` diagram category,
and the order `L ⋙ Δ'_D` to `Δ_D ⋙ Lt`. In the two counit helpers, the exact-factor
isomorphism points `Q Δ_D → Δ_K Q`, so the target helper correctly uses its hom.
The termwise comparison points `E_K Δ'_K → Δ_K E_tK`, matching the source helper's
common target. Thus the equation compares parallel morphisms. The K-flat and
flat-term conditions both occur, and the inverse formula uses the very same
transported τ as the normalization. No hypothesis or conclusion was changed.
The first compile exposed an elaboration heartbeat limit at the type comparison;
transparent packaging of the comparison type and representative equation, with
explicit category and universe arguments, was introduced without changing its meaning.

## Saved-packet repair, 2026-10-21

The required first dry run reproduced the missing RingedToposMorphism artifact.
Explicit imports of the already-used ringed-topos module and the tensor, sheaf Hom,
and pointwise monoidal preadditive support modules let the prescribed server wrapper
resolve these published dependency sources. These introduce no declarations or
replacement constructions in this delivery.

The resulting compile reproduced the saved 200000-heartbeat failure at the concrete
representative predicate. Diagnostics showed repeated sheafCompose and ring-coercion
comparisons. Supplying explicit universes alone and suppressing exposure of the
counit definitions did not fix it. The repair changes the helper definition boundary:
HasUniqueConstantTowerNormalizedComparison packages the existence-and-uniqueness
quantifier and its representative normalization in the generic abelian-category
section. The concrete theorem specializes this once, instead of re-elaborating
concrete sheaf-category identifications for the comparison binder and predicate.
All helpers remain exposed with their actual bodies. No timeout or heartbeat
limit was raised, and no mathematical hypothesis, conclusion, or node statement
was changed.

Self-check: reopened all eight statement-dependency records and their source
interfaces, the item's six proof steps, and Stacks 06XN (dual). The normalized
source and target counits still point to the same strict-tower complex. The
representative predicate is unchanged; grouping its two hypotheses into a
conjunction is logically equivalent. The only postponed theorem remains the
recorded main theorem. Only the item's lean field changes.

## Validation

The final exposed-helper version passes scompile.py: sandbox compilation 26.4 s,
library compilation 26.4 s, with no warnings or errors. The required deliver2.py
--no-push passes server preflight and compilation: OK (dry run), commit f3498990d70.
The delivered signature is verbatim in lean.statement; all module lines are at
most 100 characters; no auto-bound variables or universes are used. A current
search across lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json
finds no collision for the main declaration or the new generic quantifier helper.

Final author reading also checked the sixth helper's body: it quantifies over
exactly ConstantTowerDerivedComparison L Lt and requires the unchanged normalized
predicate at every member of W. The concrete W contains both K-flatness and
flatness of every term. The scope of uniqueness is therefore exactly the original
representative normalization. No additional theorem or assumption was introduced.
