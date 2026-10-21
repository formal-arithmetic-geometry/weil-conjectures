## Worker report

The module `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction` states
`SheafOfModules.SequenceProjection.derivedAdjunction`. Its only postponed proof is this
named theorem, with the complete six-step DAG proof in its docstring. The three helper
declarations are transparent specializations of existing module categories and scalar
restriction, and the actual sheafification-unit image of a local scalar-extension tensor.
They contain real data. No node statement, proof, dependency list or existing module changes.

Source read: `literature/stacks-project/sites-cohomology.tex`, section-derived-limits
(opening paragraphs before lemma-derived-limit-is-ok), lemma-derived-base-change, and
lemma-adjoint. The first passage identifies constant inverse image and limit direct image;
the second computes unbounded pullback on flat-term K-flat representatives; the third gives
the canonical derived adjunction. The node's application adds its structural ring maps.

Hypothesis and clause correspondence:

- Small site C: `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}` and
  `[EssentiallySmall.{w} C]`. Object, morphism, coefficient and derived-Hom universes are
  independent. The HasSheafCompose, WEqualsLocallyBijective and HasSheafify witnesses
  are precisely those of the recorded sequence-site interface; they implement sheaf
  composition, module sheafification and the abelian structure, with no geometric
  restriction on the small site.
- Inverse sequence of commutative ring sheaves: `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}`.
  As in `systemLevel`, index n means the positive index n+1. This reindexing omits no level.
- Strict semilinear systems, componentwise exactness, and their identification with
  sequence-site modules: use the existing `StrictRingSystem B`, its existing canonical
  Abelian instance, and import `strictSystemSequenceEquivalence`. The target derived
  category is `DerivedCategory (StrictRingSystem B)`; no new category or exact structure
  is chosen. The equivalence is the one already attached to the statement dependency.
- Base ring and compatible structural maps: `A : Sheaf J CommRingCat.{w}` and
  `α : (Functor.const ℕᵒᵖ).obj A ⟶ B`. Naturality of α is exactly compatibility with every
  transition of B. This is the coefficient datum of the stated projection with constant
  underlying inverse image; there is no arbitrary geometric map substituted for p.
- Unbounded derived categories: both `HasDerivedCategory.{d}` binders choose the common
  localization universe allowed by def-weil-abstract-derived-category. No truncation,
  boundedness or resolution hypothesis is imposed.
- Ordinary pullback tensor formula: the existential additive functor G has level
  isomorphisms `e M n` to the existing `changeOfRings (α.app (op n)) M`, which sheafifies
  the sectionwise balanced tensor. The first conjunct gives naturality on module maps.
  The second gives transitions explicitly on all local pure tensors, with scalar sent
  by the actual map `B.map (homOfLE h).op` and x unchanged. `tensorSection` is the
  sheafification-unit image of b tensor x, which is the scalar-first convention for
  the paper's x tensor b. G therefore supplies the specified strict complex, rather
  than unrelated choices at different levels.
- Ordinary direct image as the limit of scalar restrictions: F is additive, and
  `π N n : F.obj N ⟶ (restriction A B α n).obj (N.level n)` are its projections.
  The third and fourth conjuncts impose naturality in N and transition compatibility.
  The fifth is the entire limit universal property: for every module M and every
  compatible family of A-linear maps f_n, there is a unique h with `h ≫ π N n = f n`.
  This spells out the limit without introducing a second scalar-restriction diagram
  definition or an unconstrained comparison object. It determines the sheaf, its
  A-action, restriction maps and functoriality by the universal property.
- Ordinary Hom correspondence: `adj : G ⊣ F` and the sixth conjunct assert exactly
  `((adj.homEquiv M N).symm h)_n(b tensor x) = b • π_n(h(x))`, under e.
  The full adjunction gives its inverse and naturality in both variables.
- Existence and meaning of Lp* and Rp*: the last existential supplies L, R, comparisons
  ε and η, `L.IsLeftDerivedFunctor ε ...quasiIso...` and
  `R.IsRightDerivedFunctor η ...quasiIso...`. Thus these are universal derived functors
  of the specified ordinary G and F, not arbitrary functors with an abstract adjunction.
- One flat-term K-flat representative Q→P: the left comparison is invertible for every
  `Q.IsKFlatIndependentCoefficients` with `∀ i, (Q.X i).IsFlatOnSite`.
  The later representative clause gives an isomorphism c from L[P] to [GQ], characterized
  by `L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q` for every quasi-isomorphism q.
  GQ has all the levels and transitions just described. No independent choice of Q_n
  occurs. Naturality in derived P follows from the natural transformation ε and the
  displayed characterization; in particular it holds after inverting denominators.
- The right comparison is invertible on every K-injective I, specifying computation of
  Rp* by ordinary limit direct image on K-injective representatives.
- Canonical derived adjunction and fractions: `derivedAdj : L ⊣ R` is normalized on
  EVERY chain map `f : GQ ⟶ I`, with no flatness or K-injectivity restriction on this
  equation. It says the derived transpose of `ε_Q ≫ [f]` is the ordinary transpose
  followed by η_I. Bifunctoriality then gives the node's fraction formula by
  precomposing with L([q]) inverse and postcomposing with [j] inverse. With I K-injective,
  η_I is invertible and identifies R[N] with [FI]. Applying the normalization to the
  ordinary transpose of h:Q→FI gives exactly the stated h-fraction correspondence.
  Naturality extends it to further denominators, without claiming a single Q represents
  every derived morphism by a chain map.

Recorded dependency declarations read and used (directly or by public import):

- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (the `restriction` abbreviation uses this exact functor).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded site's Grothendieck-topology
  and sheaf presentation, available transitively through SystemScalarModel and
  SystemLevelLeftExtensionBasic. The coverage predicate is not redefined.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.strictSystemSequenceEquivalence`, `systemSequenceModules`;
  its public prerequisite `SystemLevelLeftExtensionBasic` gives `StrictRingSystem`,
  `systemLevel`, `systemRestriction`, the canonical Abelian structure and exact evaluation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`;
  the particular projection is specified here by its constant ring datum and its
  canonical ordinary functors, so the general structure is not an additional binder.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; its existing scalar-extension construction
  `changeOfRings`, `changeOfRingsPresheaf`, `changeOfRingsHom` is used explicitly.

All modules of the recorded proof dependencies are also imported, without `public`:
module adjunction, independent-universe K-injective resolutions, KInjectiveTotalDerived,
RingedTopoiDerivedPullback, independent-coefficient K-flat resolutions,
ResolvingDerivedAdjunction and the upstream termwise/homotopy adjunction. No proof import
was omitted for a cycle.

Edge cases checked: zero modules and zero complexes, zero coefficient rings, the empty
site, identity structural maps, constant sequences, non-surjective transition maps and
nonflat A→B_n, and complexes unbounded in both directions. The limit property makes no
surjectivity claim about its projections, the tensor extension is derived, and all
transition inequalities including m=n are covered. Nothing requires a terminal object
of C, finite covers, exact ordinary pullback, or preservation of K-injectivity by F.

Searches run via the prescribed msearch wrapper:

1. LeanFinder, `Derived adjunction for a ringed inverse sequence projection with K-flat
   coefficient reduction`: 8 hits, all general Mathlib derived adjunction operations
   (`CategoryTheory.Adjunction.derived`, `derived'`, units and counits); no ringed-sequence
   specialization, limit model, or simultaneous tensor comparison.
2. Loogle, `SheafOfModules, CategoryTheory.Adjunction`: 8 ordinary sheaf adjunctions,
   including pullbackPushforwardAdjunction and sheafificationAdjunction. These do not
   state the derived theorem.
3. Mathlib grep, `sequence.*[Aa]djoint|[Ss]equence[Pp]rojection|[Ss]ystem[Pp]ullback`:
   4 generic adjoint-functor-theorem comment hits, no sequence projection statement.
4. Local rg on both `lean/WeilConjectures` and `lean/Sheaf` for sequenceProjection,
   systemPullback, sequence adjunction and the exact node id: related specialized
   coefficient constructions and exchange theorems only, no exact declaration.
   Exact node-id search in `dag/lean_names_upstream.json` and WeilConjectures found none.
5. Local generator search found systemModelTmul (requires a supplied derived scalar
   model), StrictScalarHomChain.tensorSection (R-linear tensor of a complex), and
   scalarExtensionRingIsoTmul (the separate mixed-universe extension construction).
   Here tensorSection simply exposes the pure tensor of the already used changeOfRings
   construction, with no new tensor object or scalar-extension functor.

No statement dispute, correction, new independent notion or unusable statement dependency
was found. The historical example `CompactObject.lean` is withdrawn; its node now points
to the existing Mathlib compact-object declaration, so it was read as such rather than
copied as a declaration template.

Validation: prescribed scompile.py compiled both the sandbox name and the actual library
module name without errors or warnings (13.0 s and 11.8 s). The first attempt diagnosed
scalar-action inference losing the module structure after unfolding to the underlying
sheaf; explicit `SMul.smul` source and target types repaired that without changing any
mathematical condition.

## Second reading by NA

The dispatcher forbids starting another agent and assigns independent delivery review to
the maintainer. This section records a second in-thread reading, not a claim of an
independent agent review. I reread the item statement and the final file together.

The compatible structural maps are exactly the natural transformation from the constant
A-diagram. The system category is the recorded one, with n encoding the positive index
n+1. In the transition equation, the left side moves from level n to m, and the right
side sends b by B_n→B_m, in the correct inverse-sequence direction. In the limit equation,
π_m is transition composed with π_n; projection naturality is F(f) then π'_n equals π_n
then f_n after scalar restriction. Every compatible cone is tested, so the direct image
is the genuine limit with its A-action. The ordinary transpose uses homEquiv.symm, since
h starts on the right-adjoint side; the derived normalization uses homEquiv, since f
starts on the left-adjoint side. Both orientations match the node. The scalar-first
pure tensor is only the established symmetry convention. The representative comparison
has source L[P], target [GQ], and its equation determines the fraction [q] inverse in
exactly the required direction. ε is natural on all complexes and L is a derived
functor, so this comparison is natural after localization, not only on chosen resolution
maps. No added boundedness, flatness of coefficient maps, surjectivity or exactness of
ordinary pullback appears. The only changes needed by this reading were explicit scalar
action types, already compiled successfully. All declarations are public, all universes
are bound, and the node record's main signature is copied verbatim from the module.
