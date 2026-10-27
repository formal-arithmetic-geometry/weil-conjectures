## Worker report

Stage 2, group NL, item `lem-sfb-log-canonical-deletion-algebra`, 2026-10-22.

The delivery states `AlgebraicGeometry.exists_logCanonicalDeletionAlgebra` in
`Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra`. Its only postponed proof is
that named theorem, with the complete twelve-step DAG proof plan in its docstring.
All auxiliary definitions have actual data and source/blueprint docstrings. They
unpack clauses of this same theorem; they introduce no independent prerequisite.
No theorem is proved, no additional axiom is introduced, and the natural-language
statement, proof and proof dependencies are unchanged.

This repairs H12 on immutable head `6afca2eae2bc`. The initial required dry run
of the saved packet passed at `c3ade0e88b0`; that packet still contained the node
which the maintainer rejected at landing. The correction below follows the
maintainer's explicit instructions, rather than re-pushing that packet.

The normalized dualizing line is existentially supplied before an implication
whose premise is the component-degree assumptions. This makes those assumptions
refer to the very same canonical line constructed in the first clause; the
fundamental-class-preserving uniqueness clause makes the choice immaterial.
There is no assumed dualizing construction or contraction in the hypotheses.

The phrase 'finite presentation' uses locally finite presentation together with
the supplied properness, or with the resulting closed projective-bundle embedding.
Properness supplies quasi-compactness and quasi-separatedness on the input;
the finite locally free degree-one module and its projective-bundle embedding
supply these on the output. The ambient bundle is the canonical relative Proj of
the symmetric algebra, not a finite projective space over the whole base.

### Hypotheses, one by one

| Node hypothesis | Lean rendering |
| --- | --- |
| Any schemes Y and T, with pi:Y->T | `{Y T : Scheme.{u}} (f : Y ⟶ T)`; no Noetherian, reduced, normal, affine or integral base assumption |
| Proper | `[IsProper f]` |
| Flat | `[Flat f]` |
| Finitely presented | `[LocallyOfFinitePresentation f]`, with quasi-compactness and quasi-separatedness from properness |
| Nonempty connected nodal geometric fibres | `hnodal : HasNodalGeometricFibres f`; its `ConnectedSpace` includes nonemptiness |
| Reduced geometric fibres of pure dimension one | First two conjuncts of `hfibres`, for every algebraically closed `Ω : Type u` and every `t : Spec (.of Ω) ⟶ T` |
| Arithmetic genus g>=2 | `g : ℕ`, `hg : 2 ≤ g`, and the final conjunct of `hfibres`, using `@Scheme.arithmeticGenus Ω _ (pullback f t) ⟨pullback.snd f t⟩ = g` |
| r>=0 labelled sections | `r : ℕ`, `a : Fin r → (T ⟶ Y)`, `ha : ∀ i, a i ≫ f = 𝟙 T` |
| Pairwise disjoint | `hdisjoint`, pairwise disjoint ranges of the individual `a i` |
| Relative smooth locus | `hsmooth : ∀ i, Set.range (a i) ⊆ (f.smoothLocus : Set Y)` |
| All normalized component log degrees nonnegative | First conjunct of `NodalDeletionNumerics f a ha (nodalDeletionLine a omega)` |
| At most one component of degree zero in each geometric fibre | `Set.Subsingleton {Z | nodalDeletionDegree f L Ω t Z = 0}` inside that predicate |
| A degree-zero component is smooth rational | `Smooth` of its actual reduced-component inclusion followed by the fibre structure map, and `normalizedComponentGenus ... Z = 0`; over an algebraically closed field a smooth proper genus-zero curve is rational |
| Exactly two special points | `encard = 2` of the inverse image, on the canonical component normalization, of the union of nonsmooth points and the base-changed labelled markings |

### Conclusions, clause by clause

| Node conclusion | Lean rendering |
| --- | --- |
| D is the effective Cartier sum of markings | `nodalDeletionMarking a := Sigma.desc a` is the actual finite disjoint-union map, and the theorem asserts `IsEffectiveCartierCenter` of that map. Its kernel is the ideal of their union, equal to their product because the sections are disjoint. This defines the effective sum with multiplicity one. |
| O(D) is the associated invertible module | `(nodalDeletionMarking a).ker.toModulesᵛ`, using the recorded Cartier-ideal dual, in `nodalDeletionLine`; invertibility follows from the asserted effective Cartier center. |
| Canonical relative dualizing invertible module with adjunction normalization | `∃ (omega : Y.Modules) (d : NodalDualizingDatum f omega)`. The datum includes invertibility, the fundamental class, regular-presentation coverage, every Jacobian normalization, and the actual local sheaf Ext. The next clause is unique isomorphism to every such datum preserving that fundamental class. |
| Arbitrary base change of the dualizing line and log twist | For every `T'` and `u : T' ⟶ T`, a datum on the literal tensor pullback of `omega`, with equality on all pulled-back differential generators, and a comparison between the pulled-back log line and the actual base-changed marking twist. |
| L=omega tensor O(D) is invertible | `nodalDeletionLine a omega` is that actual tensor product, with explicit `IsInvertible` in the conclusion. |
| Degree 2g(V)-2+b_V+m_V | The degree equality quantifies over every geometric point and every canonical irreducible component `Z`. `nodalDeletionDegree` is the existing cohomological degree on its canonical normalization, with the induced Ω-structure. The right side uses the recorded normalized genus, then separately the `ncard` of nodal branches and of marking preimages. |
| For every m>=2 the direct image is finite locally free | First conjunct under the numerical implication, `∀ m, 2 ≤ m → ...IsFiniteLocallyFree`. |
| Its formation commutes with arbitrary base change | `IsIso` of the existing `Scheme.Modules.moduleBaseChangeMap` for the actual pullback square and the actual tensor power. This is not an unspecified isomorphism between modules. |
| Cubic evaluation is surjective | `Epi` of the counit of `tensorPullbackSectionAdjunction f` at the log cubic. This is the section-normalized evaluation map; epimorphism in sheaves of modules means stalkwise surjectivity. |
| The cubic section algebra with section multiplication | `A : RelativeSectionAlgebra f (L.tensorPow 3)` fixes every affine homogeneous section, coefficient action, unit, multiplication and restriction. The additional `G : GradedSheafAlgebra ...` records the same algebra on the actual direct-image sheaves, with its unit and multiplication fixed on every open by section pullback and `tmulSection`. |
| A_j=pi_* L^(3j), including j=0 | The interface uses `(L.tensorPow 3).tensorPow j`. The existing `L.tensorPowMulIso 3 j` identifies this canonically with `L.tensorPow (3*j)`, including degree zero. This is only the canonical parenthesization of tensor powers. |
| Generated by its finite locally free degree-one part | On every affine `V`, `Algebra.adjoin Γ(T,V) (A.data.grading V 1) = ⊤`. For these quasi-coherent homogeneous pieces this is equivalent to degree-one generation as a sheaf algebra. Degree-one finite local freeness is the m=3 case above. |
| Evaluation defines q into X=Proj_T A | `q : Y ⟶ A.data.relProj`, `hq : q ≫ A.data.relProjHom = f`, and `A.IsCanonicalMap q`. The existing predicate fixes evaluation on every trivializing open by the homogeneous section/fraction formula, including degree zero. |
| X/T flat and finitely presented | `Flat A.data.relProjHom`, `LocallyOfFinitePresentation A.data.relProjHom`, and the closed projective-bundle embedding specified below. |
| Closed immersion into P_T(pi_* L^3), hence projective | `NodalDeletionProjectiveEmbedding` uses the canonical symmetric graded algebra of exactly this direct image. The map `phi` is fixed on every degree-one generator by `A.sectionEquiv` and the canonical right-unitor for M^1. Its surjectivity gives the specified `relProjMap`, asserted a closed immersion. The existing `relProjMap_relProjHom` supplies its equation over T. Thus the embedding is the one induced by evaluation, not an unrelated immersion. |
| Connected nodal genus-g geometric fibres and disjoint smooth stable markings | `IsStablePointedCurve A.data.relProjHom (fun i ↦ a i ≫ q) ...` uses the recorded definition, including projective-bundle projectivity, flatness, finite presentation, connected nonempty nodal reduced pure-one-dimensional fibres, disjoint smooth markings and the normalized-component stability inequalities. A separate universal geometric arithmetic-genus equality states genus g. |
| q contracts precisely the zero-degree component and is an isomorphism away from it | `NodalDeletionContracts`: on each geometric fibre a zero-degree reduced component maps scheme-theoretically to a rational point, and its complementary open is isomorphic to the complement of that point in the target, with the isomorphism induced by the actual fibre map. |
| No zero component in a fibre | The final conjunct of `NodalDeletionContracts` requires the whole fibre map to be an isomorphism; this case is explicit, not a vacuous exceptional-component implication. |
| If no fibre has a zero component, q itself is an isomorphism | The quantified nonzero-degree premise implies `IsIso q`, over the original arbitrary base. |
| Construction, including q, commutes with arbitrary base change | `NodalDeletionBaseChange` supplies the section algebra of the literal pulled-back cubic and a `PullbackData` whose maps on every homogeneous section are the explicitly constructed `nodalDeletionBaseChangeSection`. The existing relative-Proj comparison is cartesian; the stated evaluation square is `q' ≫ b.relProjComparison = pullback.fst f u ≫ q`. The normalized dualizing/log comparison above identifies this pulled-back cubic with that of the new marked family. |
| Functoriality for isomorphisms preserving every marking | `NodalDeletionDualizingIsomorphisms` gives the normalized fundamental-class and actual marking-twist comparisons. `NodalDeletionIsomorphisms` gives the section-normalized graded algebra isomorphism and the Proj/evaluation square. Its premise is `∀ i, a' i ≫ e.hom = a i`, preserving each label. Base isomorphisms are covered by arbitrary base change followed by these relative isomorphisms. |
| Unique up to unique isomorphism commuting with q among the stated competitors | The last universal clause takes an arbitrary stable labelled family `(Z,p,b,hb)`, a map `c : Y ⟶ Z` over T with `∀ i, a i ≫ c = b i`, and precisely the same `NodalDeletionContracts` predicate. It concludes `∃! e : A.data.relProj ≅ Z, q ≫ e.hom = c ∧ e.hom ≫ p = A.data.relProjHom`. The marking equations then force the isomorphism to preserve each label. |

### Dependency declarations read and used

All original statement dependencies were opened, including their recorded signatures
and docstrings. No dependency interface was replaced or copied.

| Module | Declarations |
| --- | --- |
| `Mathlib.AlgebraicGeometry.Scheme` | `AlgebraicGeometry.Scheme`, its morphisms |
| `Mathlib.AlgebraicGeometry.Morphisms.Proper` | `IsProper`, its separatedness and compactness consequences |
| `Mathlib.AlgebraicGeometry.Morphisms.Flat` | `Flat` |
| `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` | `LocallyOfFinitePresentation` |
| `Sheaf.AlgebraicGeometry.NodalGeometricFibres` | `HasNodalGeometricFibres` |
| `WeilConjectures.AlgebraicGeometry.EffectiveCartier` | `Scheme.Modules.dual`, `IdealSheafData.toModules`, the associated Cartier-line convention and invertibility theorem |
| `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier` | `IsEffectiveCartierCenter` |
| `Sheaf.AlgebraicGeometry.NodalDualizingDatum` | `NodalDualizingDatum`, its normalized fundamental class and local Ext fields |
| `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | `Scheme.arithmeticGenus`, `Scheme.Modules.degree` |
| `Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees` | `markedNodalComponentDegree`, specialized by `nodalDeletionDegree`; owner `def-sfb-marked-nodal-dualizing-degree-data` |
| `Sheaf.AlgebraicGeometry.ReducedNormalization` | `Scheme.reducedNormalizationComponent` and its integral instance; its canonical normalization is used through `normalizedComponentMap` |
| `WeilConjectures.AlgebraicGeometry.GradedSheafStructures` | `GradedSheafAlgebra` |
| `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` | `Scheme.GradedAlgebraData`, `relProj`, `relProjHom` |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism` | `IsProjectiveBundle` via the recorded stable-curve definition; canonical `SymmetricAlgebraSheaf.gradedAlgebraData` for the embedding |
| `Sheaf.AlgebraicGeometry.StablePointedCurve` | `IsStablePointedCurve`, `Scheme.normalizedComponentMap`, `Scheme.normalizedComponentGenus` |
| `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion` | `Scheme.Modules.RelativeSectionAlgebra`, `IsCanonicalMap`; definition owner `def-sfb-relative-section-algebra-canonical-map` |
| `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction` | `Scheme.Modules.moduleBaseChangeMap`; constructed from `lem-pc-module-pullback-adjunction` and `def-pc-module-pullback` |
| `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction` | `Scheme.Modules.exists_tensorPullbackAdjunction`; owner `lem-pc-module-pullback-adjunction` |
| `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` | `Scheme.Modules.tensorPullbackSection`, `tensorPullbackSectionAdjunction`; the existing tensor pullback functor is retained |
| `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange` | `PullbackData`, `relProjComparison`, its cartesian comparison theorem |
| `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality` | `relProjIsoOfIso`, `relProjMap`, `irrelevantLE_of_surjective` and the structural-map equation |

The statement dependencies now cite the existing construction owners:
`def-sfb-relative-section-algebra-canonical-map` (landed Q06),
`lem-pc-module-pullback-adjunction`,
`def-pc-module-pullback`, and `def-sfb-marked-nodal-dualizing-degree-data`.
The theorem nodes `lem-trf-scheme-ample-canonical-proj-criterion` and
`lem-weil-pbc-module-base-change-map-open-restriction` have been removed from the
earlier packet's added `stmt_deps`: neither theorem conclusion is used.
The canonical base-change map is built
from the section-normalized adjunction `exists_tensorPullbackAdjunction`, using
`Classical.choose` on its normalization statement, as in the landed
`lem-weil-pbc-module-base-change-map-pasting`. Their
unchanged published modules remain the defining modules of the real constructions.
No theorem or theorem-selected object is newly assumed by this ownership repair.
The remaining public imports are the existing statement constructions.
Already stated proof dependencies are imported privately.
The four unstated nodal-dualizing/field-linear-series/contraction-direct-image/
relative-image prerequisites and the unstated pinching and closed-union inputs
remain in the DAG proof plan; stage 2 does not assume their conclusions.

### Sources and edge cases

The node and Q64 stage-1 report were read in full. The Brown primary-author URL
still timed out, but the publisher's primary scan was obtained in the sandbox:
[Knudsen II, publisher PDF](https://journals.msp.org/mscand/article/download/1622/1621/1653).
Printed pp. 171--175 were inspected as rendered images: pp. 171--172 contain the
linear-series proof, p. 173 gives Corollaries 1.9--1.11, and p. 174 gives the section
algebra, the symmetric-algebra cubic embedding and the uniqueness argument in
Proposition 2.1. The source's proposition starts with an (r+1)-pointed stable family
and deletes the last marking. As already recorded in the DAG and Q64 split,
this node formulates the more general single-zero-component result; the existing
proof plan constructs the field quotient by pinching and then spreads the image,
without assuming a globally chosen extra marking. The module preserves that exact
node statement rather than silently specializing it to the source's initial data.
The Stacks prestable/stable curve and rational-tail/bridge source text was also
consulted. No source or unit statement was changed.

Edge checks were performed before fixing the signature. `r=0` gives the empty
coproduct and its unit kernel ideal, so D=0 and L=omega. There is no excluded empty
index set. Empty T has no geometric tests; its marking, line, Proj and uniqueness
claims have their ordinary empty-scheme interpretations. A rational tail contributes
one node branch and one marking; a rational bridge contributes two branches and
no marking. A self-node contributes two distinct normalization preimages. Its
component is not smooth, so it cannot be an exceptional component under the stated
smoothness premise. A bridge whose attachments lie on the same remaining component
is allowed and can produce a self-node in the stable quotient. With no exceptional
component the whole fibre map and, universally, q are required to be isomorphisms.
Arbitrary base change includes the identity, empty base and nonflat maps; it is not
restricted to geometric points. Nonreduced and non-Noetherian bases remain allowed.
The uniqueness comparison explicitly preserves labels, preventing relabelling from
being treated as the same competitor. All variables and the universe `u` are bound
explicitly; geometric tests use the same size convention as the recorded nodal and
stable-pointed interfaces.

### Searches

Actual `msearch.py` calls and their outputs are retained in `searches.jsonl`.

- LeanFinder: `logarithmic canonical section algebra stabilization nodal pointed curve contraction degree zero component`; 8 hits on Weierstrass coordinates/minimality and rational maps, no matching contraction theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.degree, AlgebraicGeometry.IsStablePointedCurve`; 0 hits, reporting that the project-specific degree identifier is unknown to its Mathlib index. The project sources were read directly instead.
- Mathlib grep in `AlgebraicGeometry`: `log.*[Cc]anonical|[Ll]og.*[Cc]ontract|[Ss]tabiliz`; 13 hits, on Noetherian stabilization and site material, not this theorem.
- LeanSearch: `log canonical section algebra nodal pointed curve contraction relative Proj`; 8 hits, including `Proj.fromOfGlobalSections` and ordinary Proj charts, not the nodal contraction theorem.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for `logCanonical|LogCanonical|log_canonical|deletionAlgebra|DeletionAlgebra|lem-sfb-log-canonical-deletion-algebra`: only the already recorded locally Noetherian positive-degree reconstruction family was found, not this arbitrary-base nonnegative-degree result.
- The required upstream item-id text search has no match. Searches for section-algebra, base-change-map and relative-Proj interfaces found the existing declarations listed above, which are reused.

No `STATEMENT-DISPUTED` flag or source-based statement correction is needed.
The helper predicates are explicit unpackings of this item's own clauses, not
new independently assumed notions. The JSON copy changes only `lean` and adds the
four existing construction-owner ids to `stmt_deps`.

## Advisory H4: live marked-nodal data

The live `def-sfb-marked-nodal-dualizing-degree-data` and its full defining source
were read after the rebase. `nodalDeletionDegree` now delegates to the existing
`markedNodalComponentDegree` on the canonical integral reduced component, with its
actual inclusion followed by the two fibre projections. This is the same
normalization, module pullback and structural field map as before, up to the
associativity of composition; it replaces the repeated degree construction.
The live definition owner is cited and its module is imported publicly.

`markedNodalLine` requires a bundled `MultipointedCurve T` P; its input includes
flatness, finite presentation, quasi-compactness, quasi-separatedness, pure fibre
dimensions for the curve and marking, and a closed marking immersion.
`nodalDeletionLine` is the unbundled specialization to the actual finite labelled
marking map `Sigma.desc a`; it is defined for any a before the theorem establishes
that this map is Cartier. Its body uses the very same ideal dual and sheaf tensor
operations as `markedNodalLine`, rather than a second dual, ideal or tensor
construction. Using the bundled function here would require an additional
construction and proofs of all the `MultipointedCurve` fields merely to express
this explicit term, including for arbitrary unbundled a. No such extra hypotheses
or data are introduced. On P with `P.i = Sigma.desc a`, both expressions are
literally `omega ⊗ₘ (Sigma.desc a).ker.toModulesᵛ`. The full
`MarkedNodalDualizingDegreesData` structure is not assumed: its canonicality,
base-change and degree fields are conclusions supplied by this theorem, and the
node's separate node-branch and marking counts remain explicit.

## Second reading by NL

Repair self-check by this worker (the maintainer supplies the independent reading):
the node and repaired module were reopened together. The arbitrary-base proper,
flat, finitely presented genus-g nodal family hypotheses, labelled smooth disjoint
sections with r=0 permitted, and every conclusion in the two tables above remain
unchanged. In particular the same canonical Cartier twist, normalized dualizing
fundamental class, canonical module base-change morphism, section-normalized
algebra and q, generator-pinned closed embedding, zero-component contraction,
no-exceptional-component isomorphism, both naturality squares and labelled unique
comparison are present. The degree helper uses the actual reduced component and
its canonical normalization, not a different numerical invariant.
The ordinary comparison map on a commutative square remains the existing
adjunction construction; no extra invertibility or theorem conclusion enters
the main statement. No new node is supplied. The current H12 defect is repaired
by removing the redundant owner node and citing the existing adjunction owner.
The H4 advisory is handled by the reuse and interface justification above.
There is no statement correction, no `STATEMENT-DISPUTED`, and exactly one `sorry`,
the named main theorem with its twelve-step proof docstring.

## H12 repair: existing adjunction ownership

The return's correction is applied in full:

- Removed the sandbox node `def-sfb-module-base-change-map` from the delivery.
- Replaced its single entry in the item's `stmt_deps` with the existing
  `lem-pc-module-pullback-adjunction`; retained `def-pc-module-pullback`.
- Kept the Lean module byte-for-byte unchanged. The base-change comparison is
  still the same canonical `Scheme.Modules.moduleBaseChangeMap`, whose source
  explicitly uses `Classical.choose (exists_tensorPullbackAdjunction ...)`.
- Removed the New nodes section and updated the owner table and dependency text.
  No maintainer-owned reachability field is added or changed.

The published adjunction declaration and its full normalization docstring were
reopened, together with the existing comparison-map definition and the landed
pasting node's dependency list. They confirm this ownership. The existing
`ModuleBaseChangeMapOpenRestriction` public import already exposes the adjunction,
so no Lean import or statement needs changing. The no-exceptional-component,
arbitrary-base-change and label-preserving uniqueness clauses were rechecked
against the item and remain exactly those previously accepted by the maintainer.
The node's natural-language statement and proof are unchanged. There are no new
nodes or dependency modules. The final packet contains only the item node,
the theorem module and this report.

### Validation

The initial saved-packet dry run passed at `c3ade0e88b0`, before this repair.
The prescribed `scompile.py` completed successfully for the unchanged module:
sandbox context 11.6 s; library context 13.2 s; no errors or unexpected warnings.
The repaired packet is dry-run again before delivery; its result is recorded below.

The repaired dry run printed `OK (dry run): commit 73f939f6341 passes the preflight
and compiles; nothing pushed`. Its staged packet contains exactly the report,
the item node and the unchanged theorem module; no new node is staged.
The delivery invocation repeats these checks before pushing.
