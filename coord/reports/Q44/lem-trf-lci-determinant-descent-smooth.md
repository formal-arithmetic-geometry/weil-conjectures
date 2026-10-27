## Worker report

The delivery states `AlgebraicGeometry.LciDeterminantDescent.exists_lciDeterminantDescentSmooth`
in `Sheaf.AlgebraicGeometry.LciDeterminantDescentSmooth`. The sole postponed proof is this
named theorem. Its docstring carries all six accepted DAG proof steps and their sources.
All definitions contain actual data. No mathematical statement, dependency list, dependency
record, or other existing node field is changed; the item's only change is its `lean` record.

The input and output structures unpack this node's presentations and comparison equations.
They introduce no replacement cotangent complex, determinant functor, module pullback,
exterior power, dual, local-freeness predicate, or invertibility predicate. Their named
constructors and maps are listed in `lean.declarations`.

Hypothesis-by-hypothesis reading:

- A morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`. Both schemes are arbitrary.
- The integer `d ≥ 0` is `(d : ℕ)`.
- The cover is `cover : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (Presentation f d U)`.
  This pointwise description of an open cover allows any size of covering and the empty
  covering of the empty scheme.
- A presentation `U → P → S` is `Presentation.i`, `.p`, and `.factor`. Its `.lci` is the
  dependency's `CotangentPresentation.LciPresentation`, not a new notion of lci immersion.
  The existing `.closed`, `.ambient`, `.open_immersion`, and `.structure_map` fields say
  exactly that `i` is closed and `P` is open in relative affine n-space over S.
- `Presentation.c` and `.rank_eq : lci.dimension = c + d` express `c = n - d` without
  truncated natural subtraction accidentally admitting `n < d`.
- `Presentation.length` explicitly supplies, near every source point, `Fin c` ideal
  generators which satisfy `RingTheory.Sequence.IsKoszulRegular`. The generic `.lci.koszul`
  witness is the same condition with the finite length forgotten, already implied by this
  stronger specified-length witness; it is retained to use the recorded lci interface.
- The assumption on `I/I²` is `.conormal_free`. Its object is the existing
  `CotangentPresentation.conormalTerm i = (tensorPullback i).obj i.ker.toModules`.
- `V` is exactly `CotangentPresentation.ambientDifferentials i p`, the recorded tensor
  pullback of `p.relativeDifferentials`. The `differential` definition is transported from
  the dependency's conormal model by its specified negative and zero identifications.
  That model's defining formula sends the class of an ideal section to its derivative.
- The complex `E` is `model ... C hV`, an existing `TwoTermDeterminantModel` with the actual
  conormal and ambient terms in degrees -1 and 0. Only the positive rank witness is an
  output. `Realization.comparison`, `.negative`, and `.zero` fix its chain identification
  with the dependency's conormal complex on both nonzero terms.
- `Presentation.line` is `(dual (exteriorSheaf C_i c)) ⊗ exteriorSheaf V_i n`.
  The imported scheme `dual` is the abbreviation for the recorded sheaf Hom into the
  structure sheaf, not a categorical choice of dual object.
- The intrinsic complex is always `CotangentPresentation.cotangent (D.model f)`.
  `D`, `F`, `κ`, `E`, and `hD : CotangentPresentation.Properties D F κ E` are the existing
  construction/comparison data supplied by the dependency's existence theorem. The ring
  and scheme `HasDerivedCategory` binders select presentations of derived categories, not
  geometric restrictions on f. The slice category binders are required by `Scheme.IsPerfect`.
- `Realization.lambda` is not an arbitrary derived isomorphism: it composes the fixed
  chain bridge, the recorded `E.identification ... .iso`, and the inverse of the canonical
  cotangent restriction arrow `D.square ...` / `derivedChange`.
- `T : TwoTermPerfectDeterminantData` and `hT : T.IsCanonical` use the CURRENT recorded
  determinant declaration, `exists_canonicalTwoTermPerfectDeterminantData`, not its retired
  unconstrained-model predecessor. Its `.model` clause is the signed exact-cone expression
  for det of a chain quasi-isomorphism, with sign `(-1)^(a*(b+1))`; on degreewise surjective
  maps this is the kernel-first contraction `T_a` from the recorded surjective determinant
  calculus, in dual-first order after ordinary tensor symmetry. Its `.pullback` clause
  fixes model restrictions by pure exterior wedges and the original K-flat counit.
  These specify the affine-local normalization requested by the item. They cover finite
  projectives with varying ranks by their constant-rank open loci. No new normalization
  hypothesis involving a chosen adjunction or the theorem's conclusion is used.

Conclusion-by-conclusion reading:

- The existential `hL` gives the dependency's local two-term condition globally.
  `Descent.perfect` explicitly asserts `Scheme.IsPerfect X L`; `.tor` states the vanishing
  of the homology of `L ⊗ M[0]` for every module and integer outside [-1,0], with the recorded
  `tensorModule`, not an alternative tensor structure.
- The line D is `twoTermDeterminantValue (T.functor X) L hL` and `.invertible` uses
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `.chart` supplies a realization for EVERY polynomial presentation satisfying the input,
  not only a selected member of the cover. Its `.ambient_free` gives rank n; the conormal
  rank c is the hypothesis already held by that presentation.
- `Realization.alpha` is precisely `(modelIso)⁻¹`, then `det(lambda)`, then the inverse
  determinant pullback comparison. Its codomain is the actual restriction of D.
- `alphaOn` restricts this map to an arbitrary smaller open using the section-normalized
  tensor-pullback composition comparison. `transition` is `alphaOn_i ≪≫ alphaOn_j.symm`.
  Thus its endpoints can be different local model lines; no false equality of the objects
  coming from different presentations is asserted.
- `Descent.identity` is `t_ii = 1`; `.cocycle` is `t_ij ≪≫ t_jk = t_ik` on EVERY common open.
  Quantification over all presentations makes the latter also the precise independence
  under inserting any third presentation. It includes different presentation dimensions.
- `.refinement` is the equality between restriction of a transition and the transition
  computed on a smaller common open, with the necessary canonical composition isomorphisms
  `restrictionComp` on the two ends. It includes any sequence of refinements by iteration.
- `.presentation_restriction` additionally identifies the comparisons for an actually
  restricted polynomial presentation: for a Cartesian restriction of the closed immersion
  along an ambient open immersion, it supplies the dependency's `ConormalChange` and asserts
  `IsFlatLCIPullbackDeterminantComparison` for the induced line map. That existing predicate
  includes invertibility of the two term maps and their pure dual-wedge normalization.
  `conormalMap` and `ambientMap` just transport its already normalized component maps.
- No field asks for separatedness, quasiseparatedness, Noetherianity, flatness of f,
  affineness of the source or target, or affineness of any overlap.
- `.smooth` ranges over ALL open U with `Smooth (U.ι ≫ f)`. Its `SmoothComparison.rank`
  states rank d for the ACTUAL `(U.ι ≫ f).relativeDifferentials`, without assuming relative
  dimension d as an input.
- `SmoothComparison.beta` is the explicit determinant of the canonical smooth augmentation:
  determinant restriction, determinant of the canonical intrinsic restriction followed by
  `D.augmentation`, the inverse single-complex comparison, the degree-zero model comparison,
  and `SmoothComparison.exterior`. The chain comparison is pinned in degree zero, and the
  exterior comparison is pinned by evaluation on the empty negative wedge. There is no
  unspecified scalar in beta.
- `.source_differential` supplies the ambient-to-source differential map with the formula
  `d r ↦ d(i^*r)`. This prevents the smooth normalization from quantifying only over an
  uninhabited class of maps. `IsSourceDifferential` is the formula defining that canonical
  helper, not an independent new mathematical object.
- `.relation_first` expands to the complete section equation: the composite beta alpha
  sends the dual of the wedge of the c relation sections, tensored with the wedge of their
  differentials FIRST and d quotient lifts SECOND, to the quotient wedge. The tuple uses
  `Fin.append` and the explicit `rank_eq` cast. The empty negative wedge is normalized to 1.
  There is no unrecorded sign or reversed block order. It is stated on every open, so in
  particular on all affine frames used in the proof.
- `.smooth_restriction` constructs the canonical differential restriction map and the
  induced top-exterior isomorphism, fixes both on universal derivations/pure wedges, and
  asserts the commuting square for beta and determinant restriction. This also implies
  agreement on overlapping smooth opens after restricting both to their intersection.
- `.smooth_overlap` gives the actual equation `(beta alpha_j) t_ij = beta alpha_i` on an
  arbitrary common smooth open of two presentation domains.

Dependency declarations read and used:

- `lem-trf-lci-cotangent-presentation`: `Sheaf.AlgebraicGeometry.LciCotangentPresentation`,
  `CotangentPresentation.System`, `AffineIdentifications`, `LciIdentifications`, `Properties`,
  `exists_lciCotangentPresentation`, `cotangent`, `conormalTerm`, `ambientDifferentials`,
  `LciPresentation`, `ConormalModel`, `ConormalChange`, `derivedChange`, and `BaseSquare`.
- `lem-trf-two-term-perfect-determinant`:
  `Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant`,
  `TwoTermPerfectDeterminantData.IsCanonical` and
  `exists_canonicalTwoTermPerfectDeterminantData`. The imported existing data module provides
  `isTwoTermPerfect`, `TwoTermDeterminantModel`, `twoTermDeterminantValue`, and
  `twoTermDeterminantIso`; these definitions are reused verbatim.
- `lem-trf-surjective-two-term-determinant-calculus`:
  `Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus`,
  `Module.IsKernelNormalizedDeterminantMap`, `Module.kernelNormalizedDeterminantMap`, and
  `Module.surjective_two_term_determinant_calculus`, read to check the kernel-first sign
  and the determinant interface's normalization. The map formula itself is encoded by the
  existing canonical determinant interface, not by a new duplicate determinant construction.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionComp`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `.Hom`.
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`; the scheme abbreviation `dual` is read in
  `WeilConjectures.AlgebraicGeometry.Modules.Dual`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `Scheme.Modules.IsInvertible`.
- `def-sc-relative-differential-sheaf`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials` and `.relativeDifferentialsDerivation`.
- `def-sc-sheaf-exterior-power`: `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`,
  `Scheme.Modules.exteriorSheaf` and `.exteriorSheafSection`.
- `def-amb-finite-locally-free-module`:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `IsClosedImmersion`, via `LciPresentation.closed`.
- `def-weil-pbc-koszul-regular-sequence`: `WeilConjectures.RingTheory.KoszulRegularSequence`,
  `RingTheory.Sequence.IsKoszulRegular`.
- The additional proof-only imports are the recorded smooth relative differential theorem,
  affine determinant theorem, polynomial differential basis and differential localization.
  The full node proof and its elementary cancellation steps are in the theorem docstring.

Edge cases checked before and during the separate reading pass:

- Empty X: cover is vacuous; perfect/Tor assertions and ranks on the empty module category
  are valid; no Nonempty X or nonempty index-type binder was introduced.
- c=0, d=0, n=0: the formulas use `Fin 0` and the actual zeroth exterior power. The smooth
  exterior comparison explicitly evaluates on the empty wedge, rather than discarding it.
- Nonaffine and nonseparated intersections: W is an arbitrary `X.Opens` everywhere, and
  refinement uses morphisms of schemes of opens, never coordinate rings of intersections.
- Zero rings and all characteristics: no domain, field, nontriviality, or characteristic
  hypothesis. Pure-wedge equations have no division.
- Different ambient dimensions: transitions and cocycles quantify over independent
  presentations; only genuine restriction of a fixed ambient dimension has equal-rank
  witnesses in `.presentation_restriction`.
- Smooth opens may be empty or the whole X. All smaller-open comparisons include equal
  opens, so identity restrictions are retained.
- Source and coefficient universes are explicit. Slice derived-category witnesses use the
  same localization universe w as the existing perfect-complex interface.

Searches for an existing statement (2026-10-24):

1. `msearch.py Q44 lem-trf-lci-determinant-descent-smooth leanfinder` with query
   "Determinant line of local complete intersection cotangent complex descends conormal
   determinants and equals top differentials on smooth opens": eight hits, including
   `Algebra.smoothLocus_eq_compl_support_inter`, generator conormal/localization comparisons,
   standard smooth bases and `Algebra.Extension.cotangentComplex_mk`; no determinant descent.
2. `msearch.py ... loogle '"cotangentComplex", "det"'`: zero hits.
3. `msearch.py ... grep 'cotangent.*determinant|determinant.*cotangent|det.*cotangentComplex'`:
   zero Mathlib hits.
4. `msearch.py ... leansearch` with query "The determinant of the cotangent complex of a
   local complete intersection glues conormal determinant lines and equals top differentials
   on smooth opens": eight hits on ordinary conormal complexes, Jacobians and differentials;
   none state the item.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, lci determinant descent,
   determinant/cotangent and smooth/descent patterns: no existing declaration for this node.
   Read `AdjunctionCotangentDeterminantNormalization`: it is a different adjunction comparison,
   assumes a flat finitely presented pure-dimensional family over a Noetherian base, uses
   regular presentations, and has no complete smooth normalization/descent statement here.
   It cannot supply this general Koszul-regular statement. Its canonical comparison pattern
   and the existing normalized determinant interface are reused conceptually, without copying
   its more restrictive presentation predicate.
6. Searched `dag/lean_names_upstream.json` for cotangent/determinant combinations; no binding
   for this descent and smooth-normalization statement.

Sources opened locally: `perfect.tex` lemma-determinant-two-term-complexes and
remark-functorial-det (0FJX/0FJY); `cotangent.tex`
proposition-cotangent-complex-local-complete-intersection (08SL) and lemma-when-projective
(08R5); `morphisms.tex` lemma-smooth-omega-finite-locally-free (02G1). Also read the recorded
kernel-normalized map's full definition/docstring to check the relation-first order.
No node faults or STATEMENT-DISPUTED claims remain.

## Second reading by Q44

A separate complete reading pass was performed by this same dispatcher worker; no second
agent was started, as the task-specific brief explicitly forbids it. The maintainer's
independent delivery review remains separate.

This pass compared the original node statement with each input/output field above and
checked the maps' source and target, rather than merely inspecting the theorem name.
It caught three omissions in the first draft: actual polynomial-presentation restrictions
were not yet identified with pure-wedge pullback; beta's compatibility under smaller smooth
opens was only described in the docstring; and the canonical source differential's existence
was implicit in a universal quantification. These are now respectively
`presentation_restriction`, `smooth_restriction`, and `source_differential`. The pass also
checked that `lambda`, `alpha`, and `beta` are real composites of the dependency's maps and
that the single-complex and empty-wedge comparisons cannot absorb an arbitrary scalar.
The ambient rank is concluded, the conormal rank is assumed, and smooth relative dimension
is not assumed. No extra geometric hypothesis was introduced. The canonical determinant
predicate comes from the dependency's repaired current record, not the unconstrained record
criticized by the item's stage-1 review. The item and every auxiliary declaration have the
same blueprint tag and a source docstring. No new nodes or dependency modules are needed.

## Validation

All compilation uses the prescribed `scompile.py` against the live published project.
The first compile diagnosed the slice-derived-category instances required by `IsPerfect`;
these representation binders were added. The next compile accepted sandbox and library
forms with one 101-character line warning; that line was split. The final `scompile.py` run accepted both sandbox and library forms, with no errors
and no warnings (56.2 s and 33.7 s). The required `deliver2.py --no-push` then
printed OK: its commit passed server preflight and per-file compilation. The checked
packet has exactly the module, the item node, and this report.
