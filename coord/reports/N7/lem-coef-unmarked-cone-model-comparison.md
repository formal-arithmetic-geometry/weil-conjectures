## Worker report

Repair of the return at immutable head 492d775b60d0. The supplied sandbox contained
only dispatcher marker files, with no retained node, Lean module or report. The current
shared node also had no `lean` record. This packet supplies all three, using the current
node verbatim except for its new `lean` record and one added landed construction dependency.
The delivery wrapper rebases the packet on current newtargets-dag. No direct Git command
or edit was made in either read-only checkout.

The module is `Sheaf.AlgebraicTopology.UnmarkedConeModelComparison`, and its theorem is
`SSet.OrdinaryConeModel.unmarked_cone_model_comparison`. The only postponed proof is
that theorem. Its docstring contains all seven DAG proof steps and their named inputs.
The theorem has a literal `by sorry` proof; all six construction abbreviations/definitions
have actual data and no theorem witness is chosen for subsequent definitions.
`Data` is an existential presentation of the specified canonical constructions, not an
assumption or an arbitrary comparison: the theorem produces it together with the claims.

Clause-by-clause reading of the unchanged natural-language statement:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small ordinary category C, in the fixed universe | `C : Cat.{u,u}`; its object and arrow types are U-small. There is no nonempty, finite, discrete-category, or local-Kan hypothesis on C. |
| B=N(C), S=B opposite | `nerve C`, `(nerve C).op`; `Over.post opFunctor` is the existing opposite map on slices. |
| Any simplicial map p:X->B | `X : Over (nerve C)`; `X.left` is X and `X.hom` is p. No fibration or Kan condition on X is imposed. |
| Strict Kan-valued diagram D:C->Kan_U | `D : C ⥤ SSet.{u}` with `∀ c : C, KanComplex (D.obj c)`. This is the full category of Kan-valued ordinary functors; natural maps are arbitrary strict natural transformations. |
| D opposite is valuewise, with indexing C unchanged | `Data.strictOp` has domain `C ⥤ SSet`; `strictOp_objects` gives `(D.obj c).op`, `strictOp_action` gives the entire degree-n action `(x,f) ↦ (D.map f).op x`, and `strictOp_maps` gives `(a.app c).op`. Thus positive-dimensional mapping simplices and maps of diagrams are fixed too. |
| A=C[S] opposite | `Index C := oppositeCategory (rigidification.obj (nerve C).op)`. |
| A canonically identifies with C[B] by ordered reversal | `Data.reversal : SimplicialRightFibration.CoherentReversal (nerve C)`. Its existing simplex/path/naturality fields specify the reversal C[B opposite] ≅ C[B] opposite; taking enriched opposites gives the claimed identification. |
| epsilon is the coherent-realization counit at C opposite | `Data.epsilon_objects` and `epsilon_maps` fix its composite on every defining coherent simplex to the ordinary endpoint composite, in every mapping degree k. These are the simplex-colimit counit formulas, not merely its behavior on vertices or on pi-zero. Empty mapping sets impose no nonexistent arrows. |
| u=epsilon opposite | `Data.u_objects`, `u_maps` give exactly the opposite object and full mapping maps. This also removes the irrelevant double-Opposite type synonym on C. |
| Identity-target T_S and ordinary-target H_C | `Data.identityTarget` is normalized to the double-opposite identity on objects and full homs. `Data.presentation.straightening` is the prerequisite's `IsStraightening`, hence gives the actual ordered-cone pushout values, precomposition actions, and input arrows. `cone K` precomposes its identity-target L with `Over.post opFunctor`. This is T_S(X opposite), expressed in the existing general target interface. |
| Changed target attaches along epsilon C[p opposite] | `Data.attaching : identityTarget ≫ targetOpposite u = epsilon`; `IsStraightening` uses `rigidification.map X.hom ≫ phi` as the pushout leg. Rewriting by attaching gives precisely the stated leg. |
| u is Dwyer--Kan | First theorem conjunct, `Bergner.dwyerKanEquivalences K.u`, the same predicate used by unmarked straightening. It is an output, not a hypothesis. |
| P is projectively cofibrant | Second conjunct: for every initial Z and its arrow i into `(cone K).obj X`, `projectiveCof (Index C) i`. This is the initial-map definition, and handles every X. The prerequisite model theorem supplies initial objects; no new choice or model structure is imposed. |
| u_!P naturally isomorphic to H_C(X)=L_epsilon(X opposite) | `Data.change : TargetChangeComparison presentation u identityTarget`. Its `mate` is a natural isomorphism `L_identity ⋙ kan ≅ L_(identityTarget ≫ u opposite)`. `attaching` identifies the target with L_epsilon. Its inherited `unitMap_eq` fixes the cone-pushout map, and `mate_adjunct` fixes the mate, rather than asserting an arbitrary isomorphism. Inherited `IsStraightening.obj_eq` is exactly the displayed `(pushout)(c,v)` formula for H_C. |
| w:u_!P->D opposite objectwise weak | The third theorem conjunct universally binds `w : K.change.kan.obj ((cone K).obj X) ⟶ K.strictOp.obj D`, then assumes `projectiveWeak (discreteCategory C) w`. This is realization weak homotopy equivalence at every c. |
| Its Kan-extension adjunct P->u*D opposite is objectwise weak | `firstAdjunct` is defined by `K.change.kanAdj.homEquiv _ _ w`. The first output under the w hypothesis is `projectiveWeak (Index C) (firstAdjunct ...)`. No arbitrary map or assumed weak unit occurs. |
| Cone criterion gives contravariant X opposite->U_S(u*D opposite) | `secondAdjunct` is `K.coneAdjunction.homEquiv _ _ (firstAdjunct ...)`. `Data.coneAdjunction_eq` normalizes the bijection on each input simplex using the inherited `SimplexDescription`. The second output is `contravariantWeak S (secondAdjunct ...)`. |
| Opposite gives covariant X->U_B^cov(u*D opposite) | `covariant K` is U_S followed by the inverse of `Over.postEquiv opEquivalence`. `covariantAdjunct` is the inverse-equivalence image of the second adjunct preceded by its unit at X. The third output tests its image under `Over.post opFunctor` by `contravariantWeak S`: exactly the opposite definition of covariant weak equivalence. The unit is necessary because double opposite is canonically isomorphic to, rather than definitionally equal to, X. |
| These targets are the stipulated one-sided unstraightenings | The remaining outputs under the same hypotheses assert `Enhanced.rightFibration` of the first target projection and `Enhanced.leftFibration` of its opposite transport, consistent with the presentation's U_S and covariant convention. |
| Naturality in X and strict Kan diagrams, including compatibility of w | The last conjunct binds X,Y,D,E,k,a,w,w', their Kan conditions, and `kan.map (cone.map k) ≫ w' = w ≫ strictOp.map a`. It concludes the three equalities for `firstAdjunct`, `secondAdjunct`, and `covariantAdjunct`. These are equalities of actual enriched/slice arrows. No weak-equivalence condition is imposed on a, k, w or w' for these squares. Naturality of beta is already part of `Data.change.mate`; the same squares therefore apply to w written on H_C(X). |

Dependencies read and reused (module names have prefix `Sheaf.`):

- `CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`,
  defined by realization components and all positive based homotopy groups; the module
  reuses Mathlib SSet, nerve, products, horn and KanComplex rather than redefining them.
- `AlgebraicTopology.UnmarkedStraighteningQuillen`:
  `SSet.UnmarkedStraightening.Diagram`, `DiagramHom`, `action`, `projectiveWeak`,
  `projectiveCof`, `oppositeCategory`, `IsStraightening`, `SimplexDescription`,
  `IsConeAdjunction`, `contravariantWeak`, `unmarked_straightening_quillen`.
  I read the entire theorem signature and all relevant construction/docstring signatures.
  DiagramHom uses unit-graded enriched transformations, not underlying ordinary naturality.
- `CategoryTheory.SimplicialRightFibrationPresentation`:
  `SSet.SimplicialRightFibration.CoherentReversal`, `RightData`, `CovariantData`,
  `Presentation`, `simplicial_right_fibration_presentation`. The covariant construction
  is ordinary opposite-slice transport; it does not claim simplicial opposite preserves
  the enrichment. The general unmarked IsStraightening presentation is used for the
  cone functors; no second definition of the existing concrete cone is introduced.
- `AlgebraicTopology.UnmarkedStraighteningTargetChange`:
  `TargetChangePresentation`, `TargetChangeComparison`, `targetRestriction`,
  `targetOpposite`, `unmarked_straightening_target_change`. The comparison includes
  kanAdj, the mate isomorphism, its adjunct equation, full pushout-map normalization,
  and naturality, which are reused verbatim.
- `CategoryTheory.EnrichedDiagramRectification`:
  `CategoryTheory.EnrichedRectification.enriched_diagram_rectification`, including
  its normalized rigidification adjunction and locally Kan counit DK clause.
- `CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.SimplicialQuillenEquivalence` and
  `simplicial_projective_model_calculus`; its `quillen_criterion` uses the actual
  homEquiv with cofibrant source and fibrant target, without local Kan assumptions.
- `AlgebraicTopology.SimplicialPresheafProjectiveModel`:
  `SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`, both its Kan-model
  combinatorial/simplicial clause and ordinary-presheaf objectwise fibrancy clause.
- Proof input `CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.coherent_nerve_comparison`, `DwyerKanEquivalence`, and
  `CoherentNerveComparisonStatement.discrete_nerve`, with its simplex normalizations.
- Added already-landed statement dependency `lem-coef-free-factor-hammock-pushout`,
  module `CategoryTheory.FreeFactorHammockPushout`, solely for its existing
  `CategoryTheory.FreeFactorPushout.discreteCategory`/`discreteEnrichment`. Read its
  node, declaration and docstrings; it is constant at ordinary homs in each degree,
  with the actual ordinary composition. No new enrichment copy is defined. Its
  hammock-pushout theorem is not an extra mathematical hypothesis or proof step.
- `lem-coef-infinity-opposite-subdivision-kan-zigzag` has no published lean record,
  so there is no recorded module to import for that proof input. Its stated
  Kan-preservation fact is retained in proof step 4, not silently assumed as a binder.

Sources opened independently: the current blueprint ancestor
`main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
and the original [HTT PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf), printed
pp. 72--74, 197--198 and 871--873 (PDF pages 89--91, 214--215, 888--890).
The former fixes the ancestry; HTT supplies the model construction used by this
auxiliary node. In particular the project server explicitly keeps C fixed for valuewise opposite,
2.2.1 defines St by the last-vertex cone pushout, and A.3.3.8(1) is the enriched
projective change-of-index equivalence. No source correction is needed.

Searches run afresh with msearch.py (and returned declaration types read):

- LeanFinder: “For a Dwyer Kan equivalence the adjoint of an objectwise weak equivalence
  from a cofibrant ordered cone diagram to a strict Kan diagram is weak”. Eight hits:
  generic cofibrant-object localization, homotopy and ordinary nerve adjunctions;
  none identifies these two canonical adjuncts or the ordinary-base cone diagram.
- Loogle: `"LeftExtension"`. Twelve ordinary categorical Kan-extension declarations,
  including `Functor.LeftExtension` and its transport equivalences. They do not
  state the enriched projective weak-equivalence criterion or this comparison.
- Mathlib grep through msearch: `straighten|unstraighten|Dwyer.Kan|QuillenEquivalence`
  in CategoryTheory: zero hits.
- LeanSearch: “cofibrant cone diagram Dwyer Kan enriched left Kan extension adjoint weak
  equivalence”. Eight hits including `Functor.lanAdjunction`, `leftKanExtension`,
  and generic cofibrant resolutions, none the required theorem.
- Local rg of upstream WeilConjectures, current lean/Sheaf, and
  dag/lean_names_upstream.json for the item id, `ordinaryConeModel`, and
  `ConeModelComparison`: no existing item declaration. Direct id search upstream
  also returned no result. Broader source searches located the prerequisite
  target-change and cone-presheaf constructions listed above; these were read and reused.

Edge cases checked before writing and again after compilation: C empty (there is only
the empty input over its empty nerve; the diagram conditions and squares are vacuous
at objects but the cone/adjunction constructions still exist); empty X over a nonempty
base (T is initial and the cofibrancy claim uses its initial arrow); empty Kan values
(no artificial dimension-zero filler/nonemptiness condition); C=[0] (u is the point
index comparison and the cone adjunction is the Q-realization/Sing_Q comparison);
C=[1] (reversing the source and then taking enriched opposite gives covariant indexing
by C; the strictOp action still sends c->d forward); non-Kan X (admitted); no
projective-cofibrancy hypothesis on D; maps a of Kan diagrams which are not weak
(no restriction on a in the naturality conclusion); all small cardinalities (one
explicit universe u, no countability or independent smaller test universe).

Compile evidence: `scompile.py N7 lem-coef-unmarked-cone-model-comparison
<...>/lean/Sheaf/AlgebraicTopology/UnmarkedConeModelComparison.lean` returned exit 0.
It reported `sandbox Sheaf/Stage2/Sandbox0.lean` clean in 1.8 s and
`library Sheaf/AlgebraicTopology/UnmarkedConeModelComparison.lean` clean in 2.0 s,
with no warnings or errors. The wrapper's server compile used the prescribed 60-second
file limit. No direct Lean or Lake invocation was used. Maximum source width: 91.
The exact multiline theorem signature was copied programmatically from the file to
`lean.statement`; explicit `set_option autoImplicit false` and `universe u` bind all
variables and universes.

No STATEMENT-DISPUTED issue, new node, dependency-interface repair, or statement
correction is present. The inherited node statement, source, proof and proof_deps stay
unchanged. The new lean record and the one landed construction dependency are the
only node changes.

## Second reading by N7

This is a separate, substantive rereading pass by the same dispatched worker; the brief
explicitly prohibits starting another agent. It is not represented as an independent
worker's review. The maintainer supplies that independent review. I reopened the
current node and the completed module together and checked the following points.

1. Compared the hypotheses first, without using the proof: C is any small ordinary
   category; p is bound as the slice object's hom; X has no fibrancy assumption;
   D is an ordinary functor with exactly the objectwise Kan condition. A and S use
   opposite in the right places. No model-equivalence hypothesis has been inserted.
2. Read `Data.epsilon_maps` at a nonzero mapping degree: it gives the full constant
   endpoint composite, while `u_maps` reverses its endpoints. Thus the witness cannot
   substitute an unrelated DK functor. The double-opposite identity and attaching
   equality force the exact changed-target attaching map. The action formula for
   strictOp is forward in C, with valuewise SSet opposite; it does not take C opposite.
3. Reopened the prerequisite TargetChangeComparison: its `mate`, `mate_adjunct`, and
   `unitMap_eq` account for beta, its canonical nature, and naturality in X. Reopened
   IsStraightening: obj_eq, action_eq, map_eq fix the displayed H_C pushout and both
   functorialities. These clauses occur in Data, even though the main theorem uses
   the shorter field names. Hence the statement does not merely assert existence
   of an unspecified isomorphism.
4. Checked arrows from their definitions: firstAdjunct uses the Kan-extension
   homEquiv on w; secondAdjunct uses the cone homEquiv on that same map; the normalized
   cone adjunction rules out an arbitrary natural automorphism of this bijection.
   The three weak claims refer exactly to these definitions. On the covariant side
   the involution unit is explicitly included, so the source is actually X.
5. Compared the three naturality equations with proof step 7 by reading composition
   left-to-right. Compatibility says `u_!P(k);w' = w;a opposite`. The conclusions
   are `P(k);f' = f;u*(a opposite)`, `k opposite;g' = g;U(u*(a opposite))`, and
   `k;g'_cov = g_cov;U_cov(u*(a opposite))`. They impose no weak condition on a.
   The inherited mate naturality also accounts for the H_C version. Identity and
   composition cases follow as the same equations on compatible inputs.
6. Rechecked the universal initial-map cofibrancy clause against the existing
   ConePresheaf.IsProjectivelyCofibrant convention. It is the same mathematical
   condition in the strict-enriched target-change diagram wrapper; initial objects
   are supplied by the recorded projective model theorem. It does not assume X is
   a right or left fibration. Rechecked empty C, empty X, and empty Kan values.
7. Rechecked the new declarations against the local source searches, imports against
   stmt_deps/proof_deps, all declaration docstrings and seven proof steps, the single
   sorry, explicit binders, and the compiled exact signature. No mathematical mismatch
   was found. The extra already-landed dependency was added to record the actual
   reused discrete-enrichment construction. The absent original report/module/record
   are now replaced with the complete stage-2 delivery, rather than an unchanged push.

Delivery validation: `deliver2.py N7 lem-coef-unmarked-cone-model-comparison --no-push`
returned `OK (dry run): commit 19d21a10c9 passes the preflight and compiles; nothing pushed`.
The staged set was exactly the item node, this report, and the one Lean module. A separate
source comparison confirmed only `lean` and `stmt_deps` changed, the stored signature is
verbatim, the file has exactly one proof hole, and both Lean/JSON files end in newlines.
