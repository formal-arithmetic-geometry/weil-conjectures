## Worker report

Item: lem-cbc-complete-proetale-composition-pasting-coherence.
Module: Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting.
Namespace: AlgebraicGeometry.ProEtale.StrictTower.

The module constructs the particular strict-tower maps in the node and states their
coherence. All four theorem proofs are `sorry`; all definition data are actual
composites of the recorded normalized comparisons. No new independent definition node,
statement correction, or dependency-record repair is needed. The local input structures
only package the supplied compatible-tower refinement and pullback data already described
by lem-cbc-compactifiable-compatible-tower and this item's statement.

Hypotheses and clauses, in source order:

- The commutative ring is `(B : Type (u + 1)) [CommRing B]`, the coefficient universe
  required by StrictConstantTowerOperations, with `Scheme.{u}`. This preserves the small
  pro-etale site's object/morphism universe distinction. No new universe equality is used.
- Every theorem binds `f : X ⟶ Y`, `h : Y ⟶ Z`, their `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact` instances. The last two instances together mean finite type.
- The supplied compatible tower is the recorded dependency's upstream
  `Compactification.Triangle f h`. Its fields correspond to the node as follows:
  `T.cf.i = c`, `T.cf.g = p_Y`, `T.cg.i = i`, `T.cg.g = q`, `T.cfg.i = a`,
  `T.q = b`, and `T.p = p`. The compactification fields supply properness and openness;
  `Triangle.isProper_p` supplies properness of p. `T.i_q` is bc=a, `T.cf.comm` is p_Yc=f,
  and `T.isPullback` is the cartesian square. Its intermediate scheme is the fibre
  product up to the unique projection-preserving isomorphism, as expressly documented
  in the dependency module. It is not a different intermediate construction.
- `QuasiCompact` instances on the displayed open maps render their quasi-compactness.
  Each clause binds the open maps it uses. The isomorphism clause only needs c,i,b;
  a is their composite. No assumption on the base being qcqs or Noetherian is added.
- `compositionF B T.cf`, `compositionF B T.cg`, and `compositionF B T.cfg` are precisely
  F_f=R_pY J_c, F_h=R_q J_i, and F_hf=R_qp J_a. In Lean the functor composition is
  written in the order in which it acts, so F_f ⋙ F_h is the node's F_h F_f.
- `compositionD B T` is a natural transformation constructed by whiskering the existing
  `gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm` first by J_c and then R_q.
  `jComp` followed by `jCongr T.i_q` identifies J_b J_c with J_a; `rComp` followed by
  equality transport along `T.p_g` identifies R_q R_p with R_qp. All associators are
  inserted in its definition. No unspecified map with the right endpoints is assumed.
- The first clause of `compositionPastingCoherence` asserts
  `IsIso ((compositionD B T).app M)` on exactly the stipulated inputs:
  `∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))`.
  `ScalarEtaleOrigin` retains a finite commutative ring Λ_n, the homomorphism B→Λ_n,
  a bounded-below pro-etale object, its bounded-below etale origin L_n, and the
  scalar-restriction isomorphism. Each level has its own ring and lower bound.
  Naturality is already present in the constructed transformation. Pointwise
  invertibility is the natural-isomorphism assertion on the full subcategory of these
  inputs; it does not assert invertibility on all unbounded inputs.
- For refinement 1→2, `CompositionRefinement T₁ T₂` contains three existing
  `Compactification.Refinement` records: `rf.hom=w`, `rh.hom=u`, `rfh.hom=v`.
  Their `i_hom` equations give wc₁=c₂, ui₁=i₂, va₁=a₂. Their `hom_g` equations give
  p_Y2 w=p_Y1, q₂u=q₁, and compatibility on the composite hf. Its two remaining fields
  `b_comm` and `p_comm` give vb₁=b₂w and p₂v=up₁. All three maps are proper by the
  existing refinement instance. The composite-hf equation follows from the seven
  displayed equations and both triangles' p_g equations; packaging it in the existing
  refinement record adds no mathematical hypothesis. In particular no cartesian
  condition on these refinement squares is present.
- `compositionC B r.rf`, `compositionC B r.rh`, and `compositionC B r.rfh` give C_f,
  C_h and C_hf. The generic construction uses the actual identity-left gamma square,
  first inserts the normalized `rId` inverse, then applies gamma and the corresponding
  proper image, and finally uses `rComp` and the refinement's `hom_g` equation.
- `compositionH B r` is `(F_h2 C_f)` followed by `(C_h F_f1)` in the node's convention.
  The second clause of `compositionPastingCoherence` is the exact equality
  `compositionD B T₂ ≫ compositionC B r.rfh = compositionH B r ≫ compositionD B T₁`,
  i.e. C_hf D₂ = D₁(C_h F_f1)(F_h2 C_f).
- Arbitrary base change is bound as `g : Z' ⟶ Z`, with x=g_X and y=g_Y and a supplied
  pulled-back triangle. `CompositionBaseChange T T' x y g` records d:U'→U,
  t:Ybar'→Ybar, s:Xbar'→Xbar and its cartesian faces. These are the faces of the
  supplied pulled-back tower, including the open and proper faces for f,h,hf,b,p.
  They introduce no property of g: it may be arbitrary, including identity.
- `compositionE` is exactly the proper-square `exchange` mate followed by the
  open-square `beta`. `compositionEf`, `compositionEh`, `compositionEhf` specialize
  it to the three compactifications with the corresponding projections. The
  `IsPullback.w` equations give their commutative squares, not arbitrary arrows.
- `compositionHorizontalE` is `(e_h F_f)` followed by `(F_h' e_f)`, with associators.
  The third clause of `compositionPastingCoherence` is
  `whiskerRight D (G g) ≫ e_hf = horizontalE ≫ whiskerLeft (G x) D'`:
  precisely e_hf(G_gD)=(D'G_x)(F_h'e_f)(e_hF_f).
- `compositionRefinement_isIso` states the invertibility of C_hf and H on M, needed
  for the stated transport. It uses the finite-origin hypothesis only on M, and does
  not assume that F_f M has finite etale origin.
- `compositionRefinementExchange` states that both boundaries (C_hf and H) intertwine
  their exchanges for a refinement and its pulled-back refinement. Its wf,wh,wfh
  equations only identify the pulled-back refinement maps with the supplied maps.
  These two equations, together with the refinement and vertical-interchange clauses
  and their primed instances, are transport of the whole vertical-interchange square.
  They hold on the whole category, with no boundedness or evaluation hypothesis.
- `compositionCommonComparison` constructs the horizontal and hf comparisons from any
  common refining tower as H₂⁻¹H₁ and C₂⁻¹C₁. Its inverses come from the preceding
  isomorphism theorem; there is no arbitrary isomorphism choice. `compositionCommonCoherence`
  first states that these comparisons intertwine the two D maps, and then states
  equality with the comparisons obtained from every other common tower and every
  other pair of refinement arrows. The compatible-tower dependency supplies existence
  of common towers. Together with `compositionRefinementExchange`, this gives the last
  sentence's unchanged, independent transport of both D and the interchange identity.
- All equalities are either equalities of natural transformations in Derived B, or
  (for restricted-input common-refinement inverses) morphisms there at M. Evaluation
  occurs only in the finite-origin hypothesis. Evaluation is never assumed faithful.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.StrictConstantTowerOperations:
  `Towers`, `Derived`, `G`, `R`, `adj`, `ev`, `rComp`, `rId` in the above namespace.
- Sheaf.AlgebraicGeometry.StrictTowerOpenExtension: `J`, `jAdj`, `jComp`, `jCongr`.
- Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus and its imported
  Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows: `gamma`, `beta`, `exchange`,
  `gamma_isIso`, `normalizedProperOpenCalculus` and their normalization definitions.
- Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport: `ScalarEtaleOrigin`,
  `finiteRestriction`, `H`, `HD`, `hJ` and their canonical scalar/open transport.
- Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower:
  `AlgebraicGeometry.exists_compactifiable_compatible_tower`. Its statement explicitly
  uses upstream `Compactification.Triangle`; the present file uses that same interface.
  Upstream WeilConjectures.Compactification.Triangle and .Refinement provide
  `Triangle`, `Triangle.isProper_p`, `Refinement`, its properness instance and equations.
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition:
  `CategoryTheory.ringedToposDerivedPushforwardComposition` is imported for the canonical
  derived direct-image composition plan. The expressions use the already normalized
  strict-tower specialization `rComp`, not an instantiation forcing small-site
  object/morphism universes equal.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType, .QuasiCompact, .Proper and .Separated:
  `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsSeparated`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, its projections
  and universal property, as used by the recorded triangle's cartesian presentation.
- Proof-only imports: Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison,
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`;
  WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs,
  `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`;
  Mathlib.CategoryTheory.Adjunction.Mates, `mateEquiv_vcomp`, `mateEquiv_hcomp`,
  the conjugate-pasting equations and identity normalization.
- The proof dependency lem-cbc-complete-proetale-refinement-exchange-coherence has no
  recorded Lean module on the read base. It is cited in the proof docstring, and no
  nonexistent proof import is invented. Its notions are all already available from
  the statement dependencies, so it is not a missing notion needed to state this item.

Sources opened: the node and all stmt_deps records; the recorded Lean source modules;
Stacks more-etale.tex, lemma-shriek-composition (0F7J), the horizontal/vertical pasting
lemmas (0F7C/0F7D), and lemma-shriek-proper-and-open-base-change (0F7F); the current
main-20261015 thm-cbc-complete-proetale statement and proof (now filed in
sec-six-functors-basics/sk-thm-sf-pf-adic). The source's etale result is only the source
of the argument: the extra strict-tower equations are stated as the node requests.

Edge cases checked by reading the actual constructions and signatures:

- Zero ring B and infinite B: no Nontrivial or Finite instance is imposed on B.
- Empty X or other empty schemes, and zero complexes: there is no nonemptiness or
  nonzero-object requirement; all gamma/beta composites remain defined.
- n=0 means positive level 1 by the existing tower convention. All n are quantified;
  neither one finite coefficient ring nor a uniform cohomological bound is required.
- Identity refinement and identity base change: their normalized rId, beta and
  compositor maps are retained, rather than replaced by arbitrary endpoint isomorphisms.
- Identity open maps, a proper f, or an open h: identity maps fit the same definitions.
- Noncartesian refinement squares: CompositionRefinement has only the equations and
  proper refinement maps; it does not use upstream Triangle.Hom's cartesian fields.
- Arbitrary nonproper/nonsmooth base change, non-qcqs base, and non-Noetherian base:
  the corresponding assumptions are absent. Compactifications are supplied throughout.
- A common refinement with different arrows: the final universal clause quantifies
  over both arrows, not just a canonical pair or a fixed choice of common tower.

Searches (the interrupted session's persistent searches.jsonl was read before resuming):

- msearch.py leanfinder: "Composition comparison for compactly supported direct image
  on strict proetale towers coherent with refinements and arbitrary base change".
  Eight hits, including Scheme.Hom.appLE_comp_appLE, Scheme.Modules.pushforwardComp,
  Scheme.comp_appLE and presheafed-space composition. None state these normalized
  strict-tower maps or refinement/base-change identities.
- msearch.py loogle: `CategoryTheory.Adjunction, "mate"`. Twelve hits including
  mateEquiv, its unit/counit equations, mateEquiv_vcomp and conjugate-pasting lemmas.
  These supply generic tools, not this statement.
- msearch.py grep: `compositionPasting|composition.*[Rr]efinement|strictTower.*[Cc]ompos`
  in Mathlib/CategoryTheory. Three files (Abelian/Refinements, Hypercover/Zero and One)
  concern different refinements; no match for the item.
- msearch.py leansearch on resume: "Compactification composition comparison on derived
  strict towers commutes with proper refinement and arbitrary base change". Eight
  hits including IsBaseChange.of_comp/comp_iff, proper/quasicompact composition and
  SheafOfModules.pushforwardComp. No strict-tower composition-pasting theorem.
- rg of /home/ubuntu/weil-src-slopmaster2/WeilConjectures and lean/Sheaf for
  compositionPasting, strictTower, strict_tower and this blueprint id found only
  unrelated tower truncation/evaluation and exchange-normalization files, with no
  existing statement of the item. Upstream Compactification.Triangle supplies the
  tower notion and is reused. Its Hom is too restrictive for the present refinements.
- A final rg for compositionPastingCoherence, CompositionRefinement,
  compositionCommonComparison, compositionRefinementExchange and compositionF/C/D/E/H
  in the upstream source, shared lean/Sheaf and side lean/WeilConjectures returned
  no duplicate declarations.

Validation: scompile.py compiled the complete module as both the sandbox and canonical
library-path file, cleanly, with no errors or warnings. The final pass reported 7.9 s
for the sandbox and 19.4 s for the library file, under the prescribed 60 s per-file limit.
No global build was run. No STATEMENT-DISPUTED finding or node correction.

## Second reading by NA

The same dispatched worker reread the node and final module in a separate second pass;
no independent review by another worker is claimed (this dispatch forbids starting other
agents). The maintainer's independent delivery review remains required.

The pass checked each row above against the file: F functor direction; gamma's proper
identity normalization in C; placement of rComp/jComp and the triangle's p_g/i_q
transports in D; all seven refinement equations; lack of cartesian refinement premises;
proper-then-open order in all exchanges; order of C_f and C_h in H; direction of the
vertical-interchange equation; finite-origin only on M; invertibility of C_hf and H;
both boundary exchange equations; common comparison C₁ followed by inverse C₂; equality
for every second common refinement and every pair of arrows. The main theorem's
naturality is intrinsic to the constructed natural transformation. No mismatch or
statement change remained. The two input structures package existing supplied data,
not a replacement operation, independent mathematical notion, or extra assumption.
