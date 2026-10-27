## Worker report

The module Sheaf.AlgebraicGeometry.RegularFlagBlowupGeometry states the complete node in two named theorems: `AlgebraicGeometry.RegularFlagBlowupGeometry.regular_immersion_conormal_rank` is its universal assertion about a single regular immersion of arbitrary codimension; `regular_flag_blowup_geometry` is the regular-flag assertion and both blowup constructions. Both proofs are `sorry`. Every auxiliary definition has actual data: predicates spell out canonical equations and geometric conclusions, and `squarePullbackIso` composes the existing normalized pullback comparisons. There is no existence choice of an arbitrary scheme, map, module or isomorphism in any definition.

Hypotheses and clauses, in node order:

* The binders `X Y Z : Scheme.{u}` with all three `IsNoetherian` instances render Noetherian schemes. The maps are `i : Z ⟶ Y` and `j : Y ⟶ X`. The natural numbers `m n`, inequalities `hm hn`, and `hi hj : IsRegularClosedImmersionWithCodimension ... (fun _ ↦ ...)` render positive constant codimensions and regular local equations. This existing predicate uses the recorded Mathlib regular-sequence definition and closed immersions, and imposes the equations only along the source, retaining empty sources. No ambient regularity assumption is imposed.
* The conormal throughout is the existing `ConormalGradedAlgebra.piece k 1`, definitionally `(tensorPullback k).obj k.ker.toModules`. The affine-conormal dependency identifies it with I/I². No dual normal module is substituted.
* `regular_immersion_conormal_rank` quantifies independently over every `V W k c`, with `c : ℕ` including zero, the two Noetherian instances, and regular immersion of constant codimension c. Its conclusion is `IsFiniteLocallyFreeOfRank c`. The first four conclusions of the flag theorem give regularity of the composite and the three ranks m, n and m+n.
* `ConormalSequence` records the inclusion from i* N(j), the quotient to N(i), their zero composite and `ShortComplex.ShortExact`. `inclusion_canonical` and `quotient_canonical` use `IsConormalMap` to require the actual maps on ideal sections. Identity pullback uses `tensorPullbackSectionId`.
* `AlongMiddle` fixes B to `j.ker.blowup`. This is the canonical Rees-Proj blowup, not an existential modification. `projective` identifies P with the canonical symmetric relative Proj of N(j); `projective_over` identifies the projection. The square `_cartesian` says P is the scheme-theoretic inverse image of Y. `_cartier` is the dependency's effective-Cartier-ideal predicate.
* `twistMap`, `_twistMap_canonical` and `_twist` identify the exceptional ideal with O_B(1). `HasReesTwistOne` supplies isomorphisms on every affine base Proj chart, sending each original ideal section to the existing degree-one Rees section `Proj.unitToTwist (reesX_mem ...)`. The isomorphisms are for one global module and are normalized on the generating sections; hence they give its specified degree-one twist rather than an unspecified line of the same rank. `IsIdealPullbackMap` fixes the ideal map by its composite into O_B.
* `P' iP p' baseChange` express P'=P×_Y Z. `regular_iP` and `regular_composite` give codimensions m and m+1. The maps `q q'`, their `IsConormalMap` equations and epi clauses give exactly the two natural conormal surjections.
* `K κ κ_zero kernel_property` and their primed counterparts assert the universal kernel properties of these surjections. They do not accept arbitrary bundles with the correct rank. `kernel_rank kernel'_rank` give rank n-1. `kernelIso` gives iP* K ≅ K'; `kernelIso_canonical` makes its composite with κ' equal to pullback of κ, the normalized pullback square comparison, and p'* of the original conormal inclusion. `baseConormalIso` and its canonical-map clause identify N(iP) with p'* N(i). The normalized tautological quotient and `conormalLine` also tie the projective-bundle identification to q.
* Under exactly `n = 1`, `AlongSmallest` fixes B to `(i ≫ j).ker.blowup`. Its P, projection, projective comparison, cartesian square, Cartier ideal and normalized Rees twist are the corresponding constructions for the center Z.
* `T strictIso t _strictMap` identify T with the dependency's scheme-theoretic strict transform, using the complement of the support of the actual ideal of Z. `strictBlowupIso` and its equality over Y identify it with `i.ker.blowup`. `_strict_closed` and `_strict_cartier` state that its immersion into B is effective Cartier.
* `P' kP kT _intersection` is the scheme-theoretic intersection. `intersection_projective` and `_intersection_over` identify it with the canonical P(N(i)) over Z. `_transverse_on_P` and `_transverse_on_T` require each divisor ideal pulled to the other to be effective Cartier, exactly the parenthetical meaning of transverse intersection in the node.
* `factor` is the isomorphism π* I_Y ≅ I_P tensor I_T. `_factor_canonical` equates its composite with multiplication of the actual ideal embeddings to the actual pulled-back inclusion into O_B. Thus it agrees with the canonical trivializations off π⁻¹Y: each ideal embeds as O there and multiplication sends 1 tensor 1 to 1. The three invertibility witnesses state these are invertible modules.
* `_K0_line` states that i* N(j) is a line. `tautological`, `lineIso`, `quotient` and its normalization give the actual degree-one quotient line on P(N(ji)), and `conormalLine` plus its canonical-map equation identify the exceptional conormal quotient. `minusOne evaluation` describe its tensor inverse O(-1). `hyperplane` identifies the actual ideal of kP with p* K0 tensor O(-1); its last equation makes the ideal embedding the inclusion of K0 followed by the tautological quotient and evaluation. This retains the canonical hyperplane map and the sign of the twist.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `AlgebraicGeometry.IsClosedImmersion`.
* Mathlib.RingTheory.Regular.RegularSequence: `RingTheory.Sequence.IsRegular` and `IsWeaklyRegular` (and the proof input `IsLocalRing.isRegular_of_perm`).
* WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree: `SheafOfModules.IsFiniteLocallyFreeOfRank`.
* WeilConjectures.AlgebraicGeometry.RelativeProj.Basic: `Scheme.GradedAlgebraData`, `relProj`, `relProjHom`, `relProjι`, `relProjRestrictIso`, with its source GradedAlgebraData definition.
* WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible: `Scheme.IdealSheafData.IsInvertible`, the affine nonzerodivisor condition.
* WeilConjectures.Compactification.StrictTransform: `strictTransform`, `strictTransformMap`, `strictTransformToSource`, using the scheme-theoretic image of the complement open.
* WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules and UnitToTwist: `Proj.twist`, `Proj.unitToTwist`.
* Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: `tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionComp`, `tensorPullbackSectionId`; no duplicate pullback is defined.
* Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra: `SymmetricAlgebraSheaf.gradedAlgebraData`.
* Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData: `TautologicalQuotient`, `pulledQuotient`.
* WeilConjectures.AlgebraicGeometry.AffineConormalSections: `Scheme.Modules.affine_conormal_sections`, including its generator normalization.
* The added already-landed statement dependencies are def-per-regular-closed-immersion-codimension (`IsRegularClosedImmersionWithCodimension`), lem-pur-conormal-graded-algebra-basic (`ConormalGradedAlgebra.piece`), and def-nagata-global-blowup (`Scheme.IdealSheafData.blowup`). These reuse existing notions. The Rees comparison in RelativeProj.Rees is imported as well.

The stated proof inputs are imported without `public`: BlowupChartRegularSequencePresentation, ProjectiveBundleQuotientGeometry, ProjectiveBundleTautologicalGeometry, RegularSequenceGradedPolynomial, RegularSequenceConormal and Blowup.FiniteDegree.Algebra. The finite-local-free, Cartier, strict-transform, twist, regular-sequence and affine-conormal proof inputs already have public statement imports. No unstated proof prerequisite is assumed as a hypothesis.

Source check: read the local ILO PDF, physical pages 240–243, printed 234–237, covering the conormal diagram and excess kernels in Lemma 2.3.3 and the divisor factorization and K tensor O(-1) in Theorem 2.3.2. The source's apparent N_{Bl/P'} typo in the definition of the unprimed kernel is resolved by its diagram, as already resolved in the node. No statement correction is needed.

Edge cases checked: c=0 for a single immersion gives the zero conormal near the source; empty sources and the empty ambient scheme are retained, without Nonempty hypotheses. For n=1, n-1=0 gives both zero excess bundles, while the second blowup still uses the positive m hypothesis. For m=n=1 on Spec k[x,y] all Cartier/intersection and ideal formulas have the expected two charts. The same regular equations over k[ε]/(ε²)[x,y] show why no regularity of the ambient schemes may be added. Codimension-zero open-and-closed immersions are allowed by the source-local regular-immersion predicate. The complement of Z, rather than the complement of Y, is used for the second strict transform; the factorization normalization uses the complement of π⁻¹Y. Universes are explicitly bound, and no test universe or site-size equality is added.

Searches for an existing statement:

* msearch leanfinder: "Blowup of a flag of regular closed immersions conormal exact sequence exceptional divisor strict transform" returned eight general immersion/ideal-sheaf hits, no matching geometry statement.
* msearch loogle: `"conormal", "blowup"` returned zero hits.
* msearch grep: `regular.flag|regularFlag|conormal.*blowup|blowup.*conormal` under Mathlib/AlgebraicGeometry returned zero hits.
* msearch leansearch: "conormal exact sequence regular immersions blowup exceptional divisor" returned eight general closed-immersion and immersion hits; none is this statement.
* rg of lean/WeilConjectures and lean/Sheaf for regular flags, regular closed immersions, conormals, blowups, Rees algebras and projective quotients found the reused building blocks above but no complete statement. The exact node-id search in WeilConjectures returned no declaration. The old CompactObject example in Sheaf is withdrawn; its current upstream module was read for the module conventions.

No new nodes and no dependency modules. No statement disputed and no mathematical node fault found. The report uses the universal-property formulation of kernels and the tensor inverse of the normalized tautological line; these are equivalent presentations, not new hypotheses. The two conclusion predicates introduce only this node's conclusion data, so they belong in the owning module under the authorized helper rule.

## Repair of returned delivery d7261c7118cf

H2: added the four requested definition owners to `stmt_deps`, after reading their current node records, declaration signatures and docstrings:

* `def-sfb-tensor-pullback-structure-sheaf-map`: `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`, `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit`, used by `IsIdealPullbackMap` and the factorization equation.
* `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible`, used for the invertible modules and line.
* `def-nagata-affine-blowup`: `WeilConjectures.Blowup.Affine.Defs`, `AlgebraicGeometry.AffineBlowup`, used in `HasReesTwistOne`.
* `def-nagata-rees-piece`: `WeilConjectures.Blowup.Affine.ReesGrading`, `AlgebraicGeometry.reesGrading`, used in `HasReesTwistOne`.

These declarations are already available through the module's public imports. The Lean module and all signatures are unchanged. The returned independent review accepted the mathematics clause by clause and confirmed that `lem-pur-conormal-graded-algebra-basic` is a definition owner; its existing dependency is retained. No correction to the mathematical statement is required.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
