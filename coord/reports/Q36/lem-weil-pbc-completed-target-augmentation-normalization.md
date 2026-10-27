## Worker report

Item: lem-weil-pbc-completed-target-augmentation-normalization. Group Q36, stage 2.

The module `Sheaf.Paper.CompletedTargetAugmentationNormalization` states the three
actual-map identities in `AlgebraicGeometry.Scheme.completedTargetAugmentationNormalization`.
Its additional declaration `completedTargetAugmentationNormalization_square` states the
last paragraph's identification with strict exchange and completed base change.
Both theorem proofs are `sorry`. There are no new definitions, new nodes, dependency
repairs, or statement corrections. The item's only changed field is `lean`.

Read the node's full statement and proof, all statement dependencies' statements and
Lean records, and their source declarations/docstrings. Read Stacks
`sites-cohomology.tex`, lemma-Rf-commutes-with-Rlim (Tag 0A07) and
equation-projection-formula-map (Equation 0B56), and the current blueprint
`main-20261015/.../thm-weil-pbc-finite-extension.proof.md`, integral-lattice paragraph.
The Stacks projection arrow is explicitly the counit-tensor adjunct. The derived-limit
comparison is the comparison of composite direct images, rather than an ordinary limit
in the derived category. The source does not impose properness for those constructions.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| Commutative ring A | `{A : Type (t + 1)} [CommRing A]` |
| Noetherian A | `d : AdicCoefficientDatum A` retains `d.noetherian` from `CompleteCoefficientDatum` |
| Finitely generated ideal I | `d.ideal` and `d.finitelyGenerated : d.ideal.FG` |
| A/I additive torsion | `d.quotientTorsion : ∀ x, ∃ m : ℕ, 0 < m ∧ m • x = 0` |
| Every positive quotient is finite | `d.quotientFinite : ∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))` |
| Every positive quotient is perfect over A | `d.quotientPerfect`, inherited from `CompleteCoefficientDatum`, for all `n ≥ 1` |
| Small pro-etale sites of T | Existing `d.completedRing T`, `d.derived T`, `d.towers T` use `ProEt.topology T` |
| Completed coefficient sheaf A_T | `d.completedRing T` abbreviates `completedReductionCoefficient T d`, the actual limit of `reductionCoefficientSystem T d` |
| Ordinary unbounded module derived category | `d.derived T`, without D+, constructibility, or a restriction on its objects |
| Strict towers | `DerivedCategory (d.towers T)`, where towers are functors `ℕᵒᵖ ⥤ reductionModules T (d.completedRing T)` |
| h:U→V and p:U→W arbitrary | `{U V W : Scheme.{t}} (h : U ⟶ V) (p : U ⟶ W)`; no geometric hypotheses |
| L derived I-complete | `(L : d.derived V) (_hL : d.TowerComplete V L)`; the published quotient-unit completeness condition, compared with intrinsic completeness by `towerComplete_iff_intrinsic` |
| E0 = ordinary Lh* L | `(d.pull h).obj L` |
| N = ordinary Rp* E0 | `(d.push p).obj ((d.pull h).obj L)` |
| Z = completed pullback | `(d.completedPull h).obj L`, the codomain of `d.ordinaryToCompleted h L` |
| Actual completion unit gamma_h | `d.ordinaryToCompleted h L`; this is the constant/Rlim unit followed by Rlim of the pulled quotient augmentation |
| R_T(C) | `(completedReductionTower T d).obj C`, preserving the full quotient transition system |
| i_C | `(completedReductionAugmentation d T).app C`, used by the existing `completionUnit` and `ordinaryToCompleted` definitions |
| F_T = Rlim_T | `completedRlim T (d.completedRing T)` |
| lambda_C | `(d.constantRlimAdjunction T).unit.app C` |
| u_C = F(i_C) lambda_C | `d.completionUnit T C`; in Lean's diagrammatic order it is `lambda_C ≫ F.map i_C` |
| Q = tower pullback of R_V(L) | `(d.towerPull h).obj ((completedReductionTower V d).obj L)` |
| t : Q ≅ R_U(E0) | `(d.reductionTowerPullbackIso h).app L`; the uniquely representative-normalized comparison |
| h_E0 | `d.towerProjection p ((d.pull h).obj L)`, defined by the tower adjunction applied to t and reduction of the ambient counit |
| Normalized chi_E0 | The constant/direct-image mate underlying `towerProjection` and its augmentation compatibility; no independently supplied isomorphism is introduced |
| D = tower pushforward of Q | `(d.towerPush p).obj ((d.towerPull h).obj ((completedReductionTower V d).obj L))` |
| H prime | Explicitly `d.towerProjection p ((d.pull h).obj L) ≫ (d.towerPush p).map ((d.reductionTowerPullbackIso h).inv.app L)` |
| c_B for each strict tower B | `(d.directImageRlimIso p).hom.app B`; this is the published normalized conjugate of the identity constant/pullback square |

The ring, site and module universe conventions are the published ones: schemes have
universe t; site objects have universe t+1, site morphisms t; coefficients are in t+1.
The positive exponent n+1 reindexing retains every positive quotient including A/I.
No site universes are equated. Smaller coefficients can be lifted into the published
coefficient universe; this module imposes no extra size equality.

### Each conclusion

1. The first conjunct is `ordinaryToCompleted h L ≫ F_U.map t.hom = completionUnit U E0`.
   This is exactly F_U(t) gamma_h = u_E0 in the node's functional-composition order.
2. The second conjunct is `completionUnit W N ≫ F_W.map (towerProjection p E0) =
   (d.push p).map (completionUnit U E0) ≫ (d.directImageRlimIso p).hom.app (R_U E0)`.
   It says exactly F_W(h_E0) u_N = c_R Rp*(u_E0).
3. The third conjunct uses the displayed explicit H prime and states
   `completionUnit W N ≫ F_W.map Hprime = (d.push p).map (ordinaryToCompleted h L) ≫ c_Q`.
   Both sides have source N and target F_W D. Neither h_E0 nor gamma_h is inverted.
4. The square theorem binds `sq : ChosenCartesianSquare g' f' f g`, `[IsProper f]`,
   `K : d.derived X`, `hK : d.TowerComplete X K`, and the retained family
   `W : ∀ n, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n+1)) ((d.reduction X n).obj K)`.
   These witnesses contain actual bounded-below etale antecedents and comparison
   isomorphisms, transported to the existing function-coefficient presentation.
   No cross-level compatibility or uniform bound is added.
5. Its first conjunct equates the explicit H prime at (f',g',K) with
   `(exchangeRealizationHPrime (f' := f') (g' := g') d K).hom`. This is the exact target
   projection map of strict-tower exchange normalization, with target tower D.
6. Its second conjunct expands the recorded `completedBaseChangeMap sq K hK W` into
   its ordered composite whose final arrow is
   `(d.directImageRlimIso f').inv.app ((d.towerPull g').obj ((completedReductionTower X d).obj K))`.
   Thus its final comparison really is c_Q inverse, at this exact tower and orientation.
   This equation renders the node's requested identification of already specified maps;
   it introduces no arbitrary choice of isomorphism or additional conclusion.

Completeness of E0 and N, properness of p or h, constructibility, and invertibility
of either h_E0 or gamma_h are absent from the general theorem. The only completeness
hypothesis is the node's completeness of L. Properness and etale witnesses occur only
in the final square specialization, precisely where the node states them.

### Dependencies and canonical-map reuse

All declaration names below are in `AlgebraicGeometry.Scheme` unless qualified otherwise.
All statement dependency modules are public imports; proof-only dependencies are plain
imports. Existing exports, including integral helpers publicly reexported by the current
Qbar completed-pullback module, supply the needed notions without any dependency repair.

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, `completedReductionTower`,
  `completedReductionCoefficient`, `AdicCoefficientDatum.derived`, `.towers`, `.reduction`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: recorded `pbcQbarCompletedPull`; its public import
  chain retains `AdicCoefficientDatum.completedPull` and `.ordinaryToCompleted` from
  `Sheaf.Paper.CompletedPullback`. The general integral interface, not the specialized
  Qbar category, is the one the node requests here.
- `Sheaf.Paper.CompletedRlimFunctor`: `completedRlim`, `completedRlim_computation`;
  the existing total right derived functor of the strict inverse limit is used directly.
- `Sheaf.Paper.ReductionPullbackDerivedTower`:
  `CategoryTheory.StrictReduction.reductionPullbackDerivedTower`, with `IsNormalized`
  and its strict augmentation equation. The datum specialization used in the statement
  is the existing `AdicCoefficientDatum.reductionTowerPullbackIso` in
  `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.AugmentedDiagramProjectionMate`:
  `CategoryTheory.StrictReduction.augmentedDiagramProjectionMate` and
  `.augmentedDiagramProjection`. Their counit-adjoint construction specializes to the
  existing `AdicCoefficientDatum.towerProjection`, not a private projection map.
- `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`:
  `CategoryTheory.ringedConstantTowerPushforwardNormalization`, including the
  constant-unit, counit and derived-composite normalizations used in proof step 3.
- `Sheaf.Paper.CompletedDirectImageLimits`: `AdicCoefficientDatum.towerPush`,
  `.towerAdjunction`, `.directImageRlimIso`, `.reductionTowerPullbackIso`,
  `.towerProjection`, `.towerProjection_properties`. The last theorem already provides
  the second displayed identity; the new statement packages it with the pulled-unit
  and target-composite identities and square identification, so is not a duplicate.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: recorded `FixedEtaleOriginWitness`;
  its public import `Sheaf.Paper.RingedEtaleOriginWitness` supplies the retained
  `FiniteEtaleOriginWitness` used by the existing completed base-change construction.
- `Sheaf.Paper.StrictTowerExchangeMateNormalization`:
  `strictTowerExchangeMateNormalization`, `exchangeRealizationHPrime`; these use exactly
  projection followed by tower pushforward of inverse reduction/pullback comparison.
- `Sheaf.Paper.CompletedBaseChangeMap`: `AdicCoefficientDatum.completedBaseChangeMap`
  and `.completedExchange`, with their actual final inverse limit comparison.
- Proof-only `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image`, preserving all finite projections
  and transitions and supplying the identified completed coefficients.
- Proof-only `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: exports the
  general `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`, and
  `proEtaleRingDerivedAdjunction` used by the datum's pull, push and projection mate.
- Proof-only `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`, the normalized natural
  comparison of the two derived composites. Naturality is used at the augmentation
  and t inverse, rather than inferred from equality after evaluation.

No missing notion was encountered. In particular, neither a chosen cone comparison nor
an arbitrary map standing in for completion or projection was introduced.

### Edge cases checked before writing

- I=A: all positive quotients are the zero ring. The existing sheaf/tower definitions
  and zero derived categories still apply. No nontrivial-ring hypothesis excludes it.
- I=0 with finite A: quotients form the constant coefficient tower, transitions are
  identities, and the three equations reduce to constant-tower unit naturality.
- h=identity or p=identity: the specified identity/composition normalizations identify
  the equations with the corresponding canonical unit equations. No ad hoc identity
  isomorphism was substituted in the statement.
- Empty schemes and the zero object L are allowed. There are no nonemptiness or
  nonzero-object hypotheses. The finite-origin pairs are retained even in these cases.
- n=0 in Lean is the source's n=1. No quotient A/I^0 enters and A/I is retained.
- E0 and N need not be complete. The formulas only apply the completion unit to them,
  never invert it. General h and p may be nonproper.
- The tower lies in the derived category of strict diagrams, not the category of
  diagrams in a derived category; no faithfulness of derived evaluations is used.

### Searches

The prescribed msearch wrapper logged all four calls in `searches.jsonl` in this sandbox:

- LeanFinder: "Derived pushforward preserves the reduction tower augmentation and the
  completed pullback unit under the canonical inverse limit comparison". Eight hits:
  general derived comparison/factorization maps, derived adjunction units/counits,
  ordinary sheaf pushforward composition. None states the three normalized identities.
- Loogle: `CategoryTheory.Adjunction.unit, CategoryTheory.NatTrans`. One hit,
  `TopCat.adj₂_unit`; no match.
- Mathlib grep: `completion.*[Uu]nit|[Aa]ugment.*[Pp]rojection|[Pp]rojection.*[Aa]ugment`.
  Ten hits on ordinary adic completion and valued/adelic constructions, no match.
- LeanSearch: "Canonical derived pushforward inverse limit comparison preserves the
  quotient completion augmentation on strict towers of module sheaves". Eight hits
  on ordinary sheaf pushforward and pullback adjunctions and ordinary adic completion;
  no match.
- Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for completed
  target/augmentation, `ordinaryToCompleted`, and for the proposed declaration names;
  the item-id search in `lean/WeilConjectures` had no hits. No upstream declaration
  packages this statement. `CompletedSourceAugmentationNormalization` is its source-side
  sibling; `towerProjection_properties` gives just the second general equation.
  Reused all relevant published objects rather than defining them again.

No `STATEMENT-DISPUTED` fault found. No node statement or dependency record was changed.

### Validation

Ran the prescribed `scompile.py Q36 <item> <module>` against the live server build:
exit 0, both sandbox module (2.2 s) and library-path module (2.4 s) clean. No errors or
non-sorry warnings. Module mode, public exposure, explicit universe t and all variable
binders, 100-column limit, and sorry-only proofs were checked in the delivered file.

## Second reading by Q36

Performed a second clause-by-clause pass over the node and the final module, without
launching another agent, as required by the dispatcher. The maintainer performs the
independent review of this delivery.

The datum fields retain precisely the five coefficient conditions. The general theorem
has arbitrary h and p and complete L; its three conjuncts have the required endpoints
and arrows in diagrammatic order. In particular t is directed from pulled reduction to
reduction of pullback, so its inverse occurs only inside H prime. The second equation
uses c at R_U(E0), and the third uses c at Q. Neither equation silently uses c inverse.
The square theorem was checked against both `exchangeRealizationHPrime` and the exact
body of `completedBaseChangeMap`: the final comparison is c_Q inverse, with the same
pulled tower as in the general theorem. Properness and the retained finite etale pairs
are confined to this final specialization. The pairs impose no level compatibility.
No mismatch or further edit was found. The theorem statement is recorded verbatim in
the node's `lean.statement`; the supplemental square declaration is in `lean.declarations`.
