## Worker report

Item: lem-sfb-coefficient-heart-curve-lisse-descent. Group NZ, stage 2, 2026-10-22.
The live item has Q75's reviewed stage-1 split and no Lean record; this delivery adds its
stage-2 statement without resplitting or changing the statement or any dependency.
There is no repair note for the item. The preserved sandbox contained only dispatcher
brief markers, with no prior Lean module or node copy to recover.

Module: `Sheaf.Paper.CoefficientHeartCurveLisseDescent`.
Main declaration: `AlgebraicGeometry.ProEtale.coefficientHeart_curve_lisse_descent`.
Its sole theorem proof is `sorry`. Two explicitly constructed isomorphisms are helpers
of this same node, recorded in lean.declarations: `coefficientHeartFiniteFreePullbackIso`
and `coefficientHeartRefinementPullbackIso`. They introduce no independent mathematical
notion and have real data, using existing biproduct, scalar-change, coefficient, and
composition comparisons; there is no arbitrary isomorphism choice or postponed helper
obligation. Nothing is proved in this delivery.

Hypothesis and clause correspondence:

- Schemes T and W: `{W T : Scheme.{u}}`. The morphism is `t : T ⟶ W`.
- Surjective closed immersion: `[IsClosedImmersion t] [Surjective t]`, exactly the
  two recorded Mathlib predicates. There is no nilpotence or finiteness condition.
- Arbitrary commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the underlying-ring-object
  presentation of the dependency's `Profinite.CondensedRing` (which is `Mon` of these
  sheaves); it does not require a presentation by a topological or discrete ring.
- Small pro-etale sites: every module lives in `Sheaf (Scheme.ProEt.topology Y)
  Ab.{u + 1}`. Object and morphism universes of the site retain the framework's
  existing sizes; no equality of these universes is imposed.
- Pulled-back coefficient rings: `condensedRingObj Λ Y`, the recorded p_Y^*Λ.
- M: `Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)`.
- Actual inverse image: every occurrence is `CondensedRing.upperStar Λ f`, the
  dependency's mapMod followed by extension along `condensedPullbackHom`.
- Lisse iff: the first conjunct is literally `IsLisseCoefficientModule Λ M ↔
  IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ t).obj M)`. The recorded
  definition uses a pro-etale cover and `Mod.IsFree`, which the upstream Free module
  defines as existence of an isomorphism to a *finite* direct sum `Mod.finiteFree`.
- Given covering: universally quantified `C : Scheme.Cover.{v}
  Scheme.proetalePrecoverage T`. Independent universe v allows arbitrary-sized
  indexed families; no smallness hypothesis was added to the input.
- Given ranks and specified trivializations: `r : C.I₀ → ℕ` and the actual family
  `φ : ∀ a, (upperStar Λ (C.f a)).obj ((upperStar Λ t).obj M) ≅
  Mod.finiteFree (condensedRingObj Λ (C.X a)) (r a)`.
- Output covering: `∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage W`.
  The u-small choice loses no case: retain finitely many covering witnesses for
  each affine open of T, as in live proof step 3, before applying cover refinement.
- Each b chooses a(b): `∀ b : B.I₀, ∃ a : C.I₀`.
- T_b is the actual chosen fibre product `pullback (B.f b) t`; its projections
  are `pullback.fst (B.f b) t` and `pullback.snd (B.f b) t`.
- Refinement map over T: `f : pullback (B.f b) t ⟶ C.X a` and the existential
  witness `hf : f ≫ C.f a = pullback.snd (B.f b) t`.
- Lifted isomorphism of the prescribed rank: existential `ψ :
  (upperStar Λ (B.f b)).obj M ≅ Mod.finiteFree (condensedRingObj Λ (B.X b)) (r a)`.
- Compatibility is an equality of actual module morphisms. Its left side is
  `t_b^*(ψ.hom) ≫ κ(t_b,r a).hom`. Its right side is
  `γ.hom ≫ f^*((φ a).hom) ≫ κ(f,r a).hom`.
  Here κ is `coefficientHeartFiniteFreePullbackIso`, defined by mapBiproduct,
  extension/restriction along the inverse of alpha, and `Mod.regularIsoOfIsIso`.
  Its underlying regular comparison is alpha, so this fixes the Cartesian
  coefficient identification, including the finite-free basis normalization.
  The γ is `coefficientHeartRefinementPullbackIso`, formed from upperStarComp,
  equality transport for the commuting square, and another upperStarComp.
  The supplied square equality is the pullback condition followed by hf under
  postcomposition with t. Thus the original chosen φ, not merely some
  trivialization on its target, occurs in the conclusion.
- Rank zero, nonuniform ranks, arbitrary schemes, and arbitrary commutative
  condensed coefficients are admitted. No reducedness, Noetherianity,
  connectedness, rank bound, or nilpotence bound is present.

Dependency declarations used (full names have prefix AlgebraicGeometry.ProEtale
unless another namespace is given):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; its public
  underlying-ring-object convention is used without a second definition.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`,
  `condensedPullbackHom`, `isIso_condensedPullbackHom`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar` and `CondensedRing.upperStarComp`. The latter is
  also the specialized actual composition comparison supplied by the aggregate
  pushforward-pullback dependency; no abstract adjunction is substituted for it.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.condition`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `Scheme.ProEt.topology`, `Scheme.proetalePrecoverage`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `CategoryTheory.Mod.finiteFree`;
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`:
  `CategoryTheory.Mod.extendScalarsIsoComapInv`; and its public import
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`: `Mod.regularIsoOfIsIso`.

All stated proof dependencies' modules are imported. These include
`Sheaf.CategoryTheory.MonoidalFiniteFreeTransport` (Functor.monoidalFiniteFreeTransport),
`Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` (sfbCoefficientSectionsLocalization),
`Sheaf.Paper.CondensedSurjectiveClosedEquivalence`
(condensedSurjectiveClosedPullback_isEquivalence),
`Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`
(Scheme.exists_cover_refinement_surjective_closed), and
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
The Mathlib weakly-etale and fpqc-covering modules supply the remaining recorded
Mathlib proof-dependency matches. No dependency interface required repair.

Edge cases checked before writing: rank 0 is the empty biproduct, and mapBiproduct
also covers the empty finite index. The zero ring does not require uniqueness of
rank. Empty W and T permit empty covers. If an input cover has no members, T is
empty and surjectivity forces W empty, so no index a must be chosen. Identity
immersions, nonreduced schemes, and nil ideals with no uniform nilpotence bound
are all included. Input index universes are independent of u and can exceed it.

Searches actually run through the prescribed msearch.py wrapper:

- LeanFinder: "A condensed coefficient module is locally finite free if and only
  if its pullback by a surjective closed immersion is locally finite free, with
  compatible lifted trivializations". Eight hits, including Condensed.finFree,
  Condensed.free and light-condensed projectivity criteria. None states descent
  or its compatible prescribed refinement for internal condensed coefficients.
- Loogle: "CategoryTheory.Mod, CategoryTheory.Functor.IsEquivalence". Zero hits.
- Mathlib grep, AlgebraicGeometry: "finiteFree|IsLisse|surjective.closed". One hit,
  a comment about a surjective closed immersion into a reduced scheme being an
  isomorphism; no match to this assertion without reducedness.
- LeanSearch: "Descent of locally finite free internal condensed coefficient
  modules on the pro etale site through a surjective closed immersion". Eight
  hits, including Condensed.free, Condensed.finFree and scheme flat-descent
  declarations. These concern discrete coefficient free constructions or
  different scheme properties and do not state this theorem.
- Source rg in lean/WeilConjectures and lean/Sheaf by the node id, lisse/closed
  terms, IsLisseCoefficientModule, finiteFree, and the proposed declaration
  names; also grep -rn of the exact item id in WeilConjectures. No declaration
  states the item. Existing lisse-restriction/common-stratification material
  gives forward pullback or special coefficients, not the converse with these
  specified compatible trivializations. Existing generic geometric refinement
  and condensed-module equivalence are reused as proof dependencies.

Sources read: all statement-dependency nodes and their recorded declarations and
docstrings, the six live proof steps, the current blueprint unit and proof page,
and Stacks proetale.tex lemma-thickening (09AB). The node's source.place refers to
step 9 of proof.md, whereas the curve paragraph is in _section.md as its
blueprint.from correctly records; this is an inherited bibliographic locator
fault, not a change to the theorem. The supporting Stacks theorem is the general
topological-invariance input; the live proof assembles its coefficient and
prescribed-trivialization consequences from the cited existing tools.
No mathematical statement dispute or statement correction is needed.

Validation: prescribed scompile.py compiled both its sandbox probe and the actual
module successfully (12.6 s and 9.7 s), with no errors or warnings. autoImplicit is
explicitly false; every universe and binder is declared; all lines are at most
100 characters. The dry run and push results are recorded below when run.

## Second reading by NZ

I reread the live node and the delivered Lean in a separate checking pass. This
is a same-worker pass: the dispatcher explicitly prohibits starting another
agent, and the maintainer supplies the independent review after delivery.
The closed-immersion and surjectivity predicates, arbitrary commutative condensed
input, actual module pullback, and original lisse predicate agree with the live
statement. The second conjunct retains the input cover and its actual isomorphisms,
not just existence of lissity. I checked the domains of both sides of the final
equality: both start at t_b^* b_b^* M and end at the free rank-r_a module on the
actual fibre product. The right side runs through f^* c_a^* t^* M, and hf plus
pullback.condition supplies exactly the commuting-square comparison. The finite
free helper uses the actual coefficient alpha and finite-biproduct comparison.
The two definitions contain no sorry and no arbitrary choice of an isomorphism.
The only sorry is the full combined theorem matching this one DAG statement.
No added assumptions or omitted clauses were found, and no correction was made.

Delivery dry run: `deliver2.py NZ lem-sfb-coefficient-heart-curve-lisse-descent --no-push`
printed `OK (dry run)` for commit 53cd520ec08: preflight and compilation passed;
nothing was pushed by the dry run.
