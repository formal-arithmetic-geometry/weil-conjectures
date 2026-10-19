## Worker report

The module `lean/Sheaf/Paper/IndHeartFullFaithfulness.lean` states
`AlgebraicGeometry.ProEtale.indHeart_fullFaithfulness`. It uses the exact condensed
coefficient ring choices from the node: the hypothesis `hΛ` says that the point coefficient
sheaf is either `Profinite.continuousMapRingObj E` for a finite intermediate extension or
`Profinite.padicAlgClRingObj ℓ`. The scheme hypotheses are `[IsLocallyNoetherian X]` and
`[CompactSpace X]`, matching locally Noetherian and quasi-compact. The module also supplies the
canonical `MonObj (condensedRingObj Λ X)` instance transported by
`Functor.monObjObj` along `upperStarFromPoint`; this is the ring-object structure required by
`sk-def-sfb-pulled-back-coefficients`, not an additional mathematical hypothesis.

The first conjunct is `∀ C, IsFinitelyPresentable (C.1 : M)`, where `M` is the category of
internal modules over `condensedRingObj Λ X`. Mathlib's `IsFinitelyPresentable` is precisely
preservation of all filtered colimits by `Hom(C, -)`, hence renders the displayed canonical
filtered-colimit Hom map in clause 1. The existential second conjunct supplies a functor
`Φ : Ind Cons ⥤ M`; `Φ.Full ∧ Φ.Faithful` renders full faithfulness. For every ind-object `Z`,
`Nonempty (IsColimit (Φ.mapCocone (colimit.cocone
((Ind.presentation Z).F ⋙ Ind.yoneda))))` says that its image is the actual ambient colimit
of the presentation diagram. Finally, for each ambient module `M`,
`Φ.essImage M ↔ ObjectProperty.ind (IsConstantModelConstructible Λ X) M` identifies the
essential image with the replete filtered-colimit closure `IndCons`.

Dependency declarations used:

- `pqf-def-locnoeth`: Mathlib `AlgebraicGeometry.IsLocallyNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-quasi-compact-scheme`: Mathlib `CompactSpace` from
  `Mathlib.Topology.Defs.Filter` (the scheme's underlying topological space).
- `sk-def-sfb-condensed-ring`: the condensed coefficient sheaf interfaces imported by the
  upstream ProEtale module framework.
- `sk-def-sfb-qlbar-condensed`: `Profinite.padicAlgClRingObj`.
- `sk-def-sfb-pulled-back-coefficients`: `AlgebraicGeometry.ProEtale.condensedRingObj` and
  `upperStarFromPoint`; the module's helper instance is the transported monoid object.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod`.
- `sk-def-sfb-constructible`: `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  its module `Sheaf.Paper.CondensedConstantConstructibility`.
- `def-weil-pbc-category-colimit`: Mathlib `colimit`, `colimit.cocone`, and `IsColimit`.
- `def-weil-size-convention`: explicit universe `u` and the Mathlib Ind size convention.

Edge cases checked: `IsFinitelyPresentable` quantifies over arbitrary small filtered diagrams,
including the terminal one and zero objects; `ObjectProperty.ind` uses nonempty filtered index
categories as required by Mathlib's `IsFiltered`; `Ind.presentation` handles every ind-object,
including representables; the coefficient disjunction includes both finite extensions and the
algebraic closure; no characteristic or nonzero assumption was introduced; the universe is the
single site universe `u` from the size convention.

Searches made before writing:

- `msearch.py leanfinder "constructible sheaves finitely presented full faithfulness Ind
  category"`: only generic finite-presentation/Ind candidates, no whole-item declaration.
- `msearch.py leanfinder "A fully faithful embedding of finitely presentable objects extends
  to a fully faithful realization of the ind completion by filtered colimits"`: generic
  `CategoryTheory.Ind.inclusion` and accessibility results, no coefficient realization.
- `msearch.py loogle "\"Ind\", \"fullyFaithful\""`: generic `Ind.yoneda`/`Ind.inclusion`
  declarations only.
- `msearch.py grep "Ind|finitely.presented|filtered.*colimit" Mathlib`: Indization and
  generic category results only.
- `rg` over `WeilConjectures/` and project `lean/Sheaf`: no declaration of this constructible
  heart theorem; related filtered-colimit theorem is separate and does not give finite
  presentation or full faithfulness.
- Read Mathlib `CategoryTheory/Limits/Indization/Category.lean`,
  `CategoryTheory/Presentable/Finite.lean`, `CategoryTheory/ObjectProperty/Ind.lean`, and
  `CategoryTheory/EssentialImage.lean`; none states this coefficient-specific result.

## Second reading by Q14

I reread the node statement and the source proof paragraphs. The Lean binders retain the prime,
locally Noetherian, quasi-compact, coefficient choice, and module category. Clause 1 is rendered
by `IsFinitelyPresentable`; clause 2 is rendered by the existential `Φ`, its Full/Faithful
fields, the mapped canonical filtered-colimit cocone, and the `essImage` equivalence. The
constructible dependency is imported from its recorded module without copying its definition.
The helper monoid instance is canonical transport along `upperStarFromPoint`, needed only to
make the recorded module category elaborate. The file compiles cleanly with `scompile.py`.

## Maintainer review fix (stage-2 review of head 0b1c0a21e32e)

The delivered statement was right in its route but not typed as the node says; the maintainer
reviewer repaired it in place (same module, same theorem name):

1. Universes. `#check` with `pp.universes` showed `indHeart_fullFaithfulness.{u_1, u_2, u_3}`:
   `IsFinitelyPresentable.{u_2}` and `ObjectProperty.ind.{u_3}` were unbound, so clause 1 was
   claimed for filtered diagrams of every size and the essential image was compared with
   filtered colimits of every size. Both are now `.{u + 1}`, the hom universe of
   `Mod_{Λ_X}` and the index universe of `CategoryTheory.Ind` (small diagrams of
   def-weil-size-convention), as in the landed sibling det-ind-heart-filtered-colimits.
2. Coefficients. `[MonObj Λ] [IsCommMonObj Λ]` were free instance binders while `hΛ` only
   equated the underlying abelian sheaf with `continuousMapRingObj E` or
   `padicAlgClRingObj ℓ`, so the ring structure was arbitrary. The assertions are now the
   definition `IndHeartFullFaithfulnessAssertions Λ X` and the theorem states them for
   `Profinite.continuousMapRingObj E` (every `E : PadicAlgCl.FiniteIntermediateField ℓ`) and
   for `Profinite.padicAlgClRingObj ℓ`, with their canonical instances.
3. Realization. `∃ Φ` with presentation-colimit preservation only said that `Φ Z` is the colimit
   of `Φ (Ind.yoneda C_i)`, not of `C_i`. Added `Nonempty (Ind.yoneda ⋙ Φ ≅ ObjectProperty.ι Cons)`;
   with the colimit clause this pins `Φ` to the realization `"colim" C_i ↦ colim C_i` up to
   isomorphism, as the node says.
4. The global instance `monObj_condensedRingObj` duplicated the canonical scoped instance
   `Functor.monObjObj` (`open scoped CategoryTheory.Obj`), which is now used instead.

Compiled with `tools/nt_compile.py` (side overlay): clean, only the `sorry`; `#check` shows the
single universe `u`.
