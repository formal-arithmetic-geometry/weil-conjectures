## Worker report

The module `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy` states
`CategoryTheory.cartanEilenberg_comparison_homotopy`, with one `sorry` proof and no
new definitions. The item's statement is unchanged. No new nodes or dependency
modules are needed.

Hypothesis and clause correspondence:

- The two abelian categories are independent universe-polymorphic `A : Type u₁`
  and `B : Type u₂`, with `Category.{v₁}`, `Category.{v₂}`, `Abelian A`, `Abelian B`,
  `EnoughInjectives A`, and `EnoughInjectives B`.
- The exact additive functor is `F : A ⥤ B` with `F.Additive`,
  `PreservesFiniteLimits F`, and `PreservesFiniteColimits F`. For additive functors
  between abelian categories this is exactly exactness, without requiring
  preservation of infinite limits or preservation of injectives.
- `K : CochainComplex A ℤ` and `L : CochainComplex B ℤ` are the given complexes.
  `hK` and `hL` say `IsZero` at every negative degree, exactly their stated bound.
- `I` and `J` have the recorded bicomplex shape `up ℤ`, `up ℕ`.
  `hIbelow` and `hJbelow` give horizontal vanishing below zero. The natural
  resolution index encodes vertical nonnegativity.
- `eI` and `eJ` are bicomplex morphisms from the complexes placed in resolution
  degree zero via `single₀`. These are the two augmentations.
- That they are Cartan--Eilenberg injective resolutions is rendered by exactly
  the conjunction fields of `exists_cartanEilenberg_resolution`: `hIcol` and
  `hJcol` are column quasi-isomorphisms; `hIinj`, `hJinj` are column term
  injectivity; `hIinj'`, `hJinj'` give injectivity of horizontal cycles, boundaries
  (`image (I.d (p-1) p)`) and homology in each resolution degree; `hIres`, `hJres`
  are the three induced augmentation quasi-isomorphisms. Thus these are the
  definition's data, not extra comparison hypotheses.
- `u u'` are maps from the functorially mapped `K` to `L`.
  `s : Homotopy u u'` specifies the given homotopy. Its adjacent components
  `s.hom p (p-1)` are precisely the node's `s^p`; `Homotopy.comm` is the
  stated equation `u-u' = ds+sd`.
- The let-bound `FI` maps both directions of `I` through the same functor `F`.
  The universally quantified `φ ψ : FI ⟶ J` are the given double-complex maps.
  The two following hypotheses are the augmentation equations at every `p`.
  `singleObjXSelf.inv` identifies the resolution-degree-zero object in a
  single complex with `K.X p` or `L.X p`, so the equations literally compare
  maps from `F.obj (K.X p)` to `(J.X p).X 0`.
- `E` extends the natural resolution index by zero to integers; `FIZ`, `JZ`
  are exactly those extended double complexes. Existential `tI`, `tJ` assert
  the existence of the diagonal coproducts, rather than assume additional
  completeness of either category. First-quadrant diagonals are finite.
- The conclusion's `H : Homotopy (total.map (E.map φ) ...) (total.map (E.map ψ) ...)`
  is the required total-complex homotopy. `Homotopy.comm` is equivalent to
  `Tot(φ)-Tot(ψ)=dH+Hd`, with Mathlib's same signed total differential.
- For every integer `q,n`, the existential `f` and its equation factor the
  restriction of `H.hom n (n-1)` through the target `secondFiltration` step
  `q-1`. This is exactly `H(F^q Tot^n) ⊆ F^(q-1) Tot^(n-1)` in an arbitrary
  abelian category, expressed without elements.
- The final same-map assertion is included by specialization `u'=u` and
  `s=Homotopy.refl u` (or `Homotopy.ofEq` of their equality). Its components
  are zero by definition. No separate theorem or stronger conclusion is needed.

Dependencies read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.EnoughInjectives`, `CategoryTheory.Injective`.
- `Sheaf.CategoryTheory.CartanEilenbergExists`:
  `CategoryTheory.exists_cartanEilenberg_resolution`; its full conclusion
  determines all resolution binders, with exactly the same augmentation maps.
- `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`:
  `CategoryTheory.cartanEilenberg_doubleComplex_homotopy`; directly imported
  and read in full, supplying the component construction described in the
  docstring and importing the required bicomplex, homotopy, extension and
  total-complex declarations.
- `Sheaf.CategoryTheory.DoubleComplexTotal`:
  `HomologicalComplex₂.secondFiltration`, with Mathlib's `HomologicalComplex₂`,
  `HomologicalComplex₂.total`, and `HomologicalComplex₂.total.map`.
- `Sheaf.CategoryTheory.Filtration`: `CategoryTheory.DecreasingFiltration`,
  its `step` field, and the subobject arrows used in the factorization.

Edge cases checked before writing: zero complexes, zero functor, zero comparison
maps, `u=u'`, and degree zero (whose homotopy target is degree -1). Extension by
zero handles the resolution-degree boundary; negative total degrees vanish.
The filtration quantifies all integers, including negative steps and empty
positive diagonals, and uses factorization through subobjects rather than an
assumption about elements. The two category and morphism universes are independent.
No hypothesis that F carries injectives to injectives is present or needed:
the double-complex dependency requires exact source resolutions and injective
TARGET resolutions.

Searches made on 2026-10-11:

- `msearch.py leansearch`: "Cartan Eilenberg comparison maps homotopic filtered
  total complex". Service unavailable (Internal Server Error).
- `msearch.py leanfinder`: "Homotopic maps lifted to Cartan Eilenberg resolutions
  induce total complex homotopies lowering the resolution filtration by one".
  Eight hits, all ordinary injective/projective resolution homotopies, including
  `CategoryTheory.InjectiveResolution.descHomotopy`. No bicomplex filtered theorem.
- `msearch.py loogle`: "Homotopy, HomologicalComplex₂". One hit,
  `HomologicalComplex.mapBifunctorMapHomotopy.comm₁_aux`; not this statement.
- `msearch.py grep`: "Cartan.Eilenberg|cartan.*eilenberg", `Algebra/Homology`.
  Zero Mathlib hits.
- `rg` in `WeilConjectures` and `lean/Sheaf` for Cartan--Eilenberg names and
  the item id: source only has descriptive spectral-sequence comments;
  project has the existence, functorial lift, properties, left-exact cohomology,
  vertical-nullhomotopy and double-complex-homotopy dependencies. None states
  the two-category exact-functor comparison uniqueness theorem.
- `rg` in `dag/lean_names_upstream.json` for the proposed declaration name:
  no collision. Read Mathlib's `Homotopy`, `equivSubZero`, `ofEq`, and `refl`
  definitions to check the orientation and the zero-homotopy specialization.

Source checked at https://stacks.math.columbia.edu/tag/015I and
https://stacks.math.columbia.edu/tag/015K (local derived.tex is absent on this
machine). These provide the Cartan--Eilenberg construction and its functoriality;
the detailed component homotopy is the previously reviewed dependency's statement
and proof. No statement dispute or correction is proposed.

Validation: server single-file compilation succeeded in 1.7 seconds with no
errors or warnings. Every theorem proof in the delivery is `sorry`; there are
no data definitions or auto-bound variables. The independent second reader is
to supply the second-reading section and perform delivery.

## Second reading by C1

I reread the node statement, its Stacks source place (Tags 015I and 015K),
the dependency declarations, and the delivered Lean file item by item.

- The two independent abelian categories are rendered by `A : Type u₁`,
  `B : Type u₂`, their independent category universes, `[Abelian A]`,
  `[Abelian B]`, `[EnoughInjectives A]`, and `[EnoughInjectives B]`.
  Verdict: exact match; no finiteness, Noetherian, or universe restriction is added.
- The exact additive functor is `F : A ⥤ B` with `[F.Additive]`,
  `[PreservesFiniteLimits F]`, and `[PreservesFiniteColimits F]`.  In abelian
  categories this is the finite-limit/finite-colimit formulation of exactness.
  Verdict: exact match; preservation of injectives or infinite limits is not assumed.
- The complexes and their nonnegative bounds are `K`, `L`, `hK`, and `hL`.
  Verdict: exact match, including all integer degrees and the zero-complex case.
- The Cartan--Eilenberg resolutions are the explicitly introduced bicomplexes
  `I`, `J`, augmentations `eI`, `eJ`, and the complete conjunction fields
  `hIbelow`, `hIcol`, `hIinj`, `hIinj'`, `hIres` and their `J` analogues.
  These fields are exactly the conclusion fields of
  `exists_cartanEilenberg_resolution`, including cycles, boundaries, homology,
  and all three induced augmentation quasi-isomorphisms.  Verdict: exact match.
- The homotopic maps are `u`, `u'`, and `s : Homotopy u u'`; the augmentation
  equations for `φ` and `ψ` are the two displayed universal equations over all
  `p : ℤ`.  The `singleObjXSelf` inverses make the degree-zero terms literally
  the augmented maps in the node.  Verdict: exact match and correct composition.
- `FI`, `E`, `FIZ`, and `JZ` are the functor image and extension-by-zero
  complexes used for the total construction.  The existential `tI`, `tJ`
  states precisely existence of the finite diagonal coproducts and introduces
  their `HasTotal` instances.  Verdict: exact match; no completeness assumption
  is hidden.
- The conclusion is the existential `H : Homotopy` between the two total maps,
  followed by the factorization through
  `(JZ.secondFiltration (n - 1)).step (q - 1)` for every integer `q,n`.
  This is the element-free rendering of
  `H(F^q Tot^n) ⊆ F^(q-1) Tot^(n-1)`, with the same second (resolution-degree)
  filtration and degree shift.  Verdict: exact match.  The node's final
  “in particular” clause is the specialization of the preceding universal
  assertion to `u' = u` and the zero homotopy; it is therefore already implied
  without adding a redundant second conclusion.

Edge cases checked: empty/zero complexes and zero comparison maps; `u = u'`;
`n = 0` and negative total degrees; resolution degree zero and extension by
zero at negative degrees; empty positive diagonals; arbitrary integer `q` and
`n`; and all four independent category/type universes.  No characteristic,
Noetherian, or nonzero-object hypothesis occurs in the node or Lean.

I searched Mathlib and the project/source with `msearch.py` LeanSearch,
LeanFinder, Loogle, and `rg` for Cartan--Eilenberg comparison homotopies,
filtered total homotopies, and the declaration name.  The only related hits
were generic injective-resolution homotopies and bicomplex infrastructure;
there is no existing declaration with this statement.  The dependency modules
were opened and their signatures match the fields used here.

No mismatch was found in this independent reading, so no Lean or node repair
was required.  The worker's stale note that the second reading was still
missing is addressed by this section.  Compilation with `scompile.py` succeeds
with the sole allowed `sorry` proof and no warnings.
