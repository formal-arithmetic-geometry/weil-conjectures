## Worker report

The module `Sheaf.CategoryTheory.AbsoluteTraceExchange` states
`CategoryTheory.absoluteTraceExchange`, with `sorry` as its only proof. Three real-data
helper definitions give exactly the maps already specified by the node:
`absoluteTraceExchangeTrace`, `absoluteTraceExchangeMap`, and
`absoluteTraceExchangeHomEquiv`. They are recorded in `lean.declarations`. No new nodes,
dependency repairs, or statement corrections are needed. No statement is disputed.

Hypotheses, in the order of the node:

- Locally small symmetric monoidal categories C_X and C_Y are `X : Type uX`,
  `Y : Type uY`, `[Category.{vX} X]`, `[Category.{vY} Y]`, `[MonoidalCategory X]`,
  `[SymmetricCategory X]`, and the corresponding Y instances. All six object/morphism
  universes, including those for S, are independent and explicitly declared. There is
  no small-category restriction or imposed universe equality. Mathlib's `β_` is the
  stipulated symmetry, with naturality, involutivity and hexagons.
- The locally small category S and its object Ω are `S : Type uS`,
  `[Category.{vS} S]`, `(Ω : S)`.
- P_T, A_T and their specified Hom adjunctions are `PX`, `AX`, `PY`, `AY`,
  `(adjX : PX ⊣ AX)` and `(adjY : PY ⊣ AY)`. Mathlib adjunctions give the specified
  natural Hom equivalences and counits, equivalently to the node's convention.
  The dualizing objects are literally `AX.obj Ω` and `AY.obj Ω`; the traces are
  `adjX.counit.app Ω` and `adjY.counit.app Ω`.
- The internal-Hom contravariant functors are `DX : Xᵒᵖ ⥤ X` and `DY : Yᵒᵖ ⥤ Y`.
  Evaluation is `evX` and `evY`. The specified bijections are the families of
  equivalences `eX W M` and `eY W M`. Hypotheses `hX` and `hY` say precisely that
  each forward map sends v to `(v ⊗ₘ 𝟙 M) ≫ ev M`.
  Their naturality in W follows from this formula and the tensor composition law:
  substituting `f ≫ v` gives `(f ⊗ₘ 1) ≫ e W M v`. Their naturality in M is
  exactly the evaluation naturality equalities `hXM` and `hYM`, together with that
  formula. Conversely, naturality of the stipulated bijections in M, evaluated on
  the identity of D(M), gives those evaluation equalities. Thus this encoding neither
  adds nor drops a hypothesis, and requires no internal Hom into other targets.
- The functors F and U, the right adjoint R of U, and its ordinary counit are
  `{F : X ⥤ Y}`, `{U : Y ⥤ X}`, `{R : X ⥤ Y}`, `(adj : U ⊣ R)`,
  and `adj.counit.app`. There is no right adjoint of F among the assumptions.
- The compact-support composition isomorphism κ is `(κ : F ⋙ PY ≅ PX)`;
  Mathlib composition writes the first functor first, so this is exactly P_Y F ≅ P_X.
- The projection isomorphisms are
  `θ : ∀ M W, F.obj M ⊗ W ≅ F.obj (M ⊗ U.obj W)`.
  Their two naturality squares are `hθW` and `hθM`. A family of isomorphisms
  with these two squares is exactly a natural isomorphism of the stated bifunctors.

Definitions and conclusions, clause by clause:

- `absoluteTraceExchangeTrace` is `adjY.homEquiv _ Ω` applied to
  `κ.hom.app (AX.obj Ω) ≫ adjX.counit.app Ω`. This is exactly τ in the node.
- `J_M` is written explicitly as `R.obj (DX.obj (op M))`.
- `absoluteTraceExchangeMap` applies the inverse Y evaluation equivalence to
  the node's λ_M. Reading Lean's composition left to right, its factors are
  σ_(J_M,FM), θ_(M,J_M), F(1_M ⊗ ε_(D_X M)), F(σ_(M,D_X M) ≫ ev_(X,M)), τ.
  They are the displayed factors of λ in the exact stated order.
- `absoluteTraceExchangeHomEquiv M W` is the displayed six-step bijection Φ.
  The first step is `eY`; the second is the inverse absolute Y adjunction;
  the third is `Iso.homFromEquiv` of
  `PY.mapIso ((β_ W (F.obj M)) ≪≫ θ M W) ≪≫ κ.app (M ⊗ U.obj W)`;
  the fourth is the absolute X adjunction; the fifth is symmetry followed by
  `eX.symm`; the last is the ordinary adjunction `adj.homEquiv`.
  The third step therefore uses exactly the q specified by the node, and its
  forward direction precomposes with q inverse, as required by the displayed types.
- The theorem's first conjunct asserts `IsIso` of E_M for every M.
- The second conjunct asserts contravariant naturality: for `a : M' ⟶ M`,
  `R.map (DX.map a.op) ≫ E_M' = E_M ≫ DY.map (F.map a).op`.
  This is the node's naturality square in Lean composition order.
- The final conjunct quantifies over every M, W and `h : W ⟶ J_M` and asserts
  `Φ.symm h = h ≫ E_M`, precisely the more specific inverse-bijection clause.
  In particular Φ inverse is natural in W because it is postcomposition by E_M.
  Contravariant naturality in M follows from the preceding conjunct.

Dependencies read and used:

- `def-sfb-monoidal-category` is the Mathlib leaf
  `CategoryTheory.MonoidalCategory`, in `Mathlib.CategoryTheory.Monoidal.Category`.
  Its full structure and docstring were read (tensor structure at lines 87–107,
  laws at 162–210); it is reexported by the public braided-category import.
- `lem-galois-yoneda-fully-faithful` is the proof-only Mathlib leaf
  `CategoryTheory.Yoneda.fullyFaithful`, in `Mathlib.CategoryTheory.Yoneda`.
  Its docstring and implementation at lines 133–141 were read; the module is
  imported without `public` for the seventh proof step.
- The signatures and source of `Adjunction.homEquiv`, the adjunction counit
  interface, `SymmetricCategory`, `BraidedCategory`, `Iso.homFromEquiv`, and
  `Iso.homToEquiv` were read in Mathlib. There is no private copy of any notion.
- The source blueprint file named by the node was opened: paragraph 1 uses exactly
  the exchange `Rf_* D_X K ≅ D_Y Rf_! K` as its third Hom bijection. The item is
  its already reviewed generic categorical extraction, not the unit's statement.
- No repair note for this item exists in `coord/repair-notes`.

Edge cases checked mathematically before drafting:

- Identity functors, identity absolute adjunctions, and identity κ, θ give τ=id
  and E=id under the specified evaluation bijections. The Hom chain also reduces
  to identity after its two symmetry steps.
- For identity functors on vector spaces with κ=d·id and θ=c·id, for nonzero
  scalars c,d, E=cd·id. The Hom chain is multiplication by (cd) inverse, confirming
  that neither θ nor κ is inverted in the exchange arrow itself.
- A zero dualizing object yields zero internal Homs in an additive example and
  an isomorphism between zero objects, so no nonzero condition is needed.
- The formulation assumes neither a tensor-unit Ω in S nor a monoidal structure
  on S. It applies to arbitrary Ω, arbitrary M and W, with no biduality assumption.
- Empty categories cause no illicit choices: Ω forces S to have an object and
  the stipulated A functors then provide the two dualizing objects.

Searches for reuse:

- `msearch.py leanfinder`, query “Verdier exchange from absolute trace adjunctions
  and a projection formula in symmetric monoidal categories”: 8 hits, including
  `tensorRightHomEquiv`, `tensorLeftHomEquiv`, `frobeniusMorphism_mate`,
  `tensorLeftAdjunction` and `tensorRightAdjunction`. They concern rigid dual
  pairings or Cartesian comparisons, not the given absolute adjunctions and map.
- `msearch.py loogle`, query `CategoryTheory.Adjunction, CategoryTheory.MonoidalClosed`:
  12 hits, including `MonoidalClosed.ofEquiv`, `internalHomAdjunction₂_adj`,
  `expComparison_iso_of_frobeniusMorphism_iso` and reflective-closed constructions.
  None gives this statement. The source of `Monoidal/Closed/Functor.lean` was read:
  its comparison requires Cartesian tensor and full closedness.
- `msearch.py leansearch`, query “Absolute trace adjunctions and a projection formula
  induce the Verdier exchange isomorphism”: 8 unrelated sheaf pullback,
  absolute Kan and derived-adjunction hits, no match.
- `msearch.py grep`, query `absoluteTraceExchange|frobeniusMorphism|expComparison`
  in `CategoryTheory`: 10 hits in regular-category and Cartesian closed-functor
  modules; no absolute trace exchange.
- `rg` across project source and `lean/Sheaf` for
  `absoluteTraceExchange|absolute.trace.exchange|Verdier.exchange|frobeniusMorphism|expComparison`
  found the geometric `properAmbientVerdierExchangeMap`, derived-six-functor package
  fields, and the lax monoidal `ihomComparison`. These require geometric/proper or
  fully closed monoidal data and do not give this generic statement.
- `grep -rn lem-sf-absolute-trace-exchange` in upstream `WeilConjectures`: no hit.
  `rg` for all four proposed declaration names in upstream names, Mathlib,
  upstream source, and side-project source: no hit.

Validation: `scompile.py NS lem-sf-absolute-trace-exchange` compiled the single
module cleanly in both sandbox and library contexts, with no errors or warnings.
All definitions have actual data; the sole postponed theorem carries the complete
seven-step node proof in its docstring. Every variable and universe is explicit;
there are no local notations, local instances, hidden choices, or extra nodes.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
