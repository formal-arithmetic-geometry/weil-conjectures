## Worker report

Existing attachment: `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`
in `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction`, lines 86–105.
The unit and counit clauses are supplied by the same module's
`mapOfNatIsoAdjunction_unit_app_hom_f` (108–110) and
`mapOfNatIsoAdjunction_counit_app_hom_f` (113–115), all listed in `lean.declarations`.
No new module, definition, node, or theorem is needed. Only the item's `lean` changes.
No repair note exists for this item. There is no statement correction or disputed statement.

Read the node's whole statement, its six proof steps, its source module and the two
statement-dependency nodes and their Mathlib matches. The source is precisely the place
cited by the node, not merely a related adjoint-lifting theorem.

Hypotheses and clauses, individually:

- Categories C and D: upstream variables `{C : Type u} [Category.{v} C]`
  and `{D : Type u'} [Category.{v'} D]`; the four universes are independent.
- Functors L and R: `{L : C ⥤ D} {R : D ⥤ C}`.
- The specified adjunction with its unit and counit: `(adj : L ⊣ R)`,
  `adj.unit`, `adj.counit`; neither transformation is required to be invertible.
- Endofunctors F and G: `{F : C ⥤ C} {G : D ⥤ D}`.
- Fixed pairs: `IsoAlgebra F`, `IsoAlgebra G`. In
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`, lines 110–135,
  `Algebra.IsIsoStr F` is `fun A ↦ IsIso A.str`, and `IsoAlgebra F` is its
  full subcategory. This is definitionally the precise full subcategory in
  `def-weil-endofunctor-fixed-pair-category.mathlib_match`, not a private replacement.
  Mathlib's `Algebra.Hom.h` is `F.map f ≫ A₁.str = A₀.str ≫ f`, namely the
  node's commuting square. Its faithful forgetful functor is the full-subcategory
  inclusion followed by `Algebra.forget F` (upstream lines 149–150, 192–200).
- The exchange isomorphisms e and b: `(eL : L ⋙ G ≅ F ⋙ L)` and
  `(eR : R ⋙ F ≅ G ⋙ R)` at source line 41. Lean functor composition is
  diagrammatic, exactly as the node explicitly specifies.
- The mate assumption is source line 42:
  `(h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom)`.
  The square has horizontal functors F and G and L on both vertical sides.
  Expanding `mateEquiv` from `Mathlib.CategoryTheory.Adjunction.Mates`
  (lines 95–113) gives at M, in diagrammatic order,
  `adj.unit.app (F.obj (R.obj M)) ≫ R.map (eL.inv.app (R.obj M)) ≫
  R.map (G.map (adj.counit.app M))`, precisely the displayed component of b.
  Thus this uses `def-weil-pbc-adjunction-mate`'s recorded `CategoryTheory.mateEquiv`.
- Left transport: `mapOfNatIso eL`. In the upstream Mathlib extension module above,
  lines 280–296, its carrier is `L.obj K.carrier`, its structure is
  `eL.app K.carrier ≪≫ L.mapIso K.str`, and its carrier map is `L.map φ.hom.f`.
  These are exactly `(LK, L(θ) ∘ e_K)` and L acting on morphisms.
- Right transport: the same existing `mapOfNatIso` with L replaced by R,
  F by G, G by F, and eL by eR. Its structure is
  `eR.app M.carrier ≪≫ R.mapIso M.str`, giving `(RM, R(ψ) ∘ b_M)`;
  its carrier map is R applied to the original carrier map.
- Adjointness: the attached declaration returns
  `mapOfNatIso eL ⊣ mapOfNatIso eR`, with actual adjunction data.
- Unit as a fixed-pair morphism: the constructed component is
  `ObjectProperty.homMk ⟨adj.unit.app K.carrier, map_unit_app_comp_str ...⟩`.
  The listed unit lemma says its `.hom.f` is exactly `adj.unit.app K.carrier`.
- Counit as a fixed-pair morphism: the analogous construction uses
  `map_counit_app_comp_str`; the listed counit lemma identifies `.hom.f` with
  `adj.counit.app M.carrier`. Equalities are literal, not up to an isomorphism.
- No equivalence hypothesis: the construction and both lemmas precede
  `section Equivalence` (148) and `[F.IsEquivalence] [G.IsEquivalence]` (150).
  No additive, abelian, exactness, nonempty-category or size hypothesis is present.

Dependency declarations used: `CategoryTheory.Endofunctor.Algebra` and
`CategoryTheory.Endofunctor.Algebra.Hom` from
`Mathlib.CategoryTheory.Endofunctor.Algebra`; the full-subcategory construction from
`Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`; the identical upstream
`CategoryTheory.Endofunctor.IsoAlgebra`, its `forget` and `mapOfNatIso` from
`WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`; and
`CategoryTheory.mateEquiv` from `Mathlib.CategoryTheory.Adjunction.Mates`.
The proof leaf `lem-weil-pbc-adjunction-of-natural-bijection` records
`CategoryTheory.Adjunction.mkOfHomEquiv` in `Mathlib.CategoryTheory.Adjunction.Basic`;
read its `CoreHomEquiv` and construction at 351–454. The already proved source instead
uses the equivalent unit-counit constructor; attaching it does not require redoing its proof.

Edge cases checked: identity endofunctors and identity adjunction; empty categories
(no nonemptiness assumption); non-equivalence endofunctors (for example, the constant
singleton endofunctor on sets with the identity adjunction and identity exchanges);
non-invertible adjunction units/counits (diagonal adjoint to product, identity F and G).
All are covered by the same signature. The mate of an isomorphism is not generally
invertible; the hypothesis supplying the isomorphism eR is retained in full.

Searches actually run through `msearch.py NK lem-sf-fixed-pair-adjunction-lift`:

- LeanFinder: "An adjunction lifts to categories of fixed pairs for endofunctors with
  invertible mate exchange". Eight results, including `mateEquiv`, `mateEquiv_apply`,
  `mateEquiv_counit`, `unit_mateEquiv` and general adjoint-lifting maps; none states
  the whole fixed-pair adjunction in Mathlib.
- Loogle: `CategoryTheory.mateEquiv`. Twelve results concerning mates and their
  identities, confirming the recorded mate interface.
- grep: `mapOfNatIsoAdjunction|IsoAlgebra`. One unrelated Mathlib result,
  `algEquivIsoAlgebraIso` in `Algebra/Category/AlgCat/Basic.lean:243`.
- LeanSearch: "An adjunction lifts to invertible endofunctor algebras when the
  exchange isomorphisms are mates". Eight results, primarily
  `algebraCoalgebraEquiv` and its subsidiary declarations, plus `mateEquiv`;
  none states the whole item in Mathlib.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `lem-sf-fixed-pair-adjunction-lift|mapOfNatIsoAdjunction`: the exact source
  construction and its unit/counit lemmas occur in the module attached above,
  together with existing consumers; no corresponding Sheaf declaration was found.
  The explicit node-id grep in `lean/WeilConjectures` returned no hits.
- Direct rg and source reading in the upstream endofunctor-algebra extension for
  `IsoAlgebra|mapOfNatIso|IsIsoStr` verified the exact existing fixed-pair notion
  and the two transport formulas before selecting the attachment.

Validation: `scompile.py` successfully compiled the scratchpad axiom probe against the
live published library, in both server passes (4.0 seconds each). All three declarations
reported exactly `[propext, Classical.choice, Quot.sound]`, with no errors or warnings.
The delivery wrapper also independently #checks every name listed in the record.
The scratchpad axiom probe is not a delivered module.

Preflight record adjustment: the existing WeilConjectures attachment uses the required
`branch: "slopmaster2"`; the recorded signature begins at the keyword `def`, excluding
the preceding `noncomputable` modifier as required by the signature scanner.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
