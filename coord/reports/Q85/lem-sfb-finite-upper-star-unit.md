## Worker report

Recorded an existing statement, with no new Lean module:
`AlgebraicGeometry.ProEtale.isIso_upperStar_η`, in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`,
lines 87–93. The signature copied verbatim from the source is
`instance ProEtale.isIso_upperStar_η : IsIso (η (g)^*[A])`.
The node copy changes only `lean`, completing the former partial attachment record.
There is no repair note for this item.

Source checked: the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/` folder, unit
`sk-def-sfb-finite-pushforward-pullback`, node
`lem-sfb-finite-upper-star-unit.md`, order 1516. Its statement agrees with the DAG.
The blueprint's suggested name `isIso_η_upperStar` has become `isIso_upperStar_η` upstream.

Hypotheses and clauses, including enclosing section parameters:

- The coefficient category is `(A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]`. This is precisely the shared size convention for
  Grothendieck abelian coefficients on `Scheme.{u}` small pro-étale sites.
- The tensor is `[MonoidalCategory A]`. The node's `[SymmetricCategory A]` supplies the
  source declaration's `[BraidedCategory A]`.
- The node's closedness is `[MonoidalClosed A]`. It supplies the two source parameters
  `[((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal]` and the corresponding parameter
  for `Z`. Mathlib's `GrothendieckTopology.W.monoidal` supplies these, using closedness
  and the available enriched-Hom instances. These are inferred, not extra assumptions.
  The existing result works more generally, but its application here has exactly the
  node's hypotheses; the scratch consumer below checked this specialization.
- The schemes and arbitrary morphism are `{Z Y : Scheme.{u}} (g : Z ⟶ Y)`.
  There is no finite, weakly étale, proper, nonempty, or isomorphism hypothesis on `g`.
- `upperStar A g`, written `(g)^*[A]`, is the recorded pullback functor.
  `Functor.OplaxMonoidal.η (upperStar A g)` has type `g^*𝟙 ⟶ 𝟙` for the sheaf tensor.
- The map is the specified mate, not an arbitrarily chosen isomorphism:
  `ProEtale.oplaxMonoidal_upperStar` is defined by
  `(upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal`, and Mathlib defines its
  `η` field as `(adj.homEquiv _ _).symm (Functor.LaxMonoidal.ε G)`.
  Thus the actual map is definitionally
  `((upperStarLowerStarAdjunction A g).homEquiv _ _).symm
  (Functor.LaxMonoidal.ε (lowerStar A g))`.
  An equality to this expression compiled by `rfl` in the scratch consumer.
- The whole conclusion is `IsIso` of this map, exactly as in the existing instance.

Dependency declarations read with full section parameters and docstrings:

- `def-sfb-finite-upper-lower-star-adjunction` records
  `AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
  Its type is `(g)^*[A] ⊣ (g)_*[A]`, on sheaves over the small pro-étale sites.
  The compatibility path and the finite-coefficient implementation use the same
  declaration, as confirmed by the compiler's type check and the definitional mate check.
- `def-sfb-finite-lower-star-lax-monoidal` records
  `AlgebraicGeometry.ProEtale.laxMonoidal_lowerStar` and
  `AlgebraicGeometry.ProEtale.laxBraided_lowerStar` in the same finite-coefficient
  monoidal module as the selected instance. Their signatures give precisely the
  lax monoidal unit/tensor maps and compatibility with the braiding. Both were checked
  with `#check @...`. The shared dependency record was refreshed by another group during
  this task; the delivered item uses those same canonical declarations.

Proof correspondence: the upstream instance unfolds `upperStar` and uses
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback`.
Its docstring and proof treat the constant presheaf, sheafification, the connected comma
categories (filtered by representable flatness of base change), and the adjunction mate.
This matches the node's proof: identify both left adjoints to restriction followed by
inclusion, compute the left Kan extension of the constant unit over connected nonempty
indexing categories, sheafify, and identify the resulting unit comparison by adjunction.
No proof was added or changed in the delivery.

Edge cases: arbitrary `g` includes the identity and morphisms involving empty schemes.
The theorem imposes no nonemptiness on either scheme, and imposes no nonzero condition on
coefficients or the tensor unit. Thus the empty scheme and the zero coefficient category
are retained. No dimension, characteristic, degree or index-set assumption is introduced.
Universe `u'` for coefficient objects is independent of scheme universe `u`, while
morphisms have universe `u + 1`, exactly as in the recorded dependencies.

Searches made (the msearch results are also logged in sandbox `searches.jsonl`):

- `msearch.py leanfinder`, query
  `g star preserves the unit, mate of pushforward unit is an isomorphism`:
  eight hits, including `Adjunction.unit_app_unit_comp_map_η` and related mate identities;
  none was the specialized pro-étale theorem.
- `msearch.py loogle`, query
  `AlgebraicGeometry.ProEtale.isIso_upperStar_η, CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback`:
  zero hits; the upstream identifier is unknown to the Mathlib-only search service.
- `msearch.py grep`, query `isIso_upperStar_η|upperStar.*unit`, subdirectory
  `SixFunctors/ProEtale`: zero Mathlib hits (that is a project, not Mathlib, directory).
- `msearch.py leansearch`, query
  `The inverse image functor of sheaves preserves the monoidal unit and its comparison map is an isomorphism`:
  eight hits, including `Functor.Monoidal.instIsIsoη` and
  `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal`. These are general monoidal
  or sheaf-of-modules results, not this exact pro-étale statement.
- `msearch.py grep`, query `leftAdjointOplaxMonoidal|isIso.*η`, subdirectory
  `CategoryTheory/Monoidal`: six hits, including `leftAdjointOplaxMonoidal` and the
  general monoidal invertibility instance. Its definition establishes the mate formula.
- Direct `rg` in the upstream `WeilConjectures/` tree found the exact instance at
  `SixFunctors/ProEtale/UpperLowerStar/Monoidal.lean:91` and the canonical lax structures.
  The current canonical source was then read using `scompile.py --source` for both the
  compatibility monoidal module and its finite-coefficient implementation.
- Direct `rg` for the two unit-isomorphism spellings in `lean/Sheaf` found no duplicate.
  Direct searches for the item id in upstream `WeilConjectures/`, and for the actual
  declaration name in `dag/lean_names_upstream.json`, found no additional match.
  The item's existing `lean_audit` already named this exact declaration.

Validation: `scompile.py Q85 lem-sfb-finite-upper-star-unit scratchpad/Check.lean`
passed both sandbox and library checks without warnings. With explicitly bound universes
and `autoImplicit false`, this consumer assumed only closed symmetric monoidal
Grothendieck abelian coefficients and arbitrary `g`; it applied the existing instance
without explicit localization hypotheses and checked the mate identity by reflexivity.
`#print axioms AlgebraicGeometry.ProEtale.isIso_upperStar_η` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The scratch file is outside `lean/` and
is not delivered. The required dry run additionally checks the existing declaration.

No statement correction, new node, dependency module, or STATEMENT-DISPUTED issue.

## Second reading by Q85

The node introduces the following data and clauses, all of which match the recorded
declaration.  The coefficient category is a closed symmetric monoidal Grothendieck
abelian category \(\mathcal A\); in Lean this is specialized through
`A : Type u'`, `Category.{u + 1} A`, `Abelian A`,
`IsGrothendieckAbelian.{u + 1} A`, `MonoidalCategory A`, `SymmetricCategory A`, and
`MonoidalClosed A`.  The schemes and morphism are arbitrary `Z Y : Scheme.{u}` and
`g : Z ⟶ Y`, with no finiteness, properness, nonemptiness, or characteristic
hypothesis.  The two pro-étale sheaf tensor instances required by the source module
are inferred from closedness; they are the recorded `W.IsMonoidal` parameters of
`isIso_upperStar_η` and add no mathematical assumption in this specialization.

The map in the conclusion is the oplax unit comparison
`Functor.OplaxMonoidal.η (upperStar A g)`, whose source and target are respectively
`g^* 𝟙` and `𝟙`.  Its oplax structure is
`ProEtale.oplaxMonoidal_upperStar`, defined as the left-adjoint oplax structure of
`upperStarLowerStarAdjunction A g`; by the definitional mate formula its component is
the mate of `Functor.LaxMonoidal.ε (lowerStar A g)`, exactly the unit map supplied by
`laxMonoidal_lowerStar` in the node.  The conclusion `IsIso (η (g)^*[A])` is therefore
exactly the node's assertion that this specified mate is an isomorphism.  The exact
existing declaration is `AlgebraicGeometry.ProEtale.isIso_upperStar_η` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`.

I read both dependency records and their source declarations: the adjunction is
`AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`, and the lax unit is from
`AlgebraicGeometry.ProEtale.laxMonoidal_lowerStar` (with
`laxBraided_lowerStar` supplying the symmetry compatibility).  No dependency is
missing or unusable.  The worker's node copy already records the exact existing
declaration and its verbatim Lean statement; I made no statement or node change.

Edge cases checked: identity and arbitrary morphisms, morphisms between empty schemes,
zero coefficient objects/categories, and the absence of any nonzero or index-set
condition are all covered.  The independent coefficient universe `u'` and scheme
universe `u` are retained.  Searches over Mathlib, the upstream `WeilConjectures`
tree, and `lean/Sheaf` found no competing declaration; the only exact declaration is
the canonical upstream instance above.  The scratch consumer compiled with precisely
the node's closed symmetric hypotheses, and the mate equality reduced by `rfl`.
Thus no mismatch was found and no repair was required.
