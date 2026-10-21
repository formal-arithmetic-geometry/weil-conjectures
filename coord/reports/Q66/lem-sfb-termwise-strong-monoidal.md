## Worker report

Recorded an existing upstream interface; no new module, definition, or proof.
The main declaration is `CategoryTheory.Functor.mapCochainComplexMonoidal` in
`WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex` (line 227).
Its signature is copied verbatim into `lean.statement`. The companion declarations
in `lean.declarations` give the specified comparisons and their characterizations.
Only the item's `lean` field changes. No repair note for this item was present.

Hypotheses, matched individually:

- The two abelian categories are `[Category.{vC} C] [Abelian C]` and
  `[Category.{vD} D] [Abelian D]`, with `C : Type uC` and `D : Type uD`.
  All four universe parameters remain independent.
- Their specified tensor structures are `[MonoidalCategory C]` and
  `[MonoidalCategory D]`; additivity in both variables is
  `[MonoidalPreadditive C] [MonoidalPreadditive D]`.
- All small colimits supply `[HasColimitsOfSize.{0,0} C]` and the corresponding
  instance for `D`. Two-sided tensor preservation supplies
  `[∀ X, PreservesColimitsOfSize.{0,0} ((curriedTensor C).obj X)]` and its `.flip`
  version, and the same two instances for `D`. These are sufficient consequences
  of the node's assumptions, not added restrictions: the upstream construction
  needs only the small integer-indexed sums. Every graded binary, triple and
  quadruple tensor prerequisite is inferred from these assumptions on the server.
- The functor is `(F : C ⥤ D) [F.Additive] [F.Monoidal]`.
  The last class is exactly the strong monoidal data of the dependency:
  `Functor.Monoidal.εIso F` is `e_F`, and
  `(Functor.Monoidal.μIso F A B).symm` is `c_{A,B}`.
  `Functor.CoreMonoidal.toMonoidal` converts the dependency's isomorphism-based
  presentation to this equivalent class; there is no symmetry assumption.
- Countable coproduct preservation is
  `[∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F]`.
  This infers the upstream hypothesis for the fibres of `ComplexShape.π` on
  integer pairs; each such fibre is countable. No preservation of arbitrary
  colimits by `F` or exactness of `F` is assumed.

Conclusions, matched individually (Lean composition `a ≫ b` means first `a`):

- Unbounded integer cochain complexes are `CochainComplex C ℤ`.
  `F_Ch` is `F.mapHomologicalComplex (.up ℤ)`. The tensor is the existing
  `HomologicalComplex.tensorObj`, with injections `ιTensorObj`; the displayed
  signed differential is `CochainComplex.ιTensorObj_d`, including `p.negOnePow`.
  `HomologicalComplex.monoidalCategory` supplies the ordinary complex constraints
  recorded by `lem-sfb-total-tensor-homotopy`.
- Set `τ_{P,Q} = (F.mapCochainComplexμIso P Q).symm`. This is an isomorphism
  with exactly the source and target in the node. Its hom is the component of
  `Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F`, by
  `mapCochainComplexμIso_inv`. This is a natural transformation of bifunctors,
  and its `IsIso` instance supplies a natural isomorphism.
- The summand equation is
  `F.map (ιTensorObj P Q p q n h) ≫ τ.hom.f n =
  (Functor.Monoidal.μIso F (P.X p) (Q.X q)).inv ≫
  ιTensorObj (F_Ch.obj P) (F_Ch.obj Q) p q n h`.
  It is exactly `HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX`,
  specialized to `Functor.OplaxMonoidal.δNatTrans F`, using
  `mapHomologicalComplexδNatTrans_app_app` and `mapBifunctorComparison_f`.
  Uniqueness in every degree is exactly the preserved-coproduct extensionality
  theorem `HomologicalComplex.mapBifunctor.hom_ext_of_map`; equality of complex
  maps is componentwise. Thus this is the specified canonical comparison,
  rather than an arbitrary monoidal structure.
- The units are `𝟙_ (CochainComplex C ℤ)` and `𝟙_ (CochainComplex D ℤ)`,
  the single complexes in degree zero. Set `j = F.mapCochainComplexεIso.symm`.
  Its definition uses `single.mapIso (Functor.Monoidal.εIso F)` and
  `singleMapHomologicalComplex`. The theorem `mapCochainComplexεIso_hom_f_zero`
  identifies its inverse in degree zero with `e_F` under `singleObjXSelf`.
  Hence `j` is `e_F⁻¹` there. At every other degree both sides are zero objects,
  so the components are the unique zero-object isomorphisms; the termwise
  single-complex comparison supplies these identifications canonically.
- Write `H = F_Ch` in the following explanatory formulas. By
  `mapCochainComplex_δ`, `δ H P Q` is exactly `τ.hom`, and by
  `mapCochainComplex_η`, `η H` is exactly `j.hom`.
  `Functor.OplaxMonoidal.associativity H P Q R` says
  `δ H (P ⊗ Q) R ≫ δ H P Q ▷ H.obj R ≫ (α_ _ _ _).hom =
  H.map (α_ P Q R).hom ≫ δ H P (Q ⊗ R) ≫ H.obj P ◁ δ H Q R`.
  Reversing the equality gives precisely the node's associator equation.
- `Functor.OplaxMonoidal.left_unitality_hom H P` says
  `δ H (𝟙_ _) P ≫ η H ▷ H.obj P ≫ (λ_ _).hom = H.map (λ_ P).hom`.
  `right_unitality_hom H P` says
  `δ H P (𝟙_ _) ≫ H.obj P ◁ η H ≫ (ρ_ _).hom = H.map (ρ_ P).hom`.
  These are precisely the two displayed unit equations, with equality reversed.
- The instance `mapCochainComplexMonoidal` is explicitly built from
  `mapCochainComplexμIso` and `mapCochainComplexεIso` using
  `CoreMonoidal.toMonoidal`. Thus its tensorator and unit are `τ⁻¹` and `j⁻¹`,
  as required. The file assumes neither braiding nor symmetry, on the
  categories or on the functor.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory` in
  `Mathlib.CategoryTheory.Monoidal.Category`.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `Cocone`,
  `IsColimit` and the canonical desc interface in
  `Mathlib.CategoryTheory.Limits.HasLimits`, `Cones`, and `IsLimit`.
- `def-sfb-preserves-kflat-quasi-iso`:
  `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso` was read, including
  `CochainComplex.IsKFlatForTotalTensor` and
  `Functor.PreservesTotalTensorKFlatQuasiIso`. This node uses only its specified
  Mathlib binary total tensor, not a K-flatness hypothesis or its preservation
  property, so those classes do not occur in the binding.
- `lem-sfb-total-tensor-homotopy`: its existing
  `HomologicalComplex.monoidalCategory` in `Mathlib.Algebra.Homology.Monoidal`
  is the complex structure used here. The recorded module
  `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` was read;
  the homotopy quotient portion is not needed for this statement.
- `def-sfb-strong-monoidal-functor`: `Functor.CoreMonoidal`,
  `CoreMonoidal.toMonoidal`, `Functor.Monoidal`, `Monoidal.εIso` and
  `Monoidal.μIso` in `Mathlib.CategoryTheory.Monoidal.Functor`.

Source checked: Stacks `sites-cohomology.tex`, label
`lemma-symmetric-monoidal-cat-complexes` (Tag 0FPQ), lines 12935–12962, specifies
signed total tensor and the degree-zero unit. As the node itself records,
its abstract functor extension is not literally this Stacks lemma; it is
implemented by the upstream `MapHomologicalComplex.lean`, lines 28–248.
The auxiliary canonical comparison and uniqueness declarations are in
`WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`, lines 53–75 and 154–185;
the natural comparison is in `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`,
lines 387–441. All those definitions and docstrings were read.

Edge cases checked: zero complexes and zero summands use zero-object uniqueness;
single-degree complexes reduce to the original tensorator; the degree-zero unit
uses the supplied unit map with the correct inverse orientation. Negative and
odd degrees retain `p.negOnePow`, since the existing signed comparison commutes
with the total differential. Arbitrarily unbounded complexes are allowed, as
the coproducts range over all integer pairs. The identity functor gives the
canonical coproduct comparison. An empty coefficient category is impossible
under `Abelian`, which supplies a zero object. There are no degree bounds,
nonzero-object assumptions or hidden symmetry requirements.

Searches actually run with `msearch.py Q66 lem-sfb-termwise-strong-monoidal`:

- `leanfinder`: “An additive strong monoidal functor preserving countable
  coproducts induces a strong monoidal functor on unbounded cochain complexes
  with signed total tensor and canonical summand comparisons”. Eight hits,
  including `HomologicalComplex.monoidalCategory`, `ιTensorObj`, `tensorObj`,
  and `Monoidal.inducingFunctorData`; none is this functor extension in Mathlib.
- `loogle`: `"mapHomologicalComplex", "Monoidal"`: zero hits.
- `grep`: `mapCochainComplexMonoidal|mapCochainComplexμIso|mapHomologicalComplexδNatTrans`:
  zero Mathlib hits.
- `leansearch`: “An additive strong monoidal functor preserving countable
  coproducts extends termwise to a strong monoidal functor on cochain complexes”.
  Eight hits, including additive finite-coproduct preservation,
  `Functor.map_homogical_complex_additive`, and `CoreMonoidal.toMonoidal`;
  none is the required Mathlib theorem.
- `rg` of both project roots with the same names found exactly the upstream
  `MapHomologicalComplex` interface and its specialized consumers, including
  `Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations`. The latter assumes
  sheaf-pullback data and is not the general statement. A search for the exact
  node id in `WeilConjectures` and `dag/lean_names_upstream.json` had no hits;
  direct source inspection verifies the upstream declaration regardless.

Validation: `scompile.py Q66 lem-sfb-termwise-strong-monoidal scratchpad/Validate.lean`
compiled the sandbox and library probes cleanly. The probe supplies exactly the
hypotheses listed above, with explicit variables, universes and `autoImplicit false`,
and checks the instance, tensor/unit isomorphisms, naturality, summand formula,
coherence, and comparison identifications. `#print axioms` on the main instance
reports only `propext`, `Classical.choice`, and `Quot.sound`. The probe remains
outside `lean/` and is not part of the delivery. The delivery tool additionally
checks every recorded existing declaration on the server.

No statement correction, dependency repair, new node, or disputed statement.

## Second reading by Q66

No second reading by a worker: the worker was instructed not to start agents
and to deliver directly. The maintainer's independent review is the review.
