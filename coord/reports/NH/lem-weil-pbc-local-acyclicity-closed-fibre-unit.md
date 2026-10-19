## Worker report

The module `Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit` states
`AlgebraicGeometry.Etale.isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative`.
Its only declaration is a theorem with whole proof `sorry`. No definitions or nodes
are added, and the original node is unchanged except for `lean`.

Source read: Stacks Project, etale-cohomology.tex, Tag 0GJU,
`lemma-beta-is-isomorphism`, including the preceding construction of beta and its
bounded-below/local-acyclicity hypotheses. This is its specialization to `G[0]`.

Hypothesis and clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Abelian etale sheaf: `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Local acyclicity relative to this exact sheaf: `hG : IsLocallyAcyclicRelative f G`.
- Geometric base point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `s : Spec (.of Ω) ⟶ S`.
- The strict local base is `Scheme.strictHenselizationScheme s`. Its map to `S`
  is the already constructed `Scheme.strictHenselizationStructuralMap s`.
- The canonical lift over the closed point is
  `Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s))`.
  This is evaluation of the ring colimit at the compatible pointed-neighbourhood
  lifts, hence precisely the canonical factorization of the geometric point.
  The functoriality/residue theorem describes the same lift through the separable
  residue field; no arbitrary factorization of `s` is quantified over here.
- Arbitrary geometric point of the strict local base:
  `{Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']`
  and `t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s`.
  No algebraicity assumption on Ω' is added.
- `X'` is `pullback f (Scheme.strictHenselizationStructuralMap s)`;
  `p` is its `pullback.fst`, and `f'` its `pullback.snd`.
- The two geometric fibres are the pullbacks of `f'` along the canonical lift
  and `t`. Their maps `i` and `h` to `X'` are the respective `pullback.fst` terms.
- `G'` is `(upperStar AddCommGrpCat.{u + 1} p).obj G`.
- `G'[0]` is `(_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G'`.
- The canonical beta is
  `(Adjunction.derivedPlus (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h))`
  `.unit.app (G'[0])`. Its target is the right derived direct image of the
  termwise inverse image of `G'[0]`, canonically `Rh_*(G_t[0])`. In particular
  this is the actual unit, with no unspecified comparison map supplied as data.
- Applying `(Functor.mapDerivedCategoryPlus (upperStar AddCommGrpCat.{u + 1} i)).map`
  gives the requested `i^{-1} beta`. The conclusion is `IsIso` of this map in
  `DerivedCategory.Plus (Sheaf (X_s).smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Neither properness nor torsion occurs among the hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to the
  small etale topology and `AddCommGrpCat.{u + 1}`.
- `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf`:
  `AlgebraicGeometry.Etale.IsLocallyAcyclicRelative` (and its pointwise definition).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`, confirming
  the inline geometric-point encoding.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme`
  and `Scheme.strictHenselizationRing`.
- `Sheaf.Paper.StrictHenselizationFunctoriality`: `strictHenselizationResidue`
  and `strictHenselizationFunctoriality`; the lift used in the expression is the
  existing `Scheme.strictHenselizationPointEvaluation` from
  `Sheaf.Paper.StrictHenselizationPointEvaluation`, already publicly available
  through the local-acyclicity dependency.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded abelian-sheaf derived
  category encoding; `DerivedCategory.Plus` and `DerivedCategory.Plus.singleFunctor`
  are Mathlib constructions, not the coefficient-module variant.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `CategoryTheory.Adjunction.derivedPlus`, whose right adjoint is the existing
  `lowerStar.rightDerivedFunctorPlus`.

The module imports the available proof-dependency modules (the full six-step
natural-language proof is in the theorem docstring). The sole proof dependency
without a Lean declaration or Mathlib match is
`lem-weil-pbc-strict-base-closed-point-localizations`, so it has no import.
Mathlib stalk conservativity, pullback spectra, exact stalks, and the bounded-below
cohomology criterion are already publicly available from the imported modules.

Edge cases checked: the empty scheme and empty geometric fibres are not excluded;
the zero sheaf is allowed; Ω' may have arbitrary transcendence degree; the closed
point itself may be chosen as `t`; no characteristic restriction, coefficient
exponent, quasi-compactness of `f`, or properness occurs. Both field carriers use
`Type u` with `Scheme.{u}`, consistently with all the recorded dependencies;
there is no smaller independent universe for test points. All variables and the
universe are explicitly bound. The degree-zero embedding guarantees boundedness
below without an extra hypothesis.

Searches made before writing:

- `msearch.py ... leanfinder`, query: "For a locally acyclic morphism and abelian
  etale sheaf the derived unit to a geometric fibre restricts to an isomorphism
  on the closed fibre of the strict henselization". Eight hits, including
  `Scheme.Hom.fiberToSpecResidueField_apply`, strict-local germ lemmas, and the
  point sheafification comparison; none states this result.
- `msearch.py ... loogle`, query: "IsIso, CategoryTheory.Adjunction.derivedPlus".
  Returned zero hits and "unknown identifier 'IsIso'"; the index does not supply
  the proposed specialized statement.
- `msearch.py ... grep`, query:
  `locallyAcyclic|LocallyAcyclic|beta_is_isomorphism`. Zero Mathlib hits.
- `rg` of upstream `WeilConjectures/` and project `lean/Sheaf` for
  `localAcyclic|LocallyAcyclic|lem-weil-pbc-local-acyclicity-closed-fibre-unit|beta_is_isomorphism`.
  Only the project's dependency `LocalAcyclicityAbelianSheaf.lean` matched;
  it defines the hypothesis and does not state the present theorem.
- `rg` of Mathlib, upstream, project modules and `dag/lean_names_upstream.json`
  for `isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative`: no collision.

No statement correction or disputed statement is needed.

## Second reading by NH

Independent reading of the node, its source place and the proposed Lean: PASS.
I did not write the statement. I read Stacks etale-cohomology.tex, the whole
cospecialization construction preceding lemma-beta-is-isomorphism (Tag 0GJU),
its proof, and definition-locally-acyclic with equation-alpha-K (Tag 0GJP).
The surrounding source assumes boundedness below and local acyclicity; there
is no standing properness, torsion, finiteness, or characteristic hypothesis.
For the node's specialization K = G[0], boundedness below is automatic.

Object/hypothesis/conclusion inventory, matched individually with the Lean:

1. Arbitrary schemes X and S, and a morphism f: rendered by
   `{X S : Scheme.{u}} (f : X ⟶ S)`. PASS; no geometric property is assumed.
2. An abelian sheaf G on the small etale site of X: rendered by
   `(G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. PASS;
   this is the dependency's abelian-sheaf category, not module coefficients.
3. Local acyclicity of f relative to this G: rendered by
   `(hG : IsLocallyAcyclicRelative f G)`. PASS. I opened
   LocalAcyclicityAbelianSheaf.lean: this predicate quantifies over every
   geometric x and every geometric t in the strict localization of its image,
   requires IsIso of the canonical localAcyclicityAlpha, and vanishing of all
   positive cohomology. Its strict map is selected from a unique pointed map,
   not from a mere existence assertion, and alpha is the germ inverse followed
   by restriction. No assumption of algebraicity on the test field occurs.
4. A geometric base point s: rendered by `{Ω : Type u} [Field Ω]
   [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`. PASS; I checked the recorded
   inline geometric-point encoding and Scheme.SpecToEquivOfField.
5. The strict local base S': `Scheme.strictHenselizationScheme s`. PASS;
   StrictHenselization.lean constructs its ring as the colimit of the actual
   affine pointed-neighbourhood coordinate rings, and takes its spectrum.
6. Its structural map: `Scheme.strictHenselizationStructuralMap s`. PASS;
   I read its signature and defining characterization by all neighbourhood
   legs in StrictHenselizationStructuralMap.lean.
7. The canonical closed-point lift of s, not an arbitrary lift:
   `Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s))`.
   PASS. I read StrictHenselizationPointEvaluation.lean: the ring map is
   colimit.desc of the compatible geometric-point evaluations. The residue
   theorem strictHenselizationResidue in StrictHenselizationFunctoriality.lean
   characterizes the lift by exactly these evaluations; uniqueness of maps
   from the ring colimit identifies these descriptions. No residue-algebra
   instance or chosen residue isomorphism is added to the item's hypotheses.
8. An arbitrary geometric point t of S': rendered by `{Ω' : Type u}
   [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶
   Scheme.strictHenselizationScheme s)`. PASS; no restriction to algebraic
   geometric points, generic points, or a particular generization is added.
9. X' = X times_S S', p and f': rendered by `pullback f
   (Scheme.strictHenselizationStructuralMap s)`, its `pullback.fst`, and its
   `pullback.snd`. PASS. The projections have their correct directions.
10. X_s, X_t and their maps i, h to X': the two outer `pullback.fst` terms
    take `pullback.snd f (Scheme.strictHenselizationStructuralMap s)` first,
    and the canonical lift or t second. PASS; these are scheme fibre products,
    not the set of geometric lifts sometimes called a geometric fibre.
11. G' = p inverse-image G: rendered by `(upperStar AddCommGrpCat.{u + 1}
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G`.
    PASS. I read upperStar, lowerStar and upperStarLowerStarAdjunction in the
    recorded upstream UpperLowerStar/Defs.lean: these are the small-etale
    inverse image and direct image and their adjunction.
12. G'[0] and G_t[0] in bounded-below derived categories: the object at the unit
    is `(_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G'`. PASS;
    Mathlib Plus.singleFunctor puts precisely that sheaf in degree zero.
    The left adjoint of derivedPlus is the termwise inverse image on D+,
    so its image of this object represents h inverse-image G' in degree zero.
    No replacement object or resolution is supplied as a hypothesis.
13. The canonical beta from G'[0] to Rh_*(G_t[0]): rendered by
    `(Adjunction.derivedPlus (upperStarLowerStarAdjunction ... h)).unit.app`.
    PASS. I read the upstream derivedPlus signature and its unit_app_fac
    characterization. Its right adjoint is lowerStar.rightDerivedFunctorPlus;
    it is the recorded derived direct image, with the required unit orientation.
14. Restriction of beta by i inverse-image: rendered by
    `(Functor.mapDerivedCategoryPlus (upperStar ... i)).map` of this exact
    unit component. PASS. I read mapDerivedCategoryPlus in ExactFunctor.lean;
    it restricts the exact termwise derived functor to the bounded-below
    subcategory. The resulting source and target are on X_s.
15. Conclusion: `IsIso` of the preceding map. PASS; this states the full
    isomorphism in D+(Ab((X_s)_et)), with the original quantifier order,
    and neither merely existence of an isomorphism nor stalkwise equality.

All stmt_deps records were inspected and their operative signatures checked.
DerivedCategories.lean explicitly records the abelian-sheaf derived-category
encoding used here. Mathlib pullback supplies the fibre-product notion. The
public imports provide the statement notions and derived adjunction; the
ordinary imports match the available proof dependencies. The geometry lemma
lem-weil-pbc-strict-base-closed-point-localizations has no declaration yet,
so there is no module of it to import. This is a proof-stage obligation, not
missing data for stating the result. No new nodes or dependency modules occur
in this delivery, so H12/H13 introduce no additional review obligations.

Edge cases: the empty X and empty fibres remain permitted; a geometric s
necessarily makes S nonempty, as in the source. The zero sheaf is allowed.
There is no index family or positive coefficient integer in this statement,
so empty indexing and n = 0 add no implicit assumptions. Degree zero is the
explicit embedding degree, not a positivity restriction. Every characteristic
is covered. The test t may be the canonical closed point itself and its field
may have arbitrary transcendence degree. Both fields have Type u with
Scheme.{u}, in the recorded geometric-point convention; no smaller independent
universe makes the quantification vacuous. Sheaves have the required u+1
coefficient universe. The sole universe and all variables are bound explicitly.

Independent duplicate searches (different vocabulary from the first worker):

- LeanFinder through msearch.py: "restriction to special fibre of derived
  adjunction unit for vanishing cycles is invertible". Eight results, about
  open-immersion module adjunctions, condensed objects, and localization;
  none is this statement.
- Loogle through msearch.py: `"derivedPlus"`. Successful query, zero hits.
- Grep through msearch.py: `cospecialization|vanishingCycles|acyclic.*[Uu]nit`.
  Successful query, zero hits.
- LeanSearch through msearch.py: "A locally acyclic sheaf has invertible
  cospecialization unit on the special geometric fibre". Service unavailable
  (Internal Server Error); no mathematical verdict drawn from this failure.
- Direct rg of Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `vanishing.cycles|closed.?fibre.*unit|unit.*closed.?fibre|beta_is_isomorphism|betaIsIsomorphism`
  (case insensitive). Only unrelated special-fibre algebra statements, the
  projective-line stalk comparison comment, and the local-acyclicity definition
  occur. The projective-line result is a specific proper-base-change stalk
  comparison, not this arbitrary-f theorem. There is no existing declaration
  to replace this module.

H5/H6/H8/H9: the delivery has no definitions, private notions, local notation,
local instances, or additional assertions; its single theorem has whole proof
sorry. The source and blueprint identifiers occur in both docstrings. The
proof docstring matches all six node steps, including affineness/qcqs of h,
strict-local identifications, all cohomological degrees, the actual unit map,
local acyclicity and stalk conservativity. No mismatch was found; no Lean or
node changes were needed. Only this second-reading section was appended.
The node lean.statement was checked programmatically against the exact source
signature, from theorem through the conclusion before :=, and agrees verbatim.

Validation: scompile.py compiled LocalAcyclicityClosedFibreUnit.lean on the
server cleanly in 3.5 seconds, with nice 19, two threads, and the 60-second
per-file limit. Its side-only LocalAcyclicityAbelianSheaf dependency also
compiled in the private overlay (3.8 seconds). No warnings or errors appeared.
