## Worker report

Module: `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
Declaration: `AlgebraicGeometry.Etale.derivedInverseImageComposition`.
The single theorem, with `sorry`, states all three clauses as one conjunction. There are
no new definitions, new nodes, dependency modules, or statement corrections.

Hypotheses and objects:

- `X Y Z W : Scheme.{u}` are arbitrary schemes, and `u₀ : Y ⟶ X`, `v₀ : Z ⟶ Y`,
  `w₀ : W ⟶ Z` are exactly the three morphisms of the node. Lean composition runs
  left to right: `v₀ ≫ u₀` is the node's `u ∘ v`.
- `A := AddCommGrpCat.{u + 1}` and `Sheaf S.smallEtaleTopology A` are abelian
  sheaves on the actual small etale site, not module sheaves over a substituted ring.
  The coefficient universe is the established encoding of the dependency record.
  The universe `u` is arbitrary, and no finite-type, properness, or nonemptiness
  assumptions occur.
- `P f := upperStar A f` is the recorded inverse-image functor. `D f` applies the
  recorded `Functor.mapDerivedCategoryPlus` to this concrete exact functor.
- `c f g fg hfg` is `(upperStarComp A f g fg hfg).symm`; `e S` is `upperStarId A S`.
  These are the dependency node's actual adjunction comparisons, with the inverse
  needed for the direction written in the node. All lets are abbreviations within
  the proposition, not new definitions of notions.
- `cD` likewise abbreviates `(upperStarCompDerivedPlus ...).symm`, and `eD`
  abbreviates `upperStarIdDerivedPlus`. The data are already fully defined upstream.

Clause-by-clause rendering (conjuncts numbered in their order in the Lean statement):

1. The first conjunct is sheaf associativity. `whiskerLeft (P u₀)` of the
   `(v,w)` comparison, followed by the `(u,vw)` comparison, equals `whiskerRight`
   of the `(u,v)` comparison by `P w₀`, followed by the `(uv,w)` comparison.
   The explicit `Category.assoc ... .symm` identifies the two scheme composites;
   it adds no hypothesis. Functor composition is definitionally associative here.
2. The second conjunct is `c_{id_X,u} = u^{-1} e_X`: the comparison for
   `u₀, 𝟙 X` equals `whiskerRight (e X).hom (P u₀)`.
3. The third conjunct is `c_{u,id_Y} = e_Y u^{-1}`: the comparison for
   `𝟙 Y, u₀` equals `whiskerLeft (P u₀) (e Y).hom`. The explicit unit equality
   proofs only transport the target scheme morphism to `u₀`.
4. The fourth conjunct says, for EVERY natural isomorphism
   `t : D u₀ ⋙ D v₀ ≅ D (v₀ ≫ u₀)`, the representative formula holds iff
   `t = cD v₀ u₀ (v₀ ≫ u₀) rfl`. This is existence AND uniqueness: taking
   `t = cD ...` gives its formula; any isomorphism satisfying it equals this one.
   The equation is precisely `cᴰ ≫ φ_uv = Dv(φ_u) ≫ φ_v ≫ Q(c)` in Lean's
   composition order. Each `φ` is `mapDerivedCategoryPlusFactorsh.hom.app`,
   and `Q(c)` is `DerivedCategory.Plus.Qh.map` of the termwise natural
   transformation `NatTrans.mapHomotopyCategoryPlus ...`.
5. The fifth conjunct similarly characterizes `eD X` among ALL natural
   isomorphisms `D (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus ...)`. Its equation is
   `eᴰ_QK = φ_id,K ≫ Q(e_K)`, with the same exact termwise construction.
6. The sixth conjunct is derived associativity, with exactly the same
   whiskering and composition pattern as the first conjunct, replacing P,c by D,cD.
7. The seventh conjunct is `cᴰ_{id_X,u} = u^{-1} eᴰ_X`.
8. The eighth conjunct is `cᴰ_{u,id_Y} = eᴰ_Y u^{-1}`.

Representatives in conjuncts 4 and 5 range over `HomotopyCategory.Plus` of the
abelian sheaf category. Reading Mathlib's `HomotopyCategory.plus` shows this is
`(CochainComplex.plus C).strictMap (quotient _ _)`: it consists of objects whose
underlying complexes are bounded below, not just complexes with bounded below
cohomology. `DerivedCategory.Plus.Qh` is the localization after the homotopy quotient.
Thus quantifying these objects is exactly quantifying bounded below representing
complexes; the termwise maps have merely passed through the homotopy quotient.
`mapDerivedCategoryPlusFactorsh` is the restricted localization factorization.
No complex, bound, or degree is excluded, and no resolution assumption is added.

Dependencies read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`, read in
  `Mathlib.AlgebraicGeometry.Scheme` (the affine-local locally ringed space structure
  and its morphisms).
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and
  `upperStarLowerStarAdjunction` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, the actual sheafified
  left Kan extension and adjunction.
- `lem-weil-pbc-inverse-image-composition`: `upperStarComp` in that module,
  `upperStarId` and unit equations in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`.
  The record's location for `upperStarId` is older than the source checkout: its
  actual declaration is in Coherence, imported transitively. No replacement is needed.
- `def-weil-pbc-derived-categories`: the record explicitly gives Mathlib's
  `DerivedCategory` and `DerivedCategory.Plus` of `Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u+1}` for abelian coefficients. Read its landed
  `Sheaf.AlgebraicGeometry.DerivedCategories` module; torsion cohomology and
  module coefficients are not part of this item's statement and are not imported.
- `def-weil-pbc-derived-inverse-image`: `CategoryTheory.Functor.mapDerivedCategoryPlus`
  and `mapDerivedCategoryPlusFactorsh` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The
  general functor definition specializes directly to `upperStar`; no new notion
  is missing. The source proves exactness and installs the required instances.
- Existing data `upperStarCompDerivedPlus`, `upperStarIdDerivedPlus`, and their
  representative formulas in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` are reused.
  This is the main import; it transitively supplies the dependency modules used.
  `Mathlib.Algebra.Category.Grp.AB` supplies the Grothendieck-abelian instance for
  AddCommGrpCat needed to specialize them (it is an essential import).

Edge cases checked before writing: identities in either slot; three identity
morphisms; the zero sheaf and zero complex; an arbitrary integer lower bound;
empty schemes; nonproper and nonetale scheme morphisms; arbitrary scheme universe.
None needs a nonzero, injective, smooth, finite, or nonempty condition. In particular
all unit formulas use the identity at the correct source/target scheme, and the
associativity comparison has the common target `w₀ ≫ v₀ ≫ u₀` on both sides.

Source checked: the local Stacks TeX is not present on this machine, so opened
https://stacks.math.columbia.edu/tag/0D6D directly. It computes the composite
pullback on a representative by termwise composition; exact abelian inverse image
requires no K-flat resolution. The coherence argument is the node's six-step
argument through uniqueness of adjoints and localization, reproduced in the docstring.

Searches (2026-10-11):

- msearch LeanSearch, query `derived inverse image composition natural isomorphisms
  coherence`: unavailable, Internal Server Error (no mathematical verdict).
- msearch LeanFinder, query `derived inverse image etale sheaves composition
  associativity uniqueness natural isomorphism`: eight hits, including
  `Scheme.Modules.restrictFunctorComp` and site sheaf-composition formulas;
  none states this three-clause theorem for abelian etale sheaves on D+.
- msearch Loogle, query `Functor.mapDerivedCategoryPlusCompIso`: unknown identifier,
  zero hits. The declaration is in the project extension, not the search server.
- msearch grep, query `mapDerivedCategory.*CompIso|upperStarCompDerivedPlus_assoc`
  in Mathlib CategoryTheory: zero hits.
- rg across upstream WeilConjectures, this project's lean/Sheaf, and pinned Mathlib,
  for inverse-image, `upperStarCompDerivedPlus`, coherence, and
  `derivedInverseImageComposition|upperStarCompDerivedPlus_assoc`: finds existing
  comparison data, sheaf associativity, generic derived-functor associativity,
  representative formulas, and derived unit laws, but no complete theorem and no
  etale derived associativity. Also checked `dag/lean_names_upstream.json` for
  the proposed name: no collision.
- grep -rn for this node id in upstream WeilConjectures: no occurrence.

Validation: server single-file compile passes with no errors or warnings. The
only proof body is `by sorry`; no mathematical statement is proved in this stage.

## Second reading by H1

Read the node independently against the module and all five statement dependencies.
No mathematical mismatch found; no Lean, dependency record, or node change was needed.
The second reading adds this report only. No new definition nodes, dependency modules,
or statement correction are present.

Objects and hypotheses, listed before checking the conclusion:

- Four schemes and three arbitrary composable morphisms: `{X Y Z W : Scheme.{u}}`,
  `(u₀ : Y ⟶ X) (v₀ : Z ⟶ Y) (w₀ : W ⟶ Z)`. Verdict: exact match;
  `v₀ ≫ u₀` denotes `u ∘ v`. No morphism-property or field hypothesis is added.
  Read Mathlib's `Scheme` structure and category: locally affine locally ringed spaces,
  with locally ringed-space morphisms, as def-pc-scheme requires.
- Abelian sheaves on the small etale sites: `Sheaf S.smallEtaleTopology A` with
  `A := AddCommGrpCat.{u + 1}`. Verdict: correct coefficient category, no replacement
  by O-module sheaves. The universe convention matches the recorded derived-category
  dependency and upstream SixFunctors convention; `u` remains arbitrary.
- Sheaf inverse images and their adjunction comparisons: `P f := upperStar A f`,
  `c ... := (upperStarComp A ...).symm`, `e S := upperStarId A S`.
  Verdict: the recorded dependency notions, not private copies. Opened Defs and
  Coherence: upperStar is the sheafified left Kan extension for arbitrary scheme
  morphisms; upperStarComp is the comparison obtained by conjugating lowerStarComp.
  The latter's direction is opposite to the node's d, so the inverse upperStarComp
  is exactly the node's unit-compatible c. Read the identity comparison and its
  unit equation in Coherence (its actual location despite the older node record).
- Bounded below derived inverse images: `D f := (P f).mapDerivedCategoryPlus`.
  Verdict: exact match. Read ExactFunctor: this is the restriction of mapDerivedCategory
  to the full subcategory defined by bounded below cohomology. Its exactness instances
  are supplied for upperStar, not imposed as extra hypotheses. Read the landed
  DerivedCategories module and its record: the abelian-coefficient D and D+ here are
  explicitly the existing Mathlib categories of these same sheaves; torsion and general
  module coefficients are not hypotheses of this item.
- Factorization identifications and representing complexes:
  `mapDerivedCategoryPlusFactorsh`, `HomotopyCategory.Plus`, and `DerivedCategory.Plus.Qh`.
  Verdict: the dependency's phi restricted to D+. Read their definitions: homotopy Plus
  uses `CochainComplex.plus.strictMap (quotient ...)`, hence actually bounded below
  complexes, while derived Plus means bounded below cohomology. Qh is the restriction
  of Qh to those representatives. Termwise comparisons are mapped by
  `NatTrans.mapHomotopyCategoryPlus` and then Qh; passing through the homotopy quotient
  neither changes nor narrows the node's formula on bounded below complexes.

Conclusion clauses, with conjunct numbers as written in the file:

1. Sheaf associativity (conjunct 1): `whiskerLeft (P u₀) (c w₀ v₀ ...).hom ≫
   (c (w₀ ≫ v₀) u₀ ...).hom` equals `whiskerRight (c v₀ u₀ ...).hom (P w₀) ≫
   (c w₀ (v₀ ≫ u₀) ...).hom`. Verdict: the two paths in clause (1), with common
   target P(w₀ ≫ v₀ ≫ u₀); Category.assoc only supplies the composite equality.
2. Sheaf unit at X (conjunct 2): `c u₀ (𝟙 X) ...` equals
   `whiskerRight (e X).hom (P u₀)`. Verdict: c_{id_X,u} = u^{-1}e_X.
3. Sheaf unit at Y (conjunct 3): `c (𝟙 Y) u₀ ...` equals
   `whiskerLeft (P u₀) (e Y).hom`. Verdict: c_{u,id_Y} = e_Yu^{-1}.
4. Derived composition existence and uniqueness (conjunct 4): for every natural iso
   `t : D u₀ ⋙ D v₀ ≅ D (v₀ ≫ u₀)`, its component formula for every K holds iff
   `t = cD v₀ u₀ ...`. Verdict: exactly the unique lift of termwise c in clause (2).
   Instantiating t with cD proves existence from this proposition; the forward direction
   gives uniqueness. The formula reads in Lean composition order as
   `t_QK ≫ phi_uv = Dv(phi_u) ≫ phi_v ≫ Qh(c_K)`, exactly the node's displayed formula.
   Opened upperStarCompDerivedPlus and its component formula: it is the induced
   upperStarComp followed by the generic derived-composition comparison; taking its
   inverse supplies the selected cD with precisely this direction.
5. Derived identity existence and uniqueness (conjunct 5): for every natural iso
   `t : D (𝟙 X) ≅ 𝟭 ...`, `t_QK = phi_id ≫ Qh(e_K)` for all K iff `t = eD X`.
   Verdict: exactly the second formula and uniqueness in clause (2). Opened
   upperStarIdDerivedPlus and upperStarIdDerivedPlus_hom_app to check the chosen eD.
6. Derived associativity (conjunct 6): the conjunct-1 paths with D,cD substituted
   for P,c. Verdict: exact match to clause (3), including whiskering directions.
7. Derived unit at X (conjunct 7): `cD u₀ (𝟙 X) ...` equals
   `whiskerRight (eD X).hom (D u₀)`. Verdict: clause (3)'s first unit law.
8. Derived unit at Y (conjunct 8): `cD (𝟙 Y) u₀ ...` equals
   `whiskerLeft (D u₀) (eD Y).hom`. Verdict: clause (3)'s second unit law.

Source reading: no Stacks checkout is installed in literature on this machine.
Fetched upstream sites-cohomology.tex into the item's scratchpad and read section
Derived pullback (3494 onward), lemma-derived-pullback-composition (3658), and its
proof. The section assumes morphisms of ringed topoi, not finite type, Noetherian,
proper, or a field. Its K-flat representatives are needed for general module pullback;
for the node's exact inverse image on abelian sheaves no resolution is required.
Also read Stacks [03CB](https://stacks.math.columbia.edu/tag/03CB),
[04VG](https://stacks.math.columbia.edu/tag/04VG), and
[0D6D](https://stacks.math.columbia.edu/tag/0D6D).
The source uses composite equalities; the node explicitly supplies the adjunction and
localization coherence argument. The theorem docstring carries all six proof steps,
including uniqueness, restriction, evaluation on representatives, and naturality.

Edge cases: empty schemes and all identity morphisms remain admitted; zero sheaves
and zero complexes are included in the categories; lower bounds are arbitrary integers
(including zero and negative bounds), not a nonnegative-degree convention. There is
no characteristic hypothesis or invertibility condition. No index family occurs, so
an empty index set imposes no restriction. All schemes can be placed in a common
arbitrary universe u; coefficients follow the existing u+1 dependency encoding.
Every binder and universe is explicit. All identity equations use the correct X or Y.

Independent searches, 2026-10-11 (different conceptual query from the first reader):

- msearch LeanFinder: `pseudofunctor coherence exact pullback bounded below localization
  natural transformations`; eight hits, chiefly general pseudofunctor descent and
  derivability/localization declarations. None is this theorem for etale D+.
- msearch Loogle: `CategoryTheory.Functor.mapDerivedCategoryCompIso`; seven hits for
  the generic unbounded comparison and its formulas, no complete statement here.
  Checked the pinned Mathlib and source text rather than assuming the search server's
  newer Mathlib is installed.
- msearch LeanSearch: `unique natural transformation on localization determined on
  bounded below complexes`; unavailable (Internal Server Error). No verdict assigned.
- rg across all upstream WeilConjectures, pinned Mathlib, and project lean/Sheaf for
  `upperStarCompDerivedPlus.*assoc`, `mapDerivedCategoryPlusCompIso_assoc`,
  `derivedInverseImageComposition`, `pullback.*assoc`, and `pseudofunctor`: existing
  sheaf coherence, generic exact-functor coherence, and component formulas occur;
  no complete node statement or etale derived associativity occurs. Opened the
  upstream derived comparison definitions rather than treating data as a theorem.
  Checked dag/lean_names_upstream.json and project declarations for name collision.
  Verdict: reuse the existing data as the worker did; keep the new statement module.

H5/H6/H8/H9 checks: only one theorem with `by sorry`, no new definitions and no hollow
local data; all lets abbreviate existing definitions. Both docstrings identify source
and blueprint, the declaration has no Sheaf prefix, both imports are used, and every
line is at most 100 characters. The node's lean.statement equals the file's signature
verbatim, checked mechanically. No fields other than the existing lean record differ.
Server single-file scompile validation passed in 14.6 seconds with no warnings/errors.
