## Worker report

The module `Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization` states
`AlgebraicGeometry.Etale.isIso_etaleStalkSpecialization_of_proper_locallyAcyclic`.
Its sole proof is `sorry`. The item statement is unchanged. The accompanying definition
module constructs the actual specialization homomorphism, using existing restriction and
inverse-image stalk maps, with no new proof or choice of an unspecified object.

Hypothesis and clause correspondence:

- Schemes and the named morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Properness is `[IsProper f]`, the recorded Mathlib definition (separated, universally
  closed and locally of finite type; universal closedness supplies quasi-compactness).
- An abelian sheaf on the small etale site is
  `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Locally killed by positive integers is exactly `hG : G.IsTorsion`, defined by finite
  additive order locally on a covering sieve. There is no global annihilator requirement.
- Local acyclicity relative to this same sheaf is `hf : IsLocallyAcyclicRelative f G`.
  This uses the dependency's full definition, including its degree-zero canonical alpha
  isomorphism and positive-degree vanishing at every geometric point.
- Every integer q >= 0 is expressed by `q : ℕ` and `(q : ℤ)` for cohomology. This includes q=0.
- The geometric point s is `(s : Spec (.of Ω) ⟶ S)` with explicit `[Field Ω] [IsAlgClosed Ω]`.
- The test geometric point is `(t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)`
  with its own explicit field and algebraic-closure instances. No algebraicity over a
  residue field, prescribed image, or distinctness from the closed point is imposed.
- `((DerivedCategory.Plus.singleFunctor _ 0).obj G)` places G in degree zero;
  `rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f` applies Rf_*; and
  `DerivedCategory.Plus.homologyFunctor _ (q : ℤ)` takes R^q f_*G. This is the direct-image
  dependency's bounded-below derived functor, not a module-sheaf surrogate.
- `etaleStalkSpecialization s t` has source `(Scheme.pointSmallEtale s).sheafFiber.obj F`
  and target
  `(Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.obj F`.
  Thus the target is the stalk at the composite point on S, exactly as required.
- The conclusion `IsIso` is an isomorphism in AddCommGrpCat, hence an isomorphism of
  abelian groups, of this specific homomorphism. The definition first uses the uniquely
  characterized strict-local restriction, then the global germ at t, then
  `upperStarCompSheafFiberIso`. For a pointed neighbourhood section this sends its germ
  to the germ of the same section at the lift induced by t. This is precisely Stacks
  0GJ2's map, not an arbitrary isomorphism between the two groups.
- No smoothness, local constancy, finite stalk, common annihilator, characteristic,
  Noetherian, or connectedness assumption occurs.

Statement dependencies used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `CategoryTheory.Sheaf.IsTorsion`, the torsion declaration named by
  def-weil-pbc-etale-sheaves. The latter's locally constant predicates are not needed.
- `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf`:
  `AlgebraicGeometry.Etale.IsLocallyAcyclicRelative` (read together with its pointwise
  definition and alpha construction).
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationScheme` and its ring colimit construction.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its derived extension is
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `GrothendieckTopology.Point.sheafFiber`,
  with `AlgebraicGeometry.Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. These are the recorded stalks.
- The new definition uses
  `AlgebraicGeometry.Etale.existsUnique_strictHenselizationStalkRestriction` in
  `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`,
  `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap` in
  `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`, and
  `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.
  `Sheaf.ΓNatIsoSheafSections` identifies global sections with terminal-object sections;
  `Point.toPresheafFiber` is the germ map. Choice is solely from a uniqueness theorem
  specifying all pointed-neighbourhood components of the restriction.

The module imports every proof-dependency module recorded on the base. Proof dependencies
without recorded modules (closed-fibre unit, proper permanence, scheme conventions,
affine-morphism facts, specialization/cospecialization compatibility) have no import to add.
The theorem docstring follows all five proof steps and their map identifications, including
torsion preservation for the qcqs map h and exactness of the geometric stalks.

Edge cases checked: q=0 is included; empty X gives zero higher direct images and an
isomorphism between zero stalks; empty S has no test geometric points, so the assertion is
vacuous; zero sheaves satisfy the same statement; infinite torsion stalks with unbounded
orders remain allowed. Points over the strict-local closed point and over arbitrary
geometric generizations are both included. The universes match the established scheme,
point and abelian-sheaf encoding, and all universe and term variables are explicitly bound.
The source is Stacks 0GJW for K=G[0]; specialization itself is defined in 0GJ2. Both source
passages were read in the local Stacks source. No statement dispute or correction is needed.

Searches for the statement and the missing map:

- msearch LeanFinder: `proper locally acyclic morphism torsion etale sheaf specialization
  higher direct image stalk isomorphism`; eight hits about topological stalk specialization,
  none about this etale theorem.
- msearch Loogle: `"Sheaf", "specialization"`; zero hits.
- msearch grep: `locallyAcyclic|cospecialization|specialization.*cohomology`; zero hits.
- msearch LeanSearch: `specialization of geometric stalks of etale abelian sheaves via
  strict henselization`; unavailable (Internal Server Error), recorded as unavailable.
- msearch grep: `specialization|StalkSpecialization` in CategoryTheory/Sites; zero hits.
- rg in Mathlib, the source WeilConjectures tree, and project lean/Sheaf found no proposed
  declaration name. Concept searches found only topological stalkSpecializes and the
  source's finite-etale fibre specialization, neither defining this abelian etale map.
- rg for the item id in the source found no declaration.
- DAG definition searches for specialization map/homomorphism found no definition node.
  `tools/blueprint_refs.py search specialization` found related blueprint statements,
  not a definition of this map. `ancestor` returned
  thm-weil-pbc-direct-image-finiteness-proper.

Server validation: both delivered files compiled separately in dependency order with
scompile.py, nice 19, two threads, 60 seconds per file. No warnings or errors were emitted.

## New nodes

`def-weil-pbc-etale-stalk-specialization` defines specialization for an arbitrary abelian
etale sheaf F on S, from s to a geometric point t of its strict henselization, with target
the stalk at the composite point of S. Its source is Stacks Tag 0GJ2,
section-specialization. The real construction composes the existing unique strict-local
restriction with the terminal-section germ and the canonical pullback-stalk isomorphism.
It therefore uses the dependency notions rather than redefining stalks or inverse image.
The three search kinds and the DAG/source/project searches are recorded in its
mathlib_searches; none supplies this map. It is needed to name the precise homomorphism
whose invertibility the item asserts. The item's stmt_deps gains only this new node.

## Second reading by NQ

I independently read the item node, both delivered modules, every statement-dependency
record and the signatures and constructions used from those dependencies. I read Stacks
etale-cohomology.tex, section-specialization (0GJ2), including its alternative description,
and lemma-sp-isom-proper-torsion-loc-ac (0GJW), including its proof. The source assumes
only boundedness below, relative local acyclicity, properness and torsion cohomology;
for G[0], boundedness is automatic and torsion cohomology is precisely torsion of G.
No ambient Noetherian or characteristic assumption is needed.

Object, hypothesis and conclusion checklist (all pass):

- X and S are arbitrary schemes: `{X S : Scheme.{u}}`; f is the named morphism
  `(f : X ⟶ S)`. Properness is `[IsProper f]`. I opened Mathlib's proper-morphism
  definition: separated, universally closed, locally finite type, with quasi-compactness
  supplied by universal closedness, agreeing with the node's finite-type formulation.
- G is an abelian small-etale sheaf: `Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}`. This is the category in def-weil-pbc-etale-sheaves and
  def-weil-pbc-abelian-etale-sheaves, rather than a fixed-ring module category.
- Torsion is `hG : G.IsTorsion`. I opened SheafCohomology.Basic: it quantifies over
  sections and a covering sieve on which their restrictions have finite additive order.
  Thus the annihilator may vary locally and no common integer or finite stalk is assumed.
- Relative local acyclicity is `hf : IsLocallyAcyclicRelative f G`. I opened
  LocalAcyclicityAbelianSheaf: it quantifies over every geometric x and every geometric
  t of the strict localization of f(x); it asserts invertibility of the actual alpha
  map in degree zero and vanishing in every positive degree. Its strict-local map is
  selected from a uniqueness statement, its fibre is the actual pullback, and alpha
  uses the uniquely characterized restriction and inverse-image comparison. These are
  exactly the objects and conditions of the dependency node.
- Every nonnegative integer is `(q : ℕ)`, cast to ℤ for the cohomology functor.
  The order is q, then s, then t, as in the node.
- s is `(s : Spec (.of Ω) ⟶ S)` with `[Field Ω] [IsAlgClosed Ω]`.
  The strict henselization is `Scheme.strictHenselizationScheme s`. I opened its
  construction: the spectrum of the small representative affine pointed-neighbourhood
  ring colimit. The structural map is the common composite of its limit projections.
- t is `(t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)` with its own
  field and algebraic-closure instances. There is no algebraicity or prescribed-image
  hypothesis on this geometric point.
- R^q f_* G is the explicit composite of `Plus.singleFunctor _ 0`,
  `rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f`, and
  `Plus.homologyFunctor _ (q : ℤ)`. I opened UpperLowerStar.Defs and
  Derived.UpperLowerStarCoherence: lowerStar evaluates on the base-change etale object,
  and rightDerivedLowerStarPlus is its bounded-below right derived functor.
- The two stalks in `etaleStalkSpecialization s t` are `pointSmallEtale s` and
  `pointSmallEtale (t ≫ strictHenselizationStructuralMap s)`. I opened the Mathlib
  point and sheafFiber definitions: these are the colimits over pointed neighbourhoods,
  hence the stalks in the recorded dependency. The target is at the composite on S.
- The conclusion is `IsIso` of that particular homomorphism in AddCommGrpCat.
  This asserts exactly that the specialization homomorphism is an isomorphism of
  abelian groups; it asserts neither an unspecified isomorphism nor cospecialization.

I also read the new definition node def-weil-pbc-etale-stalk-specialization as a
stage-1 node against 0GJ2. Its introduced S, s, F, structural g and arbitrary t,
its source and target, and its two equivalent germ descriptions agree with that source.
The Lean first chooses `existsUnique_strictHenselizationStalkRestriction s F`, whose
property fixes its composite with every representative neighbourhood germ. I opened
that theorem and its defining property and section restriction: the components are
precisely inverse-image unit followed by the strict-local neighbourhood section.
Thus the choice determines the map uniquely; it is not data chosen from an
unspecified existence assertion. `ΓNatIsoSheafSections.hom` then evaluates global
sections at the terminal etale object, `toPresheafFiber` takes the germ at t, and
`upperStarCompSheafFiberIso.hom.app F` identifies the pullback stalk with the composite
stalk. I opened the latter declaration and checked its direction. This is exactly
the alternative description of specialization following the germ construction in 0GJ2.
There are no new dependency modules in this delivery. The new node has the prescribed
fields, chapter, unit, ancestry, source, dependency citations and search records;
the item adds only this new definition to its statement dependencies.

Edge cases: q=0 is included; there is no positive-degree restriction on the theorem.
The zero sheaf and empty X are allowed; empty S admits no s and makes the assertion
vacuous. A t at the strict-local closed point is allowed, as is any geometric
generization and any transcendental algebraically closed test field. No prime,
nonzero coefficient, fixed annihilator, smoothness, finite stalk or local constancy
condition is present. Universe u is arbitrary and the scheme/point universes match
the recorded strict-henselization and geometric-stalk interfaces; the abelian values
use the established u+1 encoding. Every term and universe variable is explicitly bound.
There is no index-set nonemptiness hypothesis in this statement.

Independent searches, using different wording from the first worker:

- msearch LeanFinder: `torsion etale cohomology proper pushforward invariant under
  geometric generization` returned eight etale-algebra/locus results, no such theorem.
- msearch Loogle: `"sheafFiber", "IsIso"` returned four generic point/sheafification
  and monoidal instances, no specialization construction or theorem.
- msearch grep: `strict.*stalk.*special|special.*stalk.*etale|cospecialization`
  returned zero hits.
- Direct rg in the source WeilConjectures/SixFunctors, Mathlib CategoryTheory/Sites,
  and project lean/Sheaf/AlgebraicGeometry, using `specialization`, `cospecialization`
  and `generization`, found no duplicate. The finite-etale fibre map, topological
  stalkSpecializes, and statements about fibre cardinalities concern different objects.
- `blueprint_refs.py search 'stalk specialization'` returned zero blueprint nodes.
  I also checked the new node's recorded DAG searches and existing restriction/stalk
  dependencies; they supply components, not a duplicate specialization notion.

The new definition node omitted explicit dependency citations for scheme and geometric
point. I added [def-pc-scheme] and [def-weil-geometric-point] with their stmt_deps
entries, and made explicit that F is on the small etale site of S. Its mathematical
meaning is unchanged. No mismatch in either Lean declaration was found; neither Lean
signature, definition, item statement nor proof plan was changed. Both declaration docstrings cite their source and blueprint node; the
statement docstring follows all five node proof steps, including the actual-map
identifications. The theorem has only `sorry`, and the definition is a real composition
with no sorry data or new proof. The second reading adds this independent audit and repairs those new-node citations.
