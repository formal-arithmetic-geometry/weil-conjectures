## Worker report

The module `Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing` states
`AlgebraicGeometry.ProEtale.subsingleton_cohomology_comparisonUpperStar_obj_of_injective_of_isAffine`.
Its only proof is `sorry`; no definitions, helper nodes or dependency repairs are introduced.
The natural statement is unchanged. Source read in full: Stacks `proetale.tex`,
Tag 099U, `lemma-affine-vanishing`, statement and proof. The theorem docstring
records all nine DAG proof steps, including both Cech-colimit reductions,
compatibility with face maps, fixing the descended cover target, and empty covers.

Clause-by-clause correspondence:

- “Let Y be an affine scheme”: `(Y : Scheme.{u}) [IsAffine Y]`.
- The small etale site: `Y.smallEtaleTopology`, with objects `Y.Etale`.
- The small pro-etale site: `Scheme.ProEt.topology Y`, inferred in the result type
  of `comparisonUpperStar`. These are the prescribed weakly etale site and its
  fpqc topology, with site object universe u+1 and arrow universe u.
- The comparison geometric morphism: `comparisonUpperStar AddCommGrpCat.{u + 1} Y`.
  Its data is exactly `Functor.sheafPullbackConstruction.sheafPullback (toProEt Y)`
  followed by sheafification, the same construction as `Scheme.proEtaleSiteComparison`
  for sets, now on abelian groups. It is not an arbitrary adjoint or map.
- “For every injective abelian sheaf J on Y_et”:
  `(J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]`.
  AddCommGrpCat imposes no finite-ring, torsion or constructibility condition.
- “Every integer q > 0”: `(q : ℕ) (hq : 0 < q)` ranges over exactly the positive
  integer degrees. There is no asserted degree-zero vanishing.
- “H^q(Y_proet, nu_Y^(-1) J) = 0”: `Subsingleton (@Sheaf.H _ _ _
  ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J) _ (HasExt.standard _) q)`.
  `H` is the Ext-from-constant-Z realization of right derived global sections,
  used by the recorded sites-and-cohomology interface. Its value is a type carrying
  an abelian group, so `Subsingleton` is exactly the zero-group assertion. Explicit
  `HasExt.standard` chooses the available size model, without an added assumption.
- No Noetherian, dimension, coefficient-ring or other hypothesis is added.

Dependency declarations read and used (through the indicated public import closures):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`;
  its public Mathlib import supplies `Scheme.ProEt` and `Scheme.ProEt.topology`.
  The derived category of modules over a constant ring is not substituted for abelian sheaves.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`;
  its public upstream import `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`
  supplies `AlgebraicGeometry.ProEtale.comparisonUpperStar` with arbitrary
  Grothendieck abelian coefficients, including AddCommGrpCat.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: its public
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` supplies `CategoryTheory.Sheaf.H`;
  `HasExt.standard` is from Mathlib's derived-category Ext basic module.

All recorded proof-dependency modules are imported privately unless already public.
Unstated proof prerequisites are not needed to type the theorem and are not waited on.
The available general upstream cohomology-comparison/acyclicity theorems are not an
exact existing statement of affine vanishing for pulled-back injective abelian sheaves.

Edge cases checked mathematically: q=1 is included; q=0 is correctly excluded since
injectives need not have zero global sections. The zero sheaf and empty affine scheme
are included; the empty scheme has the empty covering and zero positive cohomology.
Non-Noetherian affine schemes and injective sheaves with arbitrary torsion or
non-torsion sections remain allowed. There is no relation imposed between the
object and morphism universes of either site. The coefficient universe u+1 is the
common larger site universe from the recorded size convention.

Searches for an existing declaration:

- `msearch.py leanfinder`: “Higher proetale cohomology on an affine scheme of the
  comparison pullback of an injective abelian etale sheaf vanishes”. Eight hits:
  cotangent-complex/formally-etale lemmas, affine-limit sections, and
  `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`; none is the statement.
- `msearch.py loogle`: `"ProEt", "Injective"`. Zero hits.
- `msearch.py grep`: `proetale.*vanish|comparison.*acyclic|affine.*vanishing`.
  Zero Mathlib hits.
- `msearch.py leansearch`: “The pullback of an injective abelian etale sheaf has
  vanishing higher proetale cohomology on an affine scheme”. Service unavailable
  (Internal Server Error); no verdict assigned to that search.
- `rg` of upstream WeilConjectures and side Sheaf for affine vanishing, comparison
  acyclicity and abelian comparison found unrelated quasi-coherent vanishing and
  general comparison material. Read `Comparison/Defs.lean`, `LowerStarAcyclic.lean`
  and the affine-basis module; no exact affine injective vanishing declaration.
- `rg` for the blueprint id in upstream WeilConjectures: no hits. Search for the
  proposed full declaration name in side/upstream sources: no collision.

Validation: the required `scompile.py NA lem-cbc-abelian-affine-comparison-vanishing`
compiled this file both in its sandbox and at its intended library path cleanly.
No statement dispute or node fault was found. The independent second reading is
left to the dispatcher-appointed reader, as required.


## Second reading by NA

Independently read the node and all six statement-dependency records, their actual
Lean declarations, the delivered module, and Stacks `proetale.tex`, Tag 099U
(`lemma-affine-vanishing`), including its complete proof and the adjacent comparison
and continuity lemmas. The source assumes only affineness of the base and injectivity
of an abelian sheaf. There are no ambient Noetherian or coefficient hypotheses.

Object/hypothesis/conclusion checklist, with verdicts:

1. Affine scheme Y: `(Y : Scheme.{u}) [IsAffine Y]`. Matches the scheme and affine
   notions of def-pc-scheme, without a chosen presentation or extra hypotheses. Pass.
2. Small etale site: `Y.smallEtaleTopology`, on `Y.Etale`, read in Mathlib's
   `Sites/Etale.lean`; this is the recorded topology of jointly surjective etale
   families. Pass.
3. Small pro-etale site: the codomain of `comparisonUpperStar` is
   `Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}`. Read the imported
   `ProEtaleDerivedCategory` and Mathlib `Sites/Proetale.lean`: the objects are weakly
   etale Y-schemes and the topology is generated by fpqc weakly etale covers.
   The constant-ring derived category from that dependency is not used instead
   of abelian sheaves. Pass.
4. Canonical comparison morphism: `comparisonUpperStar AddCommGrpCat.{u + 1} Y`.
   Read `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and upstream
   `SixFunctors/ProEtale/Comparison/Defs.lean`. This is literally the constructed
   sheaf pullback along `Scheme.toProEt Y`, using left Kan extension followed by
   sheafification, the same construction recorded for sets in the dependency.
   The abelian coefficient specialization needs no finite-ring assumption. Pass.
5. Every injective abelian etale sheaf J:
   `(J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]`.
   Read `CategoryTheory.Injective` in Mathlib: extension along every mono is its
   defining condition. J is injective on the original etale site, not asserted
   injective after pullback. No torsion or constructibility restriction. Pass.
6. Every positive integer degree: `(q : ℕ) (hq : 0 < q)`. Natural positive degrees
   represent all positive integer degrees, and quantification follows J. Pass.
7. Zero right-derived global sections:
   `Subsingleton (@Sheaf.H _ _ _
     ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J) _ (HasExt.standard _) q)`.
   Read `Sheaf.H` in Mathlib `Sites/SheafCohomology/Basic.lean`: it is Ext from
   the constant ULift-Z abelian sheaf, hence derived global sections, not the
   cohomology of an arbitrary object. Its abelian-group carrier is trivial exactly
   when Subsingleton holds. Read `HasExt.standard`: this chooses the standard
   Ext size model, adding no mathematical hypothesis. Pass.
8. No additional hypotheses: the complete signature has exactly Y, affineness,
   J, injectivity, q and positivity. No dimension, Noetherian, finite-ring,
   torsion, characteristic or extra Ext-existence assumption. Pass.

Edge cases: q=1 is included and q=0 is excluded as required; zero sheaves and the
empty affine scheme are allowed. No nonemptiness is imposed on Y or a covering;
the proof docstring explicitly treats empty covers and their zero Cech complexes.
There is no index type in the signature. Arbitrary characteristic and
non-Noetherian rings are allowed. The site object universe is u+1 and morphism
universe u; coefficients in u+1 follow the recorded larger-universe convention.
No equality of these universes or unbound universe/variable is introduced.

Independent H4 searches used different queries from the worker:

- `msearch.py ... leanfinder "positive degree cohomology of the inverse image of
  an injective sheaf on the small etale site over an affine scheme"`: eight hits,
  concerning K-injectives, injective resolutions, local representability and
  affine-limit sections; no exact statement.
- `msearch.py ... loogle '"Sheaf.H", "Injective"'`: zero hits.
- `rg` in Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `affine.*(acyclic|injective)`, `injective.*affine`, and comparisonUpperStar
  vanishing/Subsingleton combinations: no exact existing statement. Opened the
  closest upstream matches in `Comparison/LowerStarAcyclic.lean`: the global
  cohomology comparison takes vanishing as a hypothesis; the relative-sections
  theorem quantifies over qcqs morphisms and affine pro-etale test objects.
  Neither is this exact affine-base Sheaf.H statement. Also inspected the
  comparison affine and continuity modules. The proposed full declaration name
  has no collision in upstream names, upstream sources or project Lean.

H5/H6/H8/H9: there are no definitions, new nodes or dependency modules to audit.
The only theorem has the entire proof `by sorry`. Module and theorem docstrings
name Stacks 099U and the correct blueprint id. The theorem docstring carries all
nine node proof steps, both Cech-colimit passages, face-map compatibility, cover
and target descent, and the fixed etale-site injectivity argument. Proof dependency
imports are retained. The node differs from the repository node only in `lean`;
its `lean.statement` is verbatim the theorem signature. No statement correction
or citer audit is required.

Mismatches found: none. Changes: appended this independent reading only; preserved
the correct Lean module and node record.
