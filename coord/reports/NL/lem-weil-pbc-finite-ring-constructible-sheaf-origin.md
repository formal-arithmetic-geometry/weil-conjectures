## Worker report

The main module states `AlgebraicGeometry.Scheme.finiteRing_constructibleSheaf_origin` with `sorry`; no proof is supplied. It asserts an equivalence of the full categories selected by the two recorded constructibility predicates. It pins that equivalence to the canonical module-valued comparison pullback by an additive natural isomorphism and explicit constant-scalar linearity on every object and section. This is the module-sheaf comparison, rather than an unrelated equivalence of the abstract categories.

Hypotheses and clauses:

- Arbitrary scheme T: `(T : Scheme.{u})`; there is no qcqs, Noetherian, nonempty or base-field assumption.
- Finite commutative ring B: `(B : Type u) [CommRing B] [Finite B]`. The étale module category uses `ULift.{u+1,u} B` to match its recorded larger-universe coefficient interface. This is the very lift used in the recorded pro-étale constant ring; no coefficient field, valuation quotient, nonzero or characteristic assumption is added.
- The small sites are `T.smallEtaleTopology` and `ProEt.topology T`. Their inclusion and pullback are the recorded `ProEtale.comparisonUpperStar`, imported through `ProEtaleSiteComparison`.
- Constructible étale module sheaves form `(IsConstructibleEtaleModuleSheaf (T := T) (Λ := ULift B)).FullSubcategory`. This uses the existing predicate, finite global immersed partitions with constructible parts and finite constant module trivializations on each stratum.
- Intrinsically constructible pro-étale module sheaves form `(IsIntrinsicallyConstructibleProEtaleModuleSheaf T B).FullSubcategory`. The §1(B) repair below states the dependency as written: positive finite global immersed partition, constructible parts, canonical constant-coefficient restriction, local constancy and finite geometric module stalks.
- Equivalence: the existential `e : ... ≌ ...` includes inverse, unit, counit and naturality; both are full subcategories, so no morphisms are removed.
- Induced by ν*: `α` is a natural isomorphism from the étale full-subcategory inclusion followed by the recorded comparison pullback and additive forgetful functor to `e.functor` followed by the pro-étale inclusion and `SheafOfModules.toSheaf`.
- Module structure: for every constructible G, every pro-étale site object U, every lifted coefficient b and every section m, the final equality says `α(b • m) = unit(b) • α(m)`. Here `unit` is exactly `toSheafify` of the constant CommRingCat presheaf. Thus α is linear for the constant coefficient ring. Together with the additive isomorphism this is precisely the canonical identification between the two encodings of B-module sheaves; its inverse is also linear. It is not merely an identification of underlying sets or groups.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`: `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` (existing predicate, read in full).
- `Sheaf.Paper.IntrinsicConstructibleProEtaleModuleSheaf`: `AlgebraicGeometry.Scheme.IsIntrinsicallyConstructibleProEtaleModuleSheaf` (repair of def-weil-proetale-constructible-sheaf).
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, identifying the imported `AlgebraicGeometry.ProEtale.comparisonUpperStar` with the specified fixed-coefficient adjunction. Its source and the upstream comparison functors were read in full.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the original small site and coefficient presentation, reused through the dependency imports; `proEtaleConstantRing` and `proEtaleRingModules` come through `ProEtaleInverseImage` and `ProEtaleOperations`.
- `LocallyClosedStratification`, `IsLocallyConstantProEtaleModuleSheaf`, `proEtaleConstantModulePullback`, `proEtaleGeometricModuleStalk` and `proEtaleConstantRing` are the dependency declarations used by the repaired predicate; none is copied.
- Mathlib `ObjectProperty.FullSubcategory`, `ObjectProperty.ι`, `SheafOfModules.toSheaf`, `sheafCompose` and `toSheafify` package the categories and coefficient identification.

The theorem docstring carries all six proof steps verbatim from the node, wrapped to the line limit. Recorded proof-dependency modules are imported without `public`, including finite locally constant values, weakly étale localization, local closed-stratum selection, distinguished triangles, homology sequences, degree-zero recovery, right-derived degree zero, closed/affine morphism permanence and enough injectives. Proof dependencies with no recorded declaration are not imported and do not prevent stating this theorem. The main statement and proof route are unchanged.

Edge cases checked: zero coefficient ring (the lift and constant unit are still unital ring constructions); zero sheaf; empty scheme (the étale empty partition is allowed, while a positive partition with an empty stratum represents the same constructibility on the pro-étale side); empty strata; arbitrary non-qcqs schemes (the predicates keep their global finite-partition convention); nonreduced strata (the actual scheme immersions and canonical restrictions are retained). No restriction on the small site's distinct object/morphism universes is imposed. The universe lift changes no finite coefficient ring or finite module values.

Searches made before writing:

- msearch.py leanfinder: “Pullback from etale to proetale induces an equivalence of constructible finite ring module sheaves”: eight hits, chiefly étale morphism instances and module pullback/free-module lemmas; none is this statement.
- msearch.py loogle: `"Constructible", "Sheaf"`: zero hits.
- msearch.py grep: `constructible.*pro.etale|pro.etale.*constructible`: zero hits.
- msearch.py leansearch: “Constructible finite coefficient module sheaves etale proetale comparison equivalence”: unavailable, Internal Server Error; no absence claim based on it.
- Direct rg in Mathlib, upstream WeilConjectures, side WeilConjectures and lean/Sheaf for constructibility/equivalence and this node id: no existing declaration of this theorem. Nearby results concern étale qcqs affine-local constructibility and unrelated open restrictions.
- Searched DAG/source for constant-ring/module-valued encoding bridges: existing étale-only equivalences and the special ZMod-r lift bridge do not apply to these pro-étale sheaf objects. No encoding bridge is duplicated: the statement uses an explicit linear natural isomorphism between the recorded encodings.
- Direct full-name searches for `finiteRing_constructibleSheaf_origin` and `IsIntrinsicallyConstructibleProEtaleModuleSheaf` in Mathlib, upstream and side sources found neither name.

Source checked directly: literature/stacks-project/proetale.tex, lemma-compare-constructible (09AK) and lemma-compare-locally-constant (099Y). The DAG explicitly requires the global finite-partition refinement; the Lean preserves this convention rather than replacing it by the affine-local Stacks definition.

No STATEMENT-DISPUTED flag. The item's natural-language statement is unchanged. The dependency fault below is repaired explicitly.

## Dependency modules

`def-weil-proetale-constructible-sheaf`: the recorded `Sheaf.Paper.ProEtaleConstructibleSheaf` predicate did not require constructibility of its strata. Reading `LocallyClosedStratification` confirmed that it imposes only a finite locally closed partition and immersed scheme structures, so it does not imply that missing condition. The dependency node explicitly requires constructible parts. The replacement module `Sheaf.Paper.IntrinsicConstructibleProEtaleModuleSheaf` states its exact notion, adding `(∀ i : Fin S.n, Topology.IsConstructible (S.stratum i))` and retaining all its other clauses. Only this dependency's lean record changes, with lean.note explaining the unusable old record. The old predicate is not used to define the new one. This is §1(B), not a change to the dependency's mathematical statement.

Validation: every delivered module is checked separately via scompile.py, with dependency ordering and the standard per-file limit. The prescribed deliver2.py --no-push dry run is the final check; no delivery is pushed by this worker.

## Second reading by NL

Read the item JSON and both originally proposed modules independently, with Stacks
`proetale.tex`, lemma-compare-constructible (09AK), definition-constructible (09AJ),
and lemma-compare-locally-constant (099Y) open. Also read the blueprint
`sec-smooth-purity/sk-def-sf-operations/def-weil-finite-torsion-constructibility.md`,
second paragraph. Stacks assumes a Noetherian coefficient ring in 09AK, automatic
for a finite commutative ring, and no qcqs hypothesis on the scheme. Its definition
is affine-local; the node explicitly asks for the global finite-partition refinement.
The Lean keeps that refinement on both sides.

Object/hypothesis/conclusion checklist (each verdict is pass after the repair below):

1. Arbitrary scheme T: `(T : Scheme.{u})`; no qcqs, separatedness, Noetherian,
   nonempty, characteristic, or field instance is assumed.
2. Finite commutative ring B: `(B : Type u) [CommRing B] [Finite B]`.
   `ULift.{u + 1, u} B` is the coefficient presentation used by the existing
   constant ring, not a different finite ring or a valuation quotient.
3. Small etale and pro-etale sites and their comparison: the source of
   `ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift B)) T` is
   `Sheaf T.smallEtaleTopology ...` and its target is `Sheaf (ProEt.topology T) ...`.
   Read `ProEtaleSiteComparison.proEtaleSiteComparisonModules` and upstream
   `SixFunctors/ProEtale/Comparison/Defs.lean`: it is the specified inclusion's
   left Kan extension followed by sheafification, with restriction as right adjoint.
4. Etale constructibility: the first `ObjectProperty.FullSubcategory` uses the
   recorded `IsConstructibleEtaleModuleSheaf`. Read its complete body: it chooses
   an immersed finite global locally closed partition, constructible parts, and
   `Etale.upperStar` restrictions with finite constant module trivializations.
   All objects and all module-sheaf morphisms are retained by the full subcategory.
5. Intrinsic pro-etale constructibility: the second full subcategory now uses
   the recorded `IsConstructibleProEtaleModuleSheaf T B`. Read its body, as well as
   `LocallyClosedStratification`, `Topology.Stratification`,
   `IsLocallyConstantProEtaleModuleSheaf`, `proEtaleConstantModulePullback`, and
   `proEtaleGeometricModuleStalk`. It requires positive finite partition size,
   immersed locally closed constructible parts, canonical constant-coefficient
   restriction, local constant module trivializations and finite geometric stalks.
   The restriction is tensor extension along `proEtaleCoefficientInverseImageMap`,
   constructed from the constant-section map and comparison counit; it is not an
   arbitrary coefficient identification. The stalk is the colimit module over
   pointed pro-etale neighbourhoods, with the scalar action from the colimit ring.
6. Equivalence induced by pullback: `∃ e : ... ≌ ...` packages full faithfulness
   and essential surjectivity. `∃ α : ... ≅ ...` identifies its forward functor
   naturally on underlying additive sheaves with the specified comparison pullback.
7. B-module identification: the final universal quantifiers over `G`, `U`, `b`,
   and `m` impose `α(b • m) = toSheafify(b) • α(m)`. The right scalar is exactly
   the constant-section unit into `proEtaleConstantRing T B`. Additivity comes
   from the components being additive-group morphisms. Locally every section of
   the constant ring sheaf comes from a constant scalar; sheaf naturality and this
   equality therefore give linearity over the whole ring sheaf. The inverse
   inherits linearity from bijectivity. Thus the equivalence concerns module sheaves
   with the canonical pullback structure, including morphisms.

Mismatch found and repaired (H4/H13): the worker's claimed missing constructibility
condition was already inherited. `LocallyClosedStratification` extends
`Topology.Stratification`, whose current actual declaration has the field
`isConstructible_stratum : ∀ i, IsConstructible (stratum i)`. Confirmed directly
using `scompile.py --source WeilConjectures.Topology.Stratification`, rather than
trusting the outdated docstring saying no constructibility is imposed. Also read
`scompile.py --source Sheaf.Paper.ProEtaleConstructibleSheaf`: its recorded predicate
is usable exactly as written. Removed the proposed duplicate
`IntrinsicConstructibleProEtaleModuleSheaf.lean` and its dependency JSON copy;
changed the main import and all predicate occurrences back to the recorded
`Sheaf.Paper.ProEtaleConstructibleSheaf` declaration. Updated `lean.statement`
verbatim. The worker report's proposed dependency repair above is withdrawn;
there are no dependency modules or new nodes in the final delivery. This is a
Lean-only repair; the natural-language statement, dependencies and proof are unchanged.

Edge cases: for empty T the etale zero-length partition is allowed, and the
pro-etale positive-length requirement is satisfied by one empty stratum. Empty
strata are not ruled out by either predicate. The zero sheaf and zero finite ring
are permitted; no `Nontrivial` assumption appears. There is no n or prime parameter
in this theorem and no characteristic restriction. Arbitrary non-qcqs schemes and
nonreduced stratum scheme structures remain covered. The universe variable u is
explicit; site objects have the existing larger object universe and their original
morphism universe. No equality between those universes is imposed. Finite rings
can be represented in the scheme universe without losing a ring isomorphism class;
module/sheaf values use u+1 as required by both recorded interfaces. Geometric
fields are in the scheme universe, which contains algebraic closures of its
residue fields; this is not a smaller independent test universe.

Independent searches performed: msearch leanfinder query
`equivalence etale proetale sheaves finite discrete coefficients` returned eight
hits, including smallEtaleTopology and LightCondMod.isDiscrete_tfae, none the
required equivalence. msearch loogle `"comparisonUpperStar"` returned zero hits.
Direct rg for `constructible.*(equiv|comparison)`, its reversed order, and both
proposed declaration names searched Mathlib CategoryTheory/AlgebraicGeometry,
slopmaster2 WeilConjectures, the group's current WeilConjectures framework and
lean/Sheaf. Opened the closest hit in full:
`ProEtale.isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`
in `SixFunctors/ProEtale/ConstructibleSheaf.lean`. Its predicate uses fixed-module
sheaves and coverwise finite values and its conclusion is an essential-image
criterion; it does not state the present equivalence for the recorded intrinsic
ring-sheaf-module predicate. It is a related proof input, not an exact existing
attachment. Also read `ConstructibleSheaf/ProEtaleModule/Def.lean`: its module-object
finite-presentation predicate is not this recorded intrinsic predicate. No exact
existing theorem was found. The duplicate dependency predicate was found and
removed as described above.

H5/H6/H8/H9: the only delivered declaration is the named theorem with whole proof
`sorry`; there is no definition, choice of data, hidden proof or proved helper.
Its module and declaration docstrings name 09AK/099Y and the item blueprint id.
Compared all six natural-language proof steps to the node: preservation, full
faithfulness, Zariski locality, extension closure, stratum induction and recovery
on the original partition are retained. No file-local instances/notation or
unbound variables occur. All delivered Lean lines satisfy the 100-column limit.

Validation: the repaired single module passed scompile.py with no errors or
warnings (sandbox 2.0 seconds, library module 2.2 seconds). Only the theorem's
`lean` record differs from the base node. The prescribed no-push preflight is
run after this report, followed by delivery if it prints OK.
