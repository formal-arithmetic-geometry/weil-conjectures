## Worker report

The module `Sheaf.Paper.ProfinitePointPullback` states the node using the published
51-module pro-etale framework. All 28 declarations are listed in `lean.declarations`.
Every new theorem proof is `sorry`; every definition has actual data.
The natural-language statement and dependency lists are unchanged. There are no
new nodes, dependency repairs, or statement disputes.

Source read: the specified read-only master `RefactorInstruction.tex`, Section 4,
Lemma `lem:XS` and Proposition `prop:pX` (including the explicit Kan-extension proof),
and Section 5, `eq:basechange-XS`, `eq:triangle`, Theorem `thm:alpha` and its proof.
Also read the exact group-clone framework, especially
`WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean` and
`ModuleObject/UpperLowerStar/Defs.lean`, and `coord/pefw-upstream-framework.md`.

The node has several substantial clauses, so its complete statement is the family
of declarations in the one module; the primary declaration states the geometric
and monoidal part. The later declarations explicitly state the coherence laws,
including normalized square comparisons. They are not replaced by a bare assertion
that some unrelated natural isomorphism exists.

Clause-by-clause correspondence:

| Natural-language hypothesis or clause | Lean rendering |
| --- | --- |
| Smaller universe, profinite spaces and continuous maps | Explicit `universe u`, `Profinite.{u}` and its existing category; no restriction to nonempty spaces |
| Finite jointly surjective covering families | `coherentTopology Profinite.{u}`; preservation of the generated Grothendieck topology is `CoverPreserving`, equivalently preservation of its finite jointly surjective generators |
| Larger sheaf universe | `Type (u + 1)` and `Ab.{u + 1}` throughout; scheme sites retain object universe `u+1`, Hom universe `u` |
| Any scheme and its small pro-etale site | `X : Scheme.{u}`, `Scheme.ProEt.topology X`; no Noetherian, finiteness, separation or nonemptiness assumption |
| `a(S) = Spec LC(S,Z)` and precomposition on arrows | Existing `profiniteToProEt`, built from `profiniteToCommRingCatOp` and `profiniteToScheme`; `LocallyConstant.comapRingHom` supplies precomposition and `Scheme.Spec` reverses arrows |
| `a(S)` weakly etale over `Spec Z` | First conjunct of `profinite_point_pullback`: `∀ S, WeaklyEtale (toSpecZ (profiniteToScheme.obj S))` |
| Finite-limit preservation | `PreservesFiniteLimits profiniteToProEt.{u}` |
| Cover preservation | `CoverPreserving (coherentTopology Profinite) (Scheme.ProEt.topology specZ) profiniteToProEt` |
| Existence of the left Kan extension | Separate quantifications over all set-valued and abelian-valued presheaves, asserting `profiniteToProEt.op.HasLeftKanExtension F` |
| Sheafified Kan extension is a geometric inverse image | `profinitePointSetInverseImage` is the actual `Functor.sheafPullbackConstruction.sheafPullback`; the theorem asserts its adjunction to restriction, finite-limit preservation and preservation of all colimits in the chosen universe |
| Abelian inverse image is exact | Existing `pointUpperStar`, with its existing additive instance; the theorem asserts preservation of finite limits and finite colimits |
| Strong symmetric monoidal for sheaf tensor | `Nonempty pointUpperStar.Monoidal` and `.Braided` for the existing sheaf tensor structure; the latter expresses compatibility with the symmetric braiding |
| `p_T^* = pi_T^{-1} a^*` | Existing `upperStarFromPoint T := pointUpperStar ⋙ (toSpecZ T)^*[Ab]`; `toSpecZ` is the terminal scheme structure morphism |
| Canonical comparison for every `h` | Existing `upperStarFromPointComp h`, whose definition is the inverse-image composition isomorphism followed by `comp_toSpecZ h`; monoidality is explicitly asserted for every `X,Y,f` |
| Identity compatibility of the point comparisons | First conjunct of `profinite_point_pullback_coefficient_coherence`, evaluated on every condensed abelian sheaf |
| Composition compatibility of the point comparisons | Second conjunct: `upperStarComp` followed by pullback of the comparison for `g` and the comparison for `f` equals the comparison for `f ≫ g` |
| Abelian composition comparisons: both units | First two conjuncts of `profinite_point_pullback_abelian_coherence`, with the transports `Category.id_comp` and `Category.comp_id` explicit |
| Abelian composition comparisons: associativity | Third conjunct, with `Category.assoc` transport explicit; the equation is stated on every sheaf, hence is the corresponding natural-transformation equation |
| Monoidal composition and identity comparisons | `profinitePoint_isMonoidal_upperStarComp` and `profinitePoint_isMonoidal_upperStarId` |
| Ring lifts of the comparisons | `profinitePointRingComp` and `profinitePointRingIdentity` use `Functor.mapMonNatIso`, `mapMonCompIso`, and `mapMonIdIso`; `profinite_point_pullback_ring_coherence` states both unit laws and associativity on all ring objects |
| Coefficient ring comparison is the stipulated abelian map | `profinite_point_pullback_ring_comparison`: the underlying map of `coefficientPullbackIso f Λ` is exactly `(upperStarFromPointComp f).hom.app Λ.X` |
| Module lift over a condensed commutative ring | Quantify over every `Λ : Sheaf (coherentTopology Profinite) Ab` with `[MonObj Λ] [IsCommMonObj Λ]`, using the framework `CondensedRing.upperStar`, its specified scalar-extension construction and coefficient isomorphism |
| Module identity is canonical | `existsUnique_profinitePointModuleDirectImageIdentity` uniquely specifies the direct-image isomorphism by its underlying abelian map; `profinitePointModuleDirectImageIdentity` selects this uniquely determined object and `profinitePointModuleIdentity` is its adjunction conjugate |
| Underlying abelian normalization of module pullback | `profinitePointModuleForgetPullbackIso` uses the actual `Mod.extendScalarsIsoComapInv`, not a chosen arbitrary map |
| Exactness and linear-lift normalization | `profinite_point_pullback_module_comparison` states exactness, identity normalization, and the equation identifying module composition with abelian composition after forgetting the action |
| Module composition comparisons: units and associativity | `profinite_point_pullback_module_coherence`, using the normalized identity and the existing `CondensedRing.upperStarComp` |
| Derived functors act termwise | Existing `Functor.mapDerivedCategory` for the exact abelian and module inverse images; their factorization is Mathlib `mapDerivedCategoryFactors` |
| Derived comparison constructions | `profinitePointAbelianDerivedComp/Identity` and `profinitePointModuleDerivedComp/Identity` explicitly use `Functor.mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, `mapDerivedCategoryIdIso`; these are the localization-normalized termwise lifts |
| Derived units and associativity | The first three conjuncts of `profinite_point_pullback_abelianderived_coherence` and `profinite_point_pullback_modulederived_coherence` |
| Any commutative square, common-composite comparison | Fourth abelian conjunct uses the inverse first-route comparison, transport by the square equality, and the second-route comparison; its point-comparison compatibility is explicit. `profinite_point_pullback_module_square` identifies its linear lift with precisely that abelian map |
| Derived square is the descent of this same square map | Fourth conjuncts of both derived coherence theorems equate their square comparisons to `mapDerivedCategoryNatIso` of the ordinary common-composite square, normalized by the derived-composition isomorphisms |

The ring-object presentation is the framework's existing `Mon (Sheaf J Ab)`: its
objects have the abelian addition together with bilinear associative unital
multiplication, and its maps preserve both structures. Commutativity is retained
by braided inverse image. Similarly, its existing `Mod (Sheaf J Ab) R` packages
an abelian sheaf with an `R`-action satisfying the module equations; bilinearity
means that the sectionwise actions are linear and restrictions semilinear, exactly
the general module-sheaf notion of `ringedSiteModules` / `SheafOfModules`.
No second category, sheaf tensor, ring action, or module pullback is defined here.
Derived categories occur for the abelian and module categories, as in proof step 7;
there is no derived category of the nonabelian category of rings.

Dependency declarations read and reused:

- `def-weil-size-convention`: its record is a metatheoretic convention, rendered by
  the explicit site and coefficient universe levels above.
- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its underlying site is the
  same `Scheme.ProEt.topology` used by the framework.
- `def-weil-pbc-sheafification`: `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`, used
  by the existing sheaf-pullback construction.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
  `SheafOfModules.positiveTensorPower`, `changeOfRings` and its recorded helpers;
  the sheaf tensor and scalar extension are the ones of that dependency, with the
  already published internal module-object construction used for condensed rings.
- `def-weil-proetale-inverse-image`:
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, its base-change,
  adjunction, ring and module helpers. The abelian specialization is definitionally
  the framework's `AlgebraicGeometry.ProEtale.upperStar` used in this module.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the exact-functor comparisons retain
  the published localization and its universe conventions.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`, read together with its `Hom` structure.

All stated proof dependencies are imported, including the generic site composition
and tensor theorems, group/ring lifting, algebraic-structure sheaves, profinite test
objects, and the Mathlib matches for composite adjunction, conjugation,
associativity of adjoint comparisons, exact derived factorization and localization.
Each theorem docstring carries its corresponding steps of the node's eight-step
proof. The generic comparison statements are used for the proof plan, while the
actual maps in the signatures are the published framework's canonical maps.

Edge cases checked before drafting:

- Empty profinite space: locally constant functions form the zero ring and its
  spectrum is empty. Cover preservation includes the empty covering of that object.
- Arbitrary schemes include the empty scheme and non-quasi-compact schemes; no
  affine, Noetherian, separated, or quasi-compact hypothesis was imposed.
- Identity scheme morphisms occur explicitly in all ordinary and derived unit laws.
- Commutative squares need not be cartesian and can contain identity arrows. Their
  equalities of composites are transported explicitly rather than silently omitted.
- Coefficients need not be finite, nonzero, flat or complete. The zero coefficient
  ring and zero modules are included. All complexes are unbounded and Z-indexed.
- The small-site object/Hom universes remain different; no extra equality or
  independent smaller test-object universe was imposed.

Searches actually run, with results also in the sandbox `searches.jsonl`:

- LeanFinder: "The inverse image from condensed abelian groups to proetale sheaves
  defined using spectrum of locally constant integer valued functions is exact
  symmetric monoidal": eight Mathlib hits on condensed modules and monoidality
  for the light site, no match for this full node.
- Loogle: `"Profinite", "Spec"`: zero hits.
- msearch grep: `pointUpperStar|upperStarFromPointComp`: zero Mathlib hits.
- LeanSearch: "inverse image sheaves profinite point preserves finite limits tensor":
  unavailable (Internal Server Error), not recorded as a negative match.
- ripgrep of the upstream, framework and project for `pointUpperStar`,
  `upperStarFromPointComp`, `profiniteToProEt`, `profiniteToScheme` found the actual
  framework constructions; the complete ring/module/derived coherence statement
  was not already present.
- Search for the node id in the old upstream checkout and project Lean found no
  existing declaration for the whole statement. Framework coherence sources were
  read by their actual signatures rather than inferred from names.

Validation: scompile.py compiled the complete module cleanly, in both its sandbox
and its actual module name, in 5.7 and 6.5 seconds respectively. The first connection
attempt failed before Lean diagnostics; its retry succeeded. A later elaboration
check identified the missing monoidality instances for the canonical identity and
composition comparisons. Those are now named statements of the corresponding node
clauses, with proof docstrings, rather than extra hypotheses on the theorem.
All lines have length at most 98. No local compiler or lake command was invoked
directly. The worker dry run is the final check; the independent second reader will
write its own section and deliver.

The worker preflight initially rejected `sorry` written directly as the body of the
two monoidality instances. They are now named `@[instance] theorem` declarations:
the postponed proof is a theorem, while the attribute makes it available to the
canonical ring-lift definitions. This changes neither their propositions nor the
maps. The independent second-reading section is intentionally left to the reader.

The geometric set-level comparison is also stated explicitly, not merely its abelian
specialization: `profinitePointSetSchemeInverseImage` is the composite along the
structure map, `profinitePointSetComp/Identity` are the adjunction conjugates of the
canonical direct-image comparisons, and `profinitePointSetSchemeComp` uses these
and `comp_toSpecZ`. `profinite_point_pullback_set_coherence` asserts finite-limit
preservation, identity, composition, and the common-composite square equation for
all condensed sets. This covers the geometric reading of the second paragraph
independently of its later abelian/ring/module specializations.

## Second reading by ND

I independently read the sandbox node and all 28 declarations, the exact master
RefactorInstruction.tex Sections 4–5 (lem:XS, prop:pX, basechange-XS, triangle,
thm:alpha), Stacks sites-modules.tex's pullback-module and adjoint-push-pull-modules
lemmas, and coord/pefw-upstream-framework.md. The source makes no Noetherian,
quasi-compactness, separation, nonemptiness, or coefficient finiteness assumption.
No statement_change or new/dependency node is present in this delivery.

My checklist of the objects, hypotheses and conclusions, with their Lean rendering:

| Node item | Lean rendering and verdict |
| --- | --- |
| Smaller-universe compact Hausdorff totally disconnected spaces and continuous arrows | `Profinite.{u}` and its existing category. Correct; no nonempty instance. |
| Topology generated by finite jointly surjective families | `coherentTopology Profinite.{u}`. Correct, including the empty cover of the empty object. |
| Larger-universe sheaves, any scheme and its small pro-etale site | `Type (u+1)`, `Ab.{u+1}`, `Scheme.{u}`, `Scheme.ProEt.topology`. Correct; small-site object/Hom levels are u+1/u. |
| LC(S,Z), pointwise ring operations, precomposition then spectrum | Framework `profiniteToCommRingCatOp` uses `LocallyConstant S ℤ` and `LocallyConstant.comapRingHom`; `profiniteToScheme` composes with `Scheme.Spec`; `profiniteToProEt` supplies the structure morphism. Correct, actual constructions. |
| Weak etaleness, finite limits, covering preservation | First three conjuncts of `profinite_point_pullback`. Correct, with the actual functor above. |
| Left Kan extension along a.op exists, then sheafification gives geometric inverse image | Separate set and abelian `HasLeftKanExtension` clauses; `profinitePointSetInverseImage` is Mathlib's sheafPullbackConstruction; its restriction adjunction, finite limits and all u+1-small colimits are asserted. Correct. |
| Abelian inverse image exact and strong symmetric monoidal for sheaf tensor | Finite limits/colimits of `pointUpperStar`, and its `Monoidal` and `Braided` structures. Correct; braiding is the existing symmetric sheaf braiding, with the framework's canonical oplax/lax structures. |
| p_T = pi_T inverse image after a inverse image | Existing `upperStarFromPoint` is `pointUpperStar ⋙ (toSpecZ T)^*`; set analogue `profinitePointSetSchemeInverseImage`. Correct. |
| Every h has canonical monoidal comparison, natural in coefficients | Existing `upperStarFromPointComp h` is the inverse composition comparison whiskered by pointUpperStar, followed by `comp_toSpecZ`; monoidality is the final primary conjunct. Set comparison is `profinitePointSetSchemeComp`. Correct, with no arbitrary isomorphism hypothesis. |
| Identity and composition of these point comparisons | `profinite_point_pullback_coefficient_coherence` and `profinite_point_pullback_set_coherence`. Correct component equations on every sheaf; functorial naturality is built into the natural isomorphisms. |
| Abelian composition comparisons have both units and associativity | First three clauses of `profinite_point_pullback_abelian_coherence`, with explicit equality transports for id_comp, comp_id and assoc. Correct order of pullbacks. |
| Ring lifts and their identity/composition coherence | `profinitePointRingComp/Identity` use mapMonNatIso and mapMonComp/IdIso; ring_coherence states both units and associativity. ring_comparison normalizes the coefficient component to upperStarFromPointComp. Correct; Mon of abelian sheaves encodes rings, including noncommutative ones. |
| Module lifts for every condensed commutative ring | Λ with MonObj and IsCommMonObj, existing `CondensedRing.upperStar` (mapMod then extension along condensedPullbackHom), and module_comparison/coherence. Correct; these are exactly the coefficient-preserving module sheaves of proof step 6. |
| Module comparisons use the specified underlying abelian map | `profinitePointModuleForgetPullbackIso` uses extendScalarsIsoComapInv; module_comparison identifies composition and identity after forgetting actions. The identity direct-image isomorphism is uniquely characterized, its inverse-image is adjunction conjugation. Correct; choice is from uniqueness, not bare existence. |
| Termwise derived functors and coherent comparisons | mapDerivedCategory and mapDerivedCategoryNatIso, with canonical composition/identity localization isomorphisms, in the two DerivedComp/Identity pairs and two derived_coherence theorems. Correct for unbounded Z-indexed complexes; no derived category of rings is asserted. |
| Every commutative square uses its common composite | Abelian/set square clauses use inverse first-route comparison, transport along `w : b ≫ f = f' ≫ g`, then second-route comparison. module_square identifies its linear lift under forgetful normalization; derived square clauses identify the localization of that same ordinary square. Correct; no cartesianness assumption. The ring comparison is the functorial mapMon lift of the same comparisons. |

Dependency signatures checked: proEtaleDerivedCategory uses the same ProEt.topology
and the Mathlib localization; proEtaleSheafInverseImage uses the same base-change
functor and sheafified Kan extension as upperStar; proEtaleSheafAdjunction uses
that construction's adjunction. ringedSiteModules is transparently SheafOfModules,
with sectionwise linear morphisms. TensorProduct imports the established sheafified
presheaf tensor and defines scalar extension; the published internal Mod framework
uses that sheaf tensor, rather than a private replacement category. Mathlib
presheafToSheaf/sheafificationAdjunction and DerivedCategory/HasDerivedCategory
have the required universal properties. The size dependency is a convention,
rendered by the explicit universes, not a missing mathematical object.

I also opened Basic.lean's actual pointUpperStar, upperStarFromPointComp,
coefficientPullbackIso and condensedPullbackHom, and UpperLowerStar/Defs.lean's
module pullback, direct image and composition adjunction conjugate. The derived
helpers in ExactFunctor.lean explicitly descend levelwise natural isomorphisms
and characterize them through mapDerivedCategoryFactors. Thus the derived
clauses refer to the termwise lifts required by proof step 7. The framework's
left-derived upperStarComp is a different construction from this exact-functor
termwise comparison; it is not substituted silently.

Edge cases: empty S gives LC(empty,Z) the zero ring and empty spectrum; neither
the site clauses nor the Kan-extension quantifiers exclude it. Empty schemes
and arbitrary non-quasi-compact schemes remain allowed. Identity arrows are
explicitly tested in the unit equations. Squares may be noncartesian and contain
identities. Zero coefficients/modules and unbounded complexes are included.
There is no n, characteristic, field, completeness, flatness or nonzero hypothesis.
No independent smaller test universe or equality of site universes was added.

Independent searches: LeanFinder, “Coherence of pullback functors on sheaves of
modules over condensed rings and their derived categories”, returned generic
SheafOfModules.pullbackComp, pullback_assoc and unit results, not this point
construction and full family. Loogle `"mapDerivedCategoryNatIso"` returned no
Mathlib match. LeanSearch for geometric morphism from condensed sets to pro-etale
sheaves was unavailable (Internal Server Error), not negative evidence. Direct rg
searches for profinitePoint, pointUpperStar, upperStarFromPointComp,
extendScalarsIsoComapInv, upperStarId and upperStarComp in Mathlib, the older
source tree, the project and the exact framework identified the reused framework
constructions and generic/abelian coherences, but no declaration of the entire
node. These existing parts are used by name, not redefined. No absent independent
notion, duplicate category, new definition node or dependency repair is needed.

No mismatch found; Lean and node fields were left unchanged. All 14 theorem
bodies are sorry, and all 14 definitions/abbreviations have actual data. Named
monoidality theorem instances provide the ring-lift prerequisites. Every
statement has a source/blueprint and a natural-language proof for its clauses;
collectively these cover proof steps 1–8. I checked that the primary lean.statement
is verbatim its file signature and the maximum line width is 98. The independent
scompile.py run compiled both the sandbox and actual module name cleanly (5.5 s
and 6.7 s); no errors or warnings were emitted. Only this second-reading report
was added.
