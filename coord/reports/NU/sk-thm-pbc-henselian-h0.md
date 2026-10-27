## Worker report

Item: sk-thm-pbc-henselian-h0. The module `Sheaf.Paper.HenselianPairH0` states
`AlgebraicGeometry.henselian_pair_h0`, with one postponed proof, `by sorry`.
It also supplies two concrete helpers belonging to the comparison stated by this
node. `henselianPairClosedFibreι` is the first projection from the chosen scheme
pullback along the quotient-spectrum map. `henselianPairH0SetRestriction` is the
set-valued inverse-image adjunction unit at the identity etale object, followed by
restriction along the inverse of the canonical second-projection isomorphism.
Neither helper chooses a map or a comparison from a mere existence assertion, and
neither contains postponed data or a postponed proof.

The source read is the current blueprint main-20261015 unit
`sec-proper-base-change/sk-thm-pbc-henselian-h0/_section.md` and Stacks Project
`etale-cohomology.tex`, Tag 0A0C, `lemma-h0-proper-over-henselian-pair`, lines
18199--18214. Its immediately preceding Tag 0A0B and its cited Tag 09ZF explain
the proof. The live node has Q57's reviewed six-step stage-1 split. That split,
the source, and the mathematical statement are retained.

Hypothesis and clause correspondence:

- The commutative ring A is `(A : Type u) [CommRing A]`; the ideal J is
  `(J : Ideal A)`. The henselian-pair hypothesis is `[HenselianRing A J]`, the
  recorded Mathlib notion from def-weil-pbc-henselian-terminology. It includes
  `J ≤ Ideal.jacobson ⊥`, and is equivalent to the finite-algebra idempotent
  formulation. No local, Noetherian, nonzero, or residue-field hypothesis occurs.
- The scheme Z and its proper morphism to Spec A are `(Z : Scheme.{u})`,
  `(f : Z ⟶ Spec (.of A))`, and `[IsProper f]`. This is precisely the properness
  convention of sk-def-conv and def-weil-proper-morphism: separated, universally
  closed and locally of finite type, with quasi-compactness following from
  universal closedness. It imposes no additional finiteness condition on A.
- The quotient spectrum is `Spec (.of (A ⧸ J))`. Its map to Spec A is
  `Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op`.
  The closed fibre is the actual Mathlib `pullback f` of this map; i is exactly
  its first projection, named `henselianPairClosedFibreι A J f`.
- Every sheaf of sets is quantified as
  `∀ F : Sheaf Z.smallEtaleTopology (Type (u + 1))`. No constructibility,
  torsion, local constancy, or finiteness restriction is present. This is the
  coefficient universe of the existing small etale inverse-image framework.
- Gamma(Z,F) is `F.obj.obj (op (Scheme.Etale.mk (𝟙 Z)))`.
  Gamma(Z0,i inverse F) is the value of
  `(Scheme.etaleSetPullback (henselianPairClosedFibreι A J f)).obj F` at the
  identity object of the displayed scheme pullback. Both ends of the comparison
  are thus actual global sections at identity objects, not unnamed isomorphic sets.
- Restriction is `henselianPairH0SetRestriction A J f F`. Its data first use
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` and its unit,
  evaluated at the identity over Z. Base change gives the etale object
  `Z ×_Z Z0 → Z0`. The second projection is an isomorphism because the first
  defining arrow is an identity. `MorphismProperty.Over.isoMk` lifts that
  isomorphism to the etale category, and the contravariant sheaf maps its inverse
  to identify the target with the identity object over Z0. This is the canonical
  restriction in 0A0C, rather than an arbitrary function or an arbitrary bijection.
- Bijectivity is the first conjunct `∀ F, Function.Bijective (...)`.
- Naturality in F is the second conjunct. For every `α : F ⟶ G`, its equality
  says `α_Z ≫ r_G = r_F ≫ (i inverse α)_Z0`. Since r_F is bijective for every F,
  its inverse is automatically natural as well. No naturality condition is assumed.
- The abelian-sheaf consequence is the third conjunct, for every
  `G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}`: the existing canonical
  `Etale.globalSectionsUpperStarMap AddCommGrpCat ... i G` is an `IsIso`.
  This states the group isomorphism, not just an unrelated equivalence of sets.
- The module consequence is the fourth conjunct, for every
  `(R : Type (u + 1)) [CommRing R]` and every
  `M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)`: the same existing
  canonical map with coefficient category `ModuleCat R` is an `IsIso`.
  Thus restriction is an R-linear isomorphism, with no torsion or invertibility
  hypothesis. The structured comparisons use the unit of the
  respective adjunction; algebraic-structure compatibility and modules-exact
  identify its underlying map with the set-valued unit. Naturality of these
  canonical maps and of their inverses follows from the set-valued naturality
  after forgetting structure, since the forgetful functors are faithful.

Recorded dependency declarations read and used:

- sk-def-conv: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (class signature and docstring at lines 41--42).
- sk-def-pbc-conventions: `Sheaf.SixFunctors.ClassicalDefinition`,
  `AlgebraicGeometry.ProEtale.IsClassicalModuleComplex`. This is a convention
  bundle, not an extra hypothesis: no pro-etale or derived object occurs in this
  degree-zero calculation. Its prescribed module is publicly imported.
- def-weil-pbc-henselian-terminology:
  `WeilConjectures.Mathlib.RingTheory.Henselian`,
  `HenselianRing`, `HenselianLocalRing`, `IsStrictlyHenselianLocalRing`.
  The actual pair class is Mathlib/RingTheory/Henselian.lean:94--99; the strict
  local class and its equivalence were read at the recorded upstream lines
  121--137. Only `HenselianRing` is used by this statement.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd` (lines 95, 111, 115).
  These are used directly, not replaced by a new fibre-product definition.
- def-weil-pbc-etale-sheaf-of-sets:
  `Mathlib.CategoryTheory.Sites.Sheaf`, `CategoryTheory.Sheaf`, the full
  subcategory of presheaves satisfying `Presheaf.IsSheaf` (lines 300--302).
- lem-weil-pbc-sets-etale-inverse-image-exact:
  `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact`,
  `AlgebraicGeometry.etaleSetInverseImage_exact`. Its full signature and proof
  docstring were read; its left-adjoint functor is precisely the existing
  `Scheme.etaleSetPullback` from `WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
  That owning module is publicly imported as required by module visibility.
- def-weil-pbc-finite-section-pullback:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`,
  `AlgebraicGeometry.Etale.globalSectionsUpperStarMap` (definition at lines
  57--65, and its full surrounding docstring). Despite the historical DAG name,
  its signature and construction apply to every scheme morphism and to every
  Grothendieck abelian coefficient category of the prescribed size; no finiteness
  hypothesis is imposed on i. Its complete definition was read before use.
Only def-weil-pbc-finite-section-pullback is added to stmt_deps, to record
the canonical structured section map used directly in the signature.
No new node or dependency repair is needed. No other node field changes, apart
from the new lean record. The recorded proof-dependency modules are imported
privately: ZariskiH0ProperHenselianPair, GabberH0EtaleCriterion,
EtaleSetInverseImageCompositionUnits, EtaleInverseImageAlgebraicStructures,
EtaleInverseImageModulesExact, and the Mathlib closed-immersion, finite, and
quasi-separated morphism modules. Their proof interfaces are left unchanged.
The six steps are reproduced in the theorem's docstring.

Edge cases checked before writing:

- J = 0: the quotient map is an isomorphism and restriction is an isomorphism
  for every sheaf. The chosen fibre may not be definitionally Z, so the statement
  uses the canonical unit and terminal transport, not a false definitional equality.
- A = 0 (and hence J = A): both schemes over Spec A are empty, and the empty
  covering forces set-valued global sections to be singletons. This case is included.
- J = A with A nonzero is excluded by the henselian pair's Jacobson condition;
  no additional proper-ideal or Nontrivial assumption is inserted.
- Empty Z over any allowed A: again both global-section sets are singletons.
- Infinite and nonconstructible sheaves are included; no finite stalk condition
  is used anywhere in the signature. The zero abelian sheaf and zero coefficient
  ring are included by the last two conjuncts.
- Properness matters: the nonproper open Spec(k((t))) in Spec(k[[t]]) has empty
  closed fibre, while a constant two-element sheaf on it has two global sections.
  A henselian pair without properness would therefore not suffice.

Searches actually run on this retry:

- msearch.py LeanFinder:
  `proper scheme over a henselian pair restriction of global sections of any sheaf of sets on the small etale site to the closed fibre is bijective`.
  Eight results, including StandardEtalePresentation.lift_bijective, Scheme.Etale,
  and Scheme.Etale.forgetFullyFaithful; none states this comparison.
- msearch.py Loogle: `HenselianRing, CategoryTheory.Sheaf`: zero hits.
- msearch.py grep of Mathlib:
  `henselian.*(section|sheaf)|((section|sheaf).*henselian)`: zero hits.
- msearch.py LeanSearch:
  `proper scheme over henselian pair etale sheaf global sections closed fibre bijective`.
  Eight results concerning GammaSpecIso, germs, etale objects, and proper
  structure-sheaf global sections; none concerns arbitrary etale sheaves of sets.
- rg of lean/WeilConjectures and lean/Sheaf with the same henselian/sheaf/section
  pattern found the existing abelian comparison and the existing Zariski
  comparison, but no exact set-valued theorem. In particular
  `AlgebraicGeometry.Etale.bijective_pullSection_of_henselianRing` in
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.HenselianPairSections`
  was read at lines 673--684: it is explicitly for abelian sheaves, so is not an
  existing match for this node. Gabber's criterion has extra Zariski invariance
  hypotheses and is likewise not the item itself.
- rg for `sk-thm-pbc-henselian-h0` in lean/WeilConjectures: no hits; in lean/Sheaf
  only the proof citation in ProperWContractibleClosedFibreRigidity was found.
- rg for all three proposed full-name suffixes in lean/WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no hits. Searches for section and
  restriction definitions identified and reused the existing structured map;
  the newly supplied set-valued helper includes the literal terminal transport
  needed for this comparison and contains no new inverse-image construction.

No statement correction, source dispute, new definition node, or dependency
module is delivered. The previous reported unchanged-node refusal is addressed
by supplying the missing stage-2 module and actual lean-field delta, rather
than changing the already reviewed stage-1 split.

Validation: scompile.py compiles each delivered file against the live published
library; the delivery dry run repeats compilation and server preflight. The first
probe exposed a missing public import and a field-notation syntax error; the next
probe compiled and exposed an overlong line. Both were repaired in the sandbox.
The final scompile.py run is clean in both sandbox and library module modes,
with no errors or warnings.

## Repair of return L, H2

The returned immutable head was bc6eaab6e482. The retained packet initially
passed the prescribed dry run as f0047eae662; that mechanical pass did not
resolve the independent review's unused-dependency finding. Removed
lem-weil-pbc-etale-constant-ring-module-equivalence from stmt_deps and removed
the public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence.
The signature uses none of that module's declarations. The module clause
continues to use Sheaf … (ModuleCat R) and the existing canonical
Etale.globalSectionsUpperStarMap. Kept def-weil-pbc-finite-section-pullback and
its public import, since that definition occurs in both structured clauses.
The mathematical statement, its six-step proof plan, helper definitions,
and theorem signature are unchanged. All node fields other than lean and this
retained canonical-map dependency agree with current main.

## Second reading by NU

Repair self-check against the open node and module, following the maintainer's
independent reading recorded in the return: HenselianRing A J renders the pair,
IsProper f renders properness, and pullback.fst along Spec(A → A/J) renders i.
The first conjunct quantifies over every Type (u+1)-valued small-etale sheaf and
asserts bijectivity of the actual unit followed by terminal-object transport.
The second conjunct is its naturality equality for every sheaf morphism. The
last two conjuncts assert IsIso for the canonical section map in AddCommGrpCat
and ModuleCat R respectively, with the same closed-fibre inclusion. No extra
finiteness, torsion, locality, or nonzero hypothesis occurs. The definitions
have real data; the only sorry is the named theorem. The saved signature in
lean.statement is unchanged and matches the file verbatim. The only defect
identified by the independent review was the unused constant-ring equivalence
dependency and import; both are now removed. No advisory refactor is needed.
