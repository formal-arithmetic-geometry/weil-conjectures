## Worker report

The delivery states Stacks Modules on Sites, Tag 093T (1), with the canonical-map
characterization, naturality in both modules, and the same constant-map rule on
localized sites from Tag 0E8H. I read sites-modules.tex, lemma-locally-constant,
including the finite-presentation argument and its canonical comparison. There
is one theorem, `CategoryTheory.siteConstantModule_hom`, with proof `sorry`.
The three helper definitions construct canonical coefficient transport and its
constant-section unit using existing Mathlib and dependency constructions. No
other DAG node is stated, no dependency record changes, and no statement correction
or disputed statement is needed.

Hypotheses and clauses:

- A small site is `{C : Type u} [Category.{v} C]` with
  `J : GrothendieckTopology C`. Object and morphism universes remain independent.
  This is the topology presentation of the site in
  `CategoryTheory.Precoverage.IsSiteForCoverings`; no global pullback, points,
  nonemptiness, or covering-finiteness hypothesis is imposed.
- The commutative coefficient ring is `(Λ : Type (max u v)) [CommRing Λ]`.
  Modules are `(P Q : ModuleCat.{max u v} Λ)`. This common ambient universe
  permits every set-sized site and coefficient/module data by enlargement; it
  does not identify the site's object and arrow universes.
- Finite presentation of the source is `[Module.FinitePresentation Λ P]`,
  Mathlib's finite presentation by finite generators and relations. There is
  no finiteness assumption on Q or Λ. In particular there is no finite-ring,
  finite-target, or points hypothesis.
- Constants are the recorded `siteConstantModuleFunctorGeneral J Λ`. Its output
  is over the RingCat constant ring. The recorded `SheafOfModules.homObj` expects
  the underlying RingCat sheaf of a CommRingCat sheaf. `constantModuleHomRingIso`
  is the canonical `sheafComposeNatIso` for forgetting commutativity, applied to
  the constant commutative-ring presheaf. `constantModuleHomFunctor` is exactly
  the recorded functor followed by `SheafOfModules.pushforward` along the inverse
  of this coefficient isomorphism, with identity site functor. Thus the constant
  sheaves are only transported along the canonical identification of the same
  coefficient ring. `constantModuleHomUnit` retains their underlying additive
  sheafification unit. These definitions have actual data and no postponed proof.
- The source of `comparison M N` is the constant module sheaf of
  `ModuleCat.of Λ (M →ₗ[Λ] N)`; the target is the dependency's actual
  `SheafOfModules.homObj` of the two constant modules. Being a morphism in
  `SheafOfModules` includes linearity over the entire constant ring sheaf.
- The first conjunct says on every object U and every constant linear map f,
  evaluation of comparison on the unit section is exactly
  `PresheafOfModules.restrictOver ... U.unop |>.map` applied to the induced
  constant sheaf morphism. Thus the existential family is the canonical
  comparison, determined by the sheafification unit; it is not an arbitrary
  isomorphism or a chosen uncharacterized map. The construction of the canonical
  map itself makes sense for all source modules, so the family includes those
  maps without asserting they are all isomorphisms.
- `IsIso (comparison P Q)` is precisely the claimed isomorphism for the given
  finitely presented P and arbitrary Q.
- The next conjunct is the two-variable naturality square for arbitrary maps
  `a : M' ⟶ M` and `b : N ⟶ N'`. The source linear map, built with
  `LinearMap.lcomp` and `LinearMap.llcomp`, sends f to `b.hom.comp (f.comp a.hom)`.
  The target map is the recorded `SheafOfModules.homObjMap` of the two constant
  module maps. No finite-presentation assumption is needed for this square;
  the isomorphism assertion is still exactly the one for P,Q.
- The last conjunct quantifies over every U, every `V : Over U`, and f. It
  restricts comparison by `SheafOfModules.Hom.over`, evaluates its resulting
  internal-Hom section at the identity object over V.left, and identifies that
  map with the V-component of the restriction of the constant sheaf map of f.
  Thus on C/U the map uses the very same constant linear map f, including on
  further objects V/U. The general first characterization applies to the slice
  site too; together with the canonical unit-preserving constant-restriction
  comparison, this is compatibility with the slice comparison. It does not
  claim a pullback formula for an arbitrary morphism of topoi.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the current presieve site
  convention; the theorem uses its associated Grothendieck-topology encoding.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`,
  `CategoryTheory.siteConstantModulePresheafGeneral` and
  `CategoryTheory.siteConstantModuleFunctorGeneral`: genuine constant
  presheaf construction followed by module sheafification, with independent
  site universes. I read the full module and its docstrings.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `SheafOfModules.homObjMap`, and
  `PresheafOfModules.restrictOver` from its presheaf dependency. I read their
  full signatures, definitions, and docstrings: sections are morphisms of
  restricted module presheaves, and the target's sheaf structure is inherited
  from the internal-Hom sheaf theorem.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.over`, `SheafOfModules.Hom.over`, `overMap`, and
  `overFunctorMap`, the recorded Mathlib match of
  def-pur-localized-ringed-site. I read the definitions and docstrings; restriction
  has exactly the original section and morphism components on the slice.

Proof-plan imports include the current recorded modules of the local Hom
sheaf, constant Hom local injectivity and surjectivity, constant module unit,
and local sheafification sections. Missing local copies were read with the
prescribed `scompile.py --source` command. The Mathlib proof leaves are imported
through `PreservesSheafification`, `CoverLifting`, and `LocallyBijective`, and
module sheafification supplies the universal-property declaration.

Edge cases checked mathematically: P=0 (including zero generators/relations),
Q=0, Λ the zero ring, P=Λ, the empty category, an object covered by the empty
sieve, and a site without enough points. All statements remain meaningful and
have the expected zero/unique morphisms. No Nonempty, Nontrivial, positive-rank,
finite-target, finite-ring, or enough-points assumption occurs. Naturality allows
zero maps and identities. Slice restriction includes U arbitrary, V=U with the
identity arrow, and nonidentity arrows V→U.

Searches actually run:

- `msearch.py leanfinder`, “The internal Hom between constant sheaves of modules
  with finitely presented source is the constant sheaf of linear maps”: eight
  hits, including condensed monoidal-closed structures, light-condensed Hom
  points, free-sheaf Hom equivalences, and presentation transport. None states
  this arbitrary-site canonical constant-module comparison.
- `msearch.py loogle`, `CategoryTheory.constantSheaf, ModuleCat`: four hits,
  all full/faithful constant-sheaf results on condensed or light-condensed sites.
  They do not give this arbitrary-site internal Hom statement.
- `msearch.py grep`, `constantSheaf.*[Hh]om|[Hh]om.*constantSheaf|constant.*[Ii]hom|[Ii]hom.*constant`:
  six hits in GlobalSections and SheafCohomology.Basic, concerning external Hom
  and adjunctions rather than the internal Hom comparison.
- `msearch.py leansearch`, “Internal Hom of constant module sheaves with finitely
  presented domain is the constant sheaf of module homomorphisms”: eight hits,
  including sheafHom, constantSheaf, global-section Hom equivalences, and the
  definition of module-sheaf morphisms. None is the requested theorem.
- `rg` in the upstream WeilConjectures source for constant-module/internal-Hom
  combinations, and `grep -rn` for this blueprint id: no exact statement.
  The ordinary internal Hom and its specialized restriction isomorphism exist
  and were read; the latter imposes equal site universes and is not used to
  impose a size restriction on this item.
- `rg -L` in the project's Sheaf source: the constant-module functors and the
  sibling SiteConstantModuleIsomSheaf were found and read. The sibling is
  093T (2), about isomorphism sheaves and requiring both modules finitely
  presented; it is not this node. `rg` for all four proposed full declaration
  names in Mathlib, upstream, Sheaf, and dag/lean_names_upstream.json found no
  existing declaration with those names.

Validation: `scompile.py NS lem-pur-site-constant-module-hom` compiled the module
cleanly in the sandbox (4.8 s) and as a library module (5.1 s), with no errors or
non-sorry warnings. The final delivery check is the prescribed
`deliver2.py NS lem-pur-site-constant-module-hom --no-push`; nothing is pushed.
No second-reading section has been written by this worker.


## Second reading by NS

I independently opened the node, its sandbox Lean module, the four statement
dependency records and their source declarations, Stacks sites-modules.tex
lemma-locally-constant (Tag 093T), its surrounding conventions and proof, and
lemma-internal-hom-restriction (Tag 0E8H). The node is unchanged, has no
statement_change, and introduces no new nodes or dependency modules. There is
no maintenance repair note for this item.

The object/hypothesis/conclusion checklist, matched in order:

1. Small site C: `{C : Type u} [Category.{v} C]` and
   `(J : GrothendieckTopology C)`. Verdict: the associated sieve-topology
   presentation covers every site of def-weil-pbc-sites-and-cohomology.
   I opened SiteCoveringAxioms: its IsSiteForCoverings describes covering
   presieves, with Sheaf on the associated Grothendieck topology. The theorem
   imposes no extra covering, pullback, final-object or points hypothesis.
2. Commutative coefficient ring Lambda: `(Λ : Type (max u v)) [CommRing Λ]`.
   Verdict: exactly the node's commutative ring. The source allows even
   noncommutative rings, but this node explicitly specializes to commutative
   rings, as required for its module-valued internal Hom.
3. Arbitrary modules P,Q: `(P Q : ModuleCat.{max u v} Λ)`.
   Verdict: the actual coefficient modules, with no finiteness assumption on Q.
4. P finitely presented: `[Module.FinitePresentation Λ P]`.
   Verdict: exactly the finite generators-and-relations condition. I opened
   Mathlib Algebra/Module/FinitePresentation.lean: the class uses a finite
   generating set and a finitely generated relation kernel, and exists_fin'
   gives precisely a surjective finite-free presentation with exact relation
   map. This includes zero generators and zero relations.
5. Constant module and ring sheaves: `constantModuleHomFunctor J Λ` is the
   recorded `siteConstantModuleFunctorGeneral J Λ` followed by pushforward
   along `(constantModuleHomRingIso J Λ).inv` with identity site functor.
   Verdict: the same module sheaf, canonically expressed over the underlying
   RingCat sheaf of the constant CommRingCat sheaf. I read the full generalized
   functor and PresheafOfModules sheafification construction, and the pushforward
   definition: transport changes scalar restriction only, preserving the
   underlying additive presheaf and constant unit. RingIso is the existing
   sheafComposeNatIso applied to the constant commutative-ring presheaf;
   sheafComposeIso_hom_fac and its inverse preserve the sheafification unit.
   All three helper definitions have real data and are canonical specializations,
   not private replacements for dependency notions or choices of arbitrary maps.
6. Ordinary sheaf Hom: `SheafOfModules.homObj` with the constant CommRingCat
   sheaf as R. Verdict: exactly def-pur-sheaf-hom. I opened both upstream
   Sheaf/InternalHom.lean and Presheaf/InternalHom.lean: its sections are
   module morphisms after restrictOver, its scalars act sectionwise, and its
   sheaf proof is supplied by isSheaf_homObj. The independent site universes
   are supported by this signature; no specialized restriction API is assumed.
7. Canonical Lambda-linear comparison: the existential family `comparison M N`
   has source `constantModuleHomFunctor.obj (ModuleCat.of Λ (M →ₗ[Λ] N))`
   and target the actual homObj of the constant M,N. Its first conjunct says
   at every U and f that the unit section maps to restrictOver applied to
   the constant sheaf morphism of f. Verdict: this characterizes the canonical
   comparison on all constant representatives. It is a morphism of module
   sheaves, so linearity is over all sections of the constant ring sheaf.
   An arbitrary isomorphism cannot meet this clause unless it is the canonical
   one: sheafification uniqueness determines the map from the unit.
8. The canonical map is an isomorphism for P,Q: `IsIso (comparison P Q)`.
   Verdict: exactly the node's main conclusion; no finite presentation of N
   or Q, finite coefficient ring, or enough-points instance is introduced.
9. Naturality in both modules: for `a : M' ⟶ M`, `b : N ⟶ N'`, the third
   conjunct identifies the composite through the induced constant linear map
   f |-> b.comp (f.comp a) with the composite through homObjMap.
   Verdict: the variance and composition order are correct, as checked against
   LinearMap.lcomp, LinearMap.llcomp and the upstream homObjMap signature.
   Canonical comparisons exist for every M,N; only the P,Q comparison is
   asserted invertible, under the given finite presentation hypothesis.
10. Same constant map on every localized site: the final conjunct quantifies
    over each U, each `V : Over U` and each `f : P →ₗ[Λ] Q`. It evaluates
    `comparison.over U` on the unit at V.left and then evaluates its resulting
    local morphism at the identity object over V.left. The result is exactly
    the V-component of the same constant sheaf map restricted by Hom.over U.
    Verdict: the same f is used on each slice and each further object of it.
    The first conjunct already specifies the whole restricted morphism, not
    only its identity component. Together these express the defining 0E8H
    localization rule. I read Mathlib overFunctor, over, Hom.over, overMap and
    overFunctorMap: their components are exactly the original components on
    the corresponding underlying objects. CoverLifting's constant-restriction
    comparison preserves the unit and is natural in f, identifying this rule
    with the comparison constructed on C/U itself.

Edge cases: P=0, Q=0, the zero coefficient ring, P=Lambda, presentations with
zero generators or relations, the empty site, empty covering sieves, and sites
without enough points are all included. ModuleCat and CommRing impose no
Nontrivial or Nonempty conditions. On an empty covering sieve the sheaf has
unique sections, so the stated rules remain valid. Localization allows every
U and every V/U, including identities and nonidentity arrows; when there are
no objects its universal clauses are vacuous. There is no characteristic or
positive-rank assumption and no scheme hypothesis. The independent object and
arrow universes u,v are retained. Coefficients, modules and internal Hom live
in the common ambient universe max u v; enlarging the object universe covers
arbitrary set-sized coefficients and modules, without identifying the site's
arrow universe with its object universe.

Independent duplicate searches, actually run during this second reading:

- msearch leanfinder: "Sheafification of the constant presheaf of linear maps
  agrees with the sheaf of local module morphisms when the source module has
  finite presentation". Eight results: module sheafification Hom adjunctions,
  finite-presentation predicates and presentation maps; none is this theorem.
  I opened Sheafify.lean at sheafifyHomEquiv and sheafifyHomEquiv': these are
  external Hom universal properties with an arbitrary sheaf target, not this
  internal-Hom identification for constant modules.
- msearch leansearch: "For a finitely presented module M, internal morphisms
  between its constant sheaf and any constant module sheaf form the constant
  sheaf of linear maps". Eight results: global-sections adjunction, condensed
  full constant functors, module Hom, free-module external Hom and finiteness
  results. None has the arbitrary-site conclusion here.
- msearch loogle: `SheafOfModules.homObj` returned unknown identifier (the
  declaration is upstream, not a Mathlib declaration). A second query,
  `CategoryTheory.constantSheaf, _ ≅ _`, returned five results including
  constantCommuteCompose and dense-site constant comparisons. These identify
  constants with change-of-values functors; they do not state this Hom theorem.
  The specialized ring comparison here uses the same existing canonical
  sheafComposeNatIso construction, rather than reimplementing it.
- msearch grep: `constant.*(homObj|sheafHom)|((homObj|sheafHom).*constant)`
  returned zero hits. Independently, rg with case-insensitive constant versus
  internalHom/homObj/sheafHom combinations across Mathlib, upstream
  WeilConjectures and project lean/Sheaf found specialized adic pullback,
  derived twists and finite-local-system comments, but no general theorem.
  A separate search for siteConstantModule_hom and the three helper full names
  in dag/lean_names_upstream.json and the upstream/project source found none.
  I opened SiteConstantModuleIsomSheaf: it is 093T(2), with both modules
  finitely presented and isomorphism-valued sections, so it is not this item.

No mathematical or signature mismatch was found, and no Lean declaration or
node field was rewritten. The module docstring and all declaration docstrings
carry the source and blueprint id. The theorem docstring gives all five proof
steps, including local injectivity/surjectivity, additive sheafification, scalar
linearity, naturality and slice compatibility, with the node ids. Proof-plan
imports cover the recorded proof dependencies (including their Mathlib matches).
There are no local/private definitions, local instances or local notation, no
hollow data, and the only postponed theorem is this node's theorem with proof
`sorry`. All variables and universes are bound. I mechanically checked the
100-column limit and exact verbatim equality of lean.statement with the file's
signature. Changes in this reading are this report and the independent search
log only. The module is recompiled with scompile.py before the required dry run
and delivery.
