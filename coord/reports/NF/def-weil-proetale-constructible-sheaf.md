## Worker report

Defines `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf` in
`Sheaf.Paper.ProEtaleConstructibleSheaf`, with real Prop-valued data and no new
proofs, proof obligations, or sorry terms. The source read was the blueprint
`sec-smooth-purity/sk-def-sf-operations/def-weil-finite-torsion-constructibility.md`,
second paragraph. This is its global finite-stratification convention, generalized
to the finite commutative coefficient ring explicitly permitted by this node.
The affine-local Stacks convention is not substituted.

Clause-by-clause correspondence:

- An arbitrary scheme is `(Y : Scheme.{u})`. The finite commutative ring is
  `(A : Type u) [CommRing A] [Finite A]`. No prime, field characteristic,
  Noetherian, quasi-compactness, or separation hypothesis is added.
  `A_{E,n}` is an example, not an additional hypothesis or a construction needed
  by this generalized definition.
- The small pro-etale site, constant ring, and module sheaf are expressed by
  `(F : proEtaleRingModules Y (proEtaleConstantRing Y A))`.
  This unfolds to exactly the `SheafOfModules.{u+1}` presentation used by the
  recorded site and local-constancy dependencies. The coefficient ring is
  lifted to `ULift.{u+1,u} A`; site objects have universe `u+1`, arrows `u`.
- `∃ S : LocallyClosedStratification Y, 0 < S.n ∧ ...` gives an integer
  `N ≥ 1`, with index `Fin S.n`, equivalent to the node's indices `1,...,N`.
  The inherited fields `stratum`, `isLocallyClosed_stratum`,
  `isConstructible_stratum`, `iUnion_stratum_eq_univ`, and
  `pairwise_disjoint_stratum` give precisely the locally closed constructible
  disjoint partition. The current published `Topology.Stratification` was
  checked using `scompile.py --source WeilConjectures.Topology.Stratification`:
  it already includes constructibility. There is no redundant constructibility
  conjunct in this definition.
- `S.domain i`, `S.immersion i`, `S.isImmersion i`, and `S.range_immersion i`
  supply the subschemes and immersions realizing exactly those subsets.
- `proEtaleConstantModulePullback (S.immersion i) A F` is the recorded canonical
  restriction construction: inverse image over the inverse-image coefficient
  ring, followed by sheaf tensor extension along
  `proEtaleCoefficientInverseImageMap`. That map is the adjunct of the
  constant-section comparison, not an arbitrary ring map or an existentially
  chosen isomorphism. Thus this uses the coefficient identification specified
  by the node, without requiring a new isomorphism witness from the caller.
- `IsLocallyConstantProEtaleModuleSheaf (S.domain i) A (...)` is exactly the
  recorded dependency's predicate. It quantifies a pro-etale cover and modules
  varying with its members, and module-sheaf isomorphisms to constant sheaves
  on the localized ringed sites.
- For each stratum, `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ S.domain i), Finite (...)` quantifies every geometric
  point within the chosen bound. Its argument is precisely
  `proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) A)` of
  the same restricted sheaf. `Finite` expresses finiteness of its underlying
  set, the node's equivalent formulation of a finite module over finite A.
  No statement about finite generation over a varying stalk ring is substituted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`: read its complete module
  and coefficient presentation; the definition uses its site/coefficient
  presentation through the following modules rather than forming a derived category.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`,
  `AlgebraicGeometry.Scheme.proEtaleRingModules` and the specified
  `proEtaleRingModulePullbackObj`: the latter is the general tensor formula;
  its constant-coefficient specialization is already available below.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `AlgebraicGeometry.Scheme.proEtaleConstantRing` and
  `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback`: the owning node
  `def-weil-proetale-inverse-image` was added to stmt_deps under the permission
  to cite an already landed node. It already has the needed declaration;
  no helper or duplicate definition was introduced. This module is publicly
  imported through ProEtaleOperations.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.LocallyClosedStratification` and the inherited
  `Topology.Stratification`. Its current inherited constructibility requirement
  is required by this item, so its recorded declaration is usable here.
- `Mathlib.Topology.Defs.Basic`, `IsLocallyClosed`, and
  `Mathlib.Topology.Constructible`, `Topology.IsConstructible`: read their
  definitions and use them through the stratification fields.
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`,
  `AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`,
  `AlgebraicGeometry.Scheme.proEtaleGeometricModuleStalk`.
- The recorded `Padic.coefficientExtensionRing` and related declarations in
  `Sheaf.NumberTheory.Padics.CoefficientExtension` were read. No declaration
  from that module is needed: this node only mentions these rings as examples.

Edge cases checked: the empty scheme is not excluded (a single empty stratum
is permitted by the stratification structure); empty parts are allowed, as the
node does not impose nonemptiness of every stratum. The zero ring and zero
module sheaf are allowed. `N = 0` is excluded exactly by the explicit `N ≥ 1`
clause; `N = 1` is allowed. Local trivialization modules may vary and have no
extra finiteness assumption: finiteness is imposed on all geometric stalks.
No affine-local replacement, uniform stalk bound, or finite-type scheme
hypothesis occurs. The universe bound agrees with the recorded stalk definition.

Searches performed before writing:

- `msearch.py ... leanfinder "Constructible sheaf of finite modules on the
  pro-etale site finite stratification locally constant finite geometric stalks"`:
  eight hits, including SheafOfModules.IsFiniteType, local generators,
  condensed modules, and finite presentation; no matching predicate.
- `msearch.py ... loogle '"IsConstructible", "Sheaf"'`: zero hits.
- `msearch.py ... grep 'IsConstructible|constructibleSheaf' AlgebraicGeometry/Sites`:
  zero hits.
- `msearch.py ... leansearch "Constructible sheaf of finite modules on the
  small pro-etale site"`: service unavailable, Internal Server Error.
- `rg` in upstream WeilConjectures and project lean/Sheaf for
  `IsConstructibleProEtaleModuleSheaf` and the item id: no existing declaration.
- Read the side framework's
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def` in full. Its
  `AlgebraicGeometry.ProEtale.IsConstructibleModuleObject` uses internal
  module objects in a general monoidal category and local finite presentations.
  It does not state this node's local-constant/finite-geometric-stalk predicate
  on constant-ring `SheafOfModules`; identifying them would require a comparison
  theorem. The framework therefore supplies no exact reusable declaration here.
- Searched the pro-etale inverse-image modules and upstream constant-sheaf APIs
  for canonical coefficient comparisons; found the existing
  `proEtaleCoefficientInverseImageMap` and `proEtaleConstantModulePullback`.
  These remove the need for any new helper.

Validation: the delivered file compiled cleanly through the prescribed
`scompile.py NF def-weil-proetale-constructible-sheaf` wrapper, both as sandbox
module and as its library module. No errors or warnings. No statement correction,
new node, dependency repair, or disputed statement is required.


## Second reading by NF

Independently read the sandbox node and module, the blueprint source's second
paragraph, Stacks proetale.tex definition-constructible (09AJ) including its
preceding Noetherian-ring convention, and coord/pefw-upstream-framework.md.
The blueprint is the governing global-partition convention. Its initial prime,
finite-field and coefficient-extension datum provides the example coefficient
ring; this split node explicitly generalizes to any finite commutative ring.
Stacks asks instead for decompositions on each affine open. Neither its
Noetherian-ring hypothesis nor an affine-local replacement belongs in this
finite-ring global definition (finite rings are already Noetherian).

Object/hypothesis/conclusion checklist, in node order:

1. Arbitrary scheme Y: `(Y : Scheme.{u})`, with no Noetherian, quasi-compact,
   separated, base-field or characteristic instance. PASS.
2. Finite commutative coefficient ring Lambda: `(A : Type u) [CommRing A]
   [Finite A]`. `A_{E,n}` is only an example. Opened the recorded
   `Padic.coefficientExtensionRing` signature: a quotient of the extension's
   integers by the nth uniformizer ideal, not needed to define the general A.
   PASS.
3. Small pro-etale site, constant ring and module sheaf F:
   `(F : proEtaleRingModules Y (proEtaleConstantRing Y A))`. Opened
   ProEtaleDerivedCategory, ProEtaleOperations and ProEtaleInverseImage:
   the first fixes the same `SheafOfModules.{u+1}` presentation; the second's
   `proEtaleRingModules` is exactly `ringedSiteModules` over the underlying
   ring sheaf; the third constructs the constant commutative ring sheaf from
   `ULift.{u+1,u} A`. No derived object is substituted for F. PASS.
4. Existential integer N >= 1 and finite disjoint partition:
   `exists S : LocallyClosedStratification Y, 0 < S.n` and indices `Fin S.n`.
   The inherited `iUnion_stratum_eq_univ` and `pairwise_disjoint_stratum`
   give coverage and pairwise disjointness. PASS.
5. Locally closed AND constructible parts: inherited
   `isLocallyClosed_stratum` and `isConstructible_stratum`. Opened Mathlib
   `IsLocallyClosed` (open intersect closed) and `Topology.IsConstructible`
   (Boolean algebra generated by retrocompact opens). Read the current
   `WeilConjectures.Topology.Stratification` through `scompile.py --source`:
   it includes constructibility. The dependency module's old prose and DAG
   note saying that no constructibility is imposed are stale; the actual
   inherited signature supplies precisely the extra condition this item
   explicitly requires. No missing conjunct and no additional condition on
   this item's partitions results. PASS; no dependency repair needed here.
6. Scheme structures and realizing immersions: opened the recorded
   `LocallyClosedStratification` structure; its `domain`, `immersion`,
   `isImmersion`, and `range_immersion` give exactly these objects and image
   equalities, without requiring reduced structures or nonempty parts. PASS.
7. Restriction through the canonical constant-ring identification:
   `proEtaleConstantModulePullback (S.immersion i) A F`. Read its body,
   `proEtaleModuleInverseImage`, and the coefficient comparison definitions:
   inverse image is transported through the equivalent small site; the
   coefficient map is the adjunct of the sheafified constant-section map;
   the module pullback is sheaf tensor extension along that specific map.
   It matches the general `proEtaleRingModulePullbackObj` tensor formula,
   specialized to the canonical constant coefficients. No arbitrary map,
   choice of left adjoint, or caller-supplied identification occurs. PASS.
8. Every stratum's restriction is locally constant: the first conjunct is
   `IsLocallyConstantProEtaleModuleSheaf (S.domain i) A` of that restriction.
   Opened its declaration and the constant module constructions: it
   existentially quantifies a covering family of the final pro-etale object,
   then a module M and a module-sheaf isomorphism on each localized ringed
   site. M varies with the cover index. PASS.
9. Every geometric stalk of the SAME restriction is finite: the second
   conjunct universally quantifies `(Omega : Type u) [Field Omega]
   [IsAlgClosed Omega] (y : Spec (.of Omega) --> S.domain i)` and applies
   `Finite` to `proEtaleGeometricModuleStalk` with the constant ring on that
   stratum. Opened the entire stalk module: its module is the colimit of
   pointed weakly etale neighbourhood sections with the induced stalk-ring
   action. Finiteness of the underlying set is exactly the node's equivalent
   finite-module condition over finite A. PASS.
10. Quantifier order: a single stratification exists before the universal
    stratum and geometric-point quantifiers; local constancy and stalk
    finiteness concern the same canonical restriction. No uniform rank or
    global trivialization module is required. PASS.

Edge cases: positive stratum count explicitly excludes N=0, as the node does;
for the empty scheme N=1 with an empty part is allowed. Individual empty parts
are allowed. Zero ring and zero module sheaf are not excluded. No prime,
characteristic, or positive exponent binder is relevant to the general finite
ring predicate. All universes and variables are bound. Scheme and bounded
geometric-field universe u, site object universe u+1, site Hom universe u,
and module/constant-trivialization universe u+1 agree with the recorded site,
local-constancy and stalk dependencies. The finite coefficient ring can be
represented in this bound, and no equality between the site object and Hom
universes is imposed.

Independent H4 searches (different queries from the first reader):

- LeanFinder via msearch: `Sheaf locally constant finite fibers on a
  decomposition by locally closed subschemes`. Eight hits about locally
  constant profinite functions and related constructions; no matching notion.
- Loogle via msearch: `"constructible"`. Twelve hits, all topological subset
  notions and their elementary properties, not constructible module sheaves.
- LeanSearch via msearch: `Finite module sheaf trivialized by covers on
  finitely many scheme strata`. Service returned Internal Server Error;
  recorded as unavailable, not a negative mathematical search result.
- Independent rg by `constructible.*sheaf`, `sheaf.*constructible`, and
  finite/local-constant variants in upstream ConstructibleSheaf, Mathlib
  AlgebraicGeometry/Sites, and project Sheaf/Paper and AlgebraicGeometry;
  narrowed to declaration signatures and opened upstream
  ConstructibleSheaf/Defs.lean. `Scheme.IsConstructibleSheaf` and
  `IsFiniteLocallyConstantSheaf` there take sheaves on `smallEtaleTopology`,
  so cannot replace this pro-etale constant-ring module predicate.
- Opened the exact side-framework
  WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean.
  `ProEtale.IsConstructibleModuleObject` uses internal Mod objects and local
  finite presentations over inverse-image ring objects in an arbitrary
  monoidal value category. It does not supply this constant-ring
  SheafOfModules predicate with local constant module sheaves and finite
  geometric stalks; no existing comparison identifies the interfaces.

No new nodes, dependency modules, or statement_change were supplied by the
first reader; thus no new-node source audit or corrected-statement citer audit
is applicable. The added stmt_deps entry def-weil-proetale-inverse-image owns
the canonical restriction already used by the module.

H5/H6/H8/H9: the module has one real Prop-valued definition, no theorem,
no sorry, no private copies or local instances/notation. Its source and
blueprint docstrings are present; this definition node has no proof steps.
The stored lean.statement equals the declaration's signature (starting at
def and ending before :=); all lines obey the 100-character bound.

Changes: appended this independent second reading only. The Lean and node
were already correct and are preserved. Validation is recorded below after
the required compilation and delivery dry run.

Second-reader validation: scompile.py compiled the sandbox module and its
library module cleanly (1.6 seconds each); no errors or warnings. Checked
lean.statement verbatim against the signature and checked the line bound.
