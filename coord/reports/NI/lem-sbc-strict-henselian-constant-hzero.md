## Worker report

The module `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantHZero` states
`AlgebraicGeometry.Etale.nonempty_constantSheaf_cohomology_zero_iso`, with `sorry`
as its entire proof. It asserts existence of a natural isomorphism from degree-zero
derived cohomology of constant étale sheaves to the identity coefficient functor.
No definitions, extra nodes, dependency replacements or statement corrections were needed.

Hypothesis and clause correspondence:

- The strictly henselian local ring is `(R : Type u) [CommRing R]
  [IsStrictlyHenselianLocalRing R]`. The recorded upstream class extends
  `HenselianLocalRing`, which includes the local-ring hypothesis, and requires
  separably closed residue field. It does not include the zero ring.
- `X = Spec R` is written explicitly throughout as `Spec (CommRingCat.of R)`;
  no extra scheme, morphism, or identification is assumed.
- The arbitrary abelian group `A` ranges over all objects of
  `AddCommGrpCat.{u + 1}`, the domain of the displayed composite functor.
  There is no finiteness, torsion or invertibility hypothesis. This is the
  coefficient universe of the recorded étale-cohomology interface; smaller
  groups are represented there by universe lifting.
- The constant étale sheaf is exactly the recorded Mathlib functor
  `constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}`.
  Its definition is constant presheaf followed by sheafification.
- `DerivedCategory.singleFunctor (Sheaf ... AddCommGrpCat.{u + 1}) 0`
  places that sheaf in degree zero.
- `cohomology AddCommGrpCat.{u + 1} (Spec (CommRingCat.of R)) 0` is the
  recorded derived-global-sections cohomology, not the Ext encoding `Sheaf.H`.
- `Nonempty (... ≅ 𝟭 AddCommGrpCat.{u + 1})` states existence of the
  requested natural equivalence. Its component at any `A` is an isomorphism
  of abelian groups, equivalently an additive equivalence to `A`.
  Naturality of the isomorphism asserts compatibility with every coefficient
  homomorphism, rather than just existence of unrelated component equivalences.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`, lines 120–135; the node's local-ring and
  separably closed residue-field conditions are precisely the class fields.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, and `AlgebraicGeometry.Spec`, definitions at lines 42, 74, 470.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Scheme.smallEtaleTopology`, lines 48–52, on the small étale category.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, lines 301–302,
  specialized to that topology and `AddCommGrpCat`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  lines 61–66, exactly sheafification of the constant presheaf.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `cohomology`,
  lines 224–236. The latter is right derived global sections followed by
  `DerivedCategory.homologyFunctor`, exactly the cohomology stipulated by the node.
- The conventions dependency fixes no separate notion and has no module to import.
  Mathlib statement dependencies are exposed transitively by the public imports.

Proof-only imports preserve the recorded plan: the full signatures and docstrings of
`AlgebraicGeometry.Etale.exists_degreeZeroCohomology_cycles_iso` and
`degreeZeroCohomology_resolution_naturality` were read in
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`; the canonical
constant-section bijectivity theorem `Scheme.bijective_toSheafify_app_terminal`
was read at lines 95–139 in
`WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`.
The connectedness and affine-spectrum notions and sheafification are already
available through these modules. All four proof steps are written in the theorem docstring.

Source reading: the ancestor blueprint's degree-zero clause in
`sec-smooth-base-change/sk-rem-rest/sbc-lem-strict-henselian-constant-cohomology.md`
and Stacks `etale-cohomology.tex`, Tag 03QO, lines 8207–8247.
The blueprint uses finite invertible coefficients, but the item's arbitrary-group
form is valid: Tag 03QO identifies sections of every sheaf with its closed stalk,
and the recorded proof uses connectedness for the constant sheaf.

Edge cases: the trivial coefficient group is included, as are infinite abelian groups
and groups with residue-characteristic torsion. A strictly henselian local ring is
nontrivial, so its spectrum cannot be empty; there is no added nonemptiness
assumption. The statement is precisely degree zero, with no positive-degree claim.
No characteristic restriction, Noetherian condition or finiteness assumption is imposed.

Searches actually run using `msearch.py NI lem-sbc-strict-henselian-constant-hzero`:

- LeanFinder: `degree zero cohomology of a constant etale sheaf on a strictly
  henselian local scheme naturally equals the coefficient group`: eight hits,
  chiefly cotangent cohomology and Hilbert 90, none an exact match.
- Loogle: `CategoryTheory.constantSheaf, CategoryTheory.NatIso`: zero hits,
  diagnostic unknown identifier `CategoryTheory.NatIso`.
- grep: `constantSheaf|equiv₀` in `CategoryTheory/Sites`: 22 hits including
  `constantSheaf`, `constantSheafAdj`, and `Sheaf.H.equiv₀`. These provide
  notions and an Ext-to-sections comparison, not the requested derived statement.
- LeanSearch: `degree zero cohomology constant sheaf connected scheme`:
  unavailable, Internal Server Error; no inference of absence is made from this.
- `rg` of the project and upstream source for constant/cohomology patterns and
  `hZeroConstant` found upstream `Scheme.hZeroConstantSheafAddEquiv`.
  Its full signature and docstring were read: it uses `Sheaf.H`, and does not
  assert naturality as a family, so it is not an exact existing declaration
  for this node's derived-cohomology statement.
- `rg` of upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the item id
  and the proposed full declaration's final name returned no matches.

Validation: `scompile.py` compiled the delivered module cleanly on the server,
nice 19, two threads, 60 seconds per file (reported compile time 1.6 s).


## Second reading by NI

Independently read the node, sandbox module, all statement-dependency records,
and the signatures defining the objects below. No mathematical or Lean mismatch
was found. The Lean module and node record are unchanged; this report adds the
second reading and fresh search/validation evidence.

Object, hypothesis and conclusion checklist (H3):

1. A commutative strictly henselian local ring R: `(R : Type u) [CommRing R]
   [IsStrictlyHenselianLocalRing R]`. PASS. Read the upstream class in
   `WeilConjectures.Mathlib.RingTheory.Henselian`: it extends
   `HenselianLocalRing R` and supplies `IsSepClosed (IsLocalRing.ResidueField R)`.
   Read Mathlib's `HenselianLocalRing` and `IsLocalRing`: these extend the
   local-ring and nontrivial-ring conditions. No additional ring hypothesis occurs.
2. X is Spec R: every occurrence is `Spec (CommRingCat.of R)`. PASS.
   Read `Scheme`, `Scheme.Hom`, and `Spec` in Mathlib's Scheme module;
   Spec is the affine locally ringed space of the given commutative ring.
3. A is an arbitrary abelian group: the source of the composite functor is
   `AddCommGrpCat.{u + 1}`. PASS. All its objects and all coefficient morphisms
   are quantified by the natural isomorphism, after R has been fixed.
   There is no finite, torsion, invertibility, or characteristic hypothesis.
4. The site is the small etale site of X: `.smallEtaleTopology`. PASS.
   Read its definition and `ofArrows_mem_smallEtaleTopology_iff` in Mathlib;
   the topology is the jointly surjective topology on schemes etale over X.
5. The constant abelian etale sheaf is
   `constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}`.
   PASS. Read Mathlib's `Sheaf`, `constantSheaf`, `presheafToSheaf`,
   `sheafificationAdjunction` and `toSheafify`: this is precisely the
   sheafification of the constant presheaf, functorially in A.
6. H^0 is the node's derived-global-sections cohomology of that sheaf:
   `DerivedCategory.singleFunctor (Sheaf ...) 0` followed by
   `cohomology AddCommGrpCat.{u + 1} (Spec (CommRingCat.of R)) 0`. PASS.
   Read the single functor in Mathlib's DerivedCategory.Basic and the definitions
   `rightDerivedGlobalSections` and `cohomology` in upstream Derived.LowerShriek:
   they put the sheaf in degree zero, derive `Sheaf.Γ`, and take zeroth homology.
7. The conclusion is a natural additive equivalence with A:
   `Nonempty (theComposite ≅ 𝟭 AddCommGrpCat.{u + 1})`. PASS.
   A functor isomorphism has mutually inverse additive homomorphisms at each A
   and its naturality equation for every A → B. Thus it states every clause,
   including naturality, without an extra choice of unrelated pointwise maps.
8. The conventions node introduces no separate notion. PASS. Its record needs
   no additional declaration, instance, or assumption here.

Source checks: read the ancestor blueprint's degree-zero clause and Stacks
`etale-cohomology.tex`, lemma-vanishing-etale-cohomology-strictly-henselian
(Tag 03QO), together with its proof. The lemma starts with an arbitrary strictly
henselian local ring and identifies sections with the closed geometric stalk
for every sheaf; it assumes neither Noetherianity nor a coefficient restriction.
Also read remark-constant-locally-constant-maps (03P5): sections of the constant
sheaf are locally constant maps for any abstract group. Read
`derived.tex`, lemma-left-exact-higher-derived (05TD), especially clause (3).
These justify the node's arbitrary-group degree-zero formulation even though
the ancestor states finite invertible coefficients.

Proof and dependency checks (H8, H13): opened
`EtaleCohomologyPullbackDegreeZero.lean` and read the signatures of
`exists_degreeZeroCohomology_cycles_iso` and
`degreeZeroCohomology_resolution_naturality`: they concern arbitrary K-injective
resolutions of the same abelian etale sheaves and the canonical augmentation
on sections. Opened upstream ConstantSheafSections and read
`Scheme.bijective_toSheafify_app_terminal`, with X and M in its enclosing
context: it is exactly the canonical constant-section map for connected X.
Read Mathlib's `ConnectedSpace`, which includes nonemptiness. The delivered
docstring carries all four node proof steps: H^0/sections comparison,
connected local spectrum, constant-section isomorphism, coefficient naturality.
All proof-only imports match the recorded plan. No new definitions, new nodes,
dependency replacement modules, or statement correction occur (4b/4c inapplicable).
There is one named theorem with its complete proof `sorry`, no data definitions,
no local notation or instances, and no unbound variables or universes.

Edge cases: the zero abelian group, infinite groups, and groups with torsion in
the residue characteristic all occur among the coefficient objects. The empty
scheme is excluded by the source's local-ring assumption itself: IsLocalRing
extends Nontrivial, and the maximal ideal gives a point. No index family is
present. The only cohomological degree is exactly zero. The parameter u is
arbitrary, and `AddCommGrpCat.{u + 1}` is exactly the recorded dependency's
coefficient universe. Smaller groups can be lifted there; a larger group and
ring can be accommodated in a common enlarged universe by lifting the ring.
There is no extra independent small test-object universe or finite-size bound.

Independent duplicate searches (H4), using words different from the worker's:

- msearch LeanFinder: `natural isomorphism zeroth derived global sections
  constant sheaf identity abelian groups`, eight hits. These include
  `Sheaf.ΓNatIsoSheafSections` and constant-sheaf adjunction ingredients,
  not this derived-cohomology statement.
- msearch Loogle: `CategoryTheory.constantSheaf`, twelve hits, including the
  exact constant-sheaf definition, adjunction, and change-of-site isomorphisms;
  no derived H^0 natural isomorphism.
- msearch grep: `hZeroConstant|cohomology_zero|constantSheaf.*[Ii]so`, four hits.
  Opened the potentially relevant `IsLocalSite.coconstantSheafΓNatIsoId` in
  Mathlib/CategoryTheory/Sites/LocalSite: it concerns the coconstant sheaf
  and ordinary global sections, so it is not a duplicate.
- Direct rg on Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  `hZeroConstant|constantSheaf.*cohomology|cohomology.*constantSheaf|
  constant.*[Hh]Zero|[Hh]Zero.*constant` found upstream
  `Scheme.hZeroConstantSheafAddEquiv`. Opened its full definition and context:
  its domain is `Sheaf.H ... 0`, the Ext encoding, and its signature asserts
  pointwise additive equivalences, not the present natural isomorphism for
  derived global sections. Thus it is not an exact existing statement.
  The other hit is a degree-one henselian comparison, not this statement.

Mechanical verification: the node's lean.statement is verbatim equal to the
file's theorem signature; every Lean line is at most 100 characters.
Compilation is performed only through the mandated server scompile.py;
no local compiler or global build was run.
