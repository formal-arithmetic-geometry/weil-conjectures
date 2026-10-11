## Worker report

The module `Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk` states
`AlgebraicGeometry.Scheme.strictlyHenselianOpen_toPresheafFiber_bijective`, with
`sorry` as its only proof. No new definition or dependency module is needed, and
no node statement is corrected.

Source checked: [Stacks Tag 03QO](https://stacks.math.columbia.edu/tag/03QO), Lemma
59.55.1, including its assertion for sheaves of sets and its identity-neighbourhood
cofinality proof. The local literature checkout is absent on this machine, so the
source was read on the Stacks website. Its argument applies to the stated open by
restricting a pointed neighbourhood to its inverse image of that open. No
Noetherian, finite type, torsion, or abelian-coefficient hypothesis is required.
The declaration docstring records all three proof steps and their DAG citations.

Hypotheses and clauses, individually:

- The scheme `T` is `{T : Scheme.{u}}`.
- The open subscheme `U ⊆ T` is `(U : T.Opens)`, its scheme is `U.toScheme`,
  and its inclusion `j` is Mathlib's `U.ι`.
- The commutative local ring is `{R : Type u} [CommRing R] [IsLocalRing R]`.
  The strictly henselian condition is `(hR : IsStrictlyHenselianLocalRing R)`,
  exactly the recorded conjunction of henselianity and a separably closed
  residue field. Its maximal ideal and residue field are those of `IsLocalRing`.
- The specified isomorphism with the affine spectrum is
  `(e : U.toScheme ≅ Spec (.of R))`.
- The algebraically closed field is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`.
  The geometric point of `T` is `(s : Spec (.of Ω) ⟶ T)`.
- The same point regarded as a point of `U` is the lift
  `(t : Spec (.of Ω) ⟶ U.toScheme)` with `(ht : t ≫ U.ι = s)`.
  Giving this lift does not strengthen the hypotheses: factorization through an
  open containing the point exists and is unique. It explicitly supplies the
  pointed neighbourhood already described in the node.
- Its image is the point corresponding to the maximal ideal precisely when
  `(hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)`.
  `default` is the unique point of the spectrum of the field `Ω`;
  `IsLocalRing.closedPoint R` is the prime defined by the maximal ideal.
  Thus the image of `s` is `U.ι (t default)`, the node's point `u ∈ U`.
- The inclusion is etale without an additional hypothesis: the open-immersion
  instance for `U.ι` supplies its `Etale` instance in `Etale.mk U.ι`.
- The pointed etale neighbourhood is the pair with underlying site object
  `Etale.mk U.ι` and lift `Over.homMk t ht`. This is an element of
  `(pointSmallEtale s).fiber`, hence an object of its category of elements.
- Every sheaf of sets is quantified by
  `(G : Sheaf (smallEtaleTopology T) (Type (max u v)))`.
  The extra universe `v` allows arbitrarily large sets while the `max` supplies
  the colimits of the site-point universe `u`; there is no smallness restriction
  on sheaf values relative to the site.
- The germ map is exactly
  `(pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) G.obj`.
  Its source is `G.obj (op (Etale.mk U.ι)) = G(U)`. Its target is definitionally
  `((pointSmallEtale s).sheafFiber).obj G = G_s`, the recorded geometric stalk.
  `toPresheafFiber` is the colimit coprojection at this pointed neighbourhood,
  so the map is the germ map, not an arbitrary bijection.
- Bijectivity of that very map is `Function.Bijective` in the conclusion.
- The parenthetical special case `U = T = Spec R` gives the identity open and
  the usual global-sections-to-closed-stalk map of Tag 03QO. The reference to the
  abelian sibling is explanatory and imposes no abelian structure here.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its scheme morphisms in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; the statement uses `Spec` directly.
- `def-weil-pbc-henselian-terminology`: `IsStrictlyHenselianLocalRing` in
  `Sheaf.RingTheory.HenselianTerminology`, imported directly.
- `def-weil-geometric-point`: the recorded field-spectrum morphism encoding,
  with `Field Ω` and `IsAlgClosed Ω`; the signature/docstring of
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` was read.
- `def-weil-pbc-pointed-etale-neighbourhoods`: `Functor.Elements` and
  `categoryOfElements` in `Mathlib.CategoryTheory.Elements`, applied to the
  fiber of `Scheme.pointSmallEtale`, as its Mathlib match specifies. The
  neighbourhood is supplied directly to `Point.toPresheafFiber`, which forms
  its category-of-elements object internally.
- `def-weil-pbc-etale-sheaf-of-sets`: `CategoryTheory.Sheaf` in
  `Mathlib.CategoryTheory.Sites.Sheaf`, on `Scheme.smallEtaleTopology`.
- `def-weil-pbc-geometric-stalks`: `Point.sheafFiber` in
  `Mathlib.CategoryTheory.Sites.Point.Basic` and `Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`, imported via the latter module.
  Their signatures, docstrings, and the definition of `Point.toPresheafFiber`
  were read. No private stalk or germ definition was introduced.

Edge cases checked mathematically before writing:

- `U = T = Spec R` recovers the source assertion.
- An empty `U` or empty `T` cannot satisfy the geometric-point and affine-local
  hypotheses; no arbitrary nonemptiness binder is introduced.
- A zero ring cannot be the local ring here, since Mathlib's `IsLocalRing` has
  a proper maximal ideal; this agrees with the source's local-ring convention.
- Empty section sets are allowed: the resulting empty stalk is covered by
  `Function.Bijective`, without a chosen section or nonempty-set assumption.
- All characteristics and non-Noetherian strictly henselian rings are included.
- Algebraically closed extensions larger than the residue field are allowed;
  the point need not be literally the residue-field spectrum.
- The ambient `T` need not itself be affine, local, or strictly henselian.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "sections of etale sheaf on strictly henselian local
  scheme equal stalk"`: service unavailable, Internal Server Error.
- `msearch.py ... leanfinder "sections of etale sheaf of sets on strictly
  henselian local scheme equal stalk at closed point"`: eight hits, all structure
  sheaf / Zariski stalk declarations such as `Scheme.stalkClosedPointTo` and
  `germ_stalkClosedPointIso_hom`; no arbitrary etale sheaf of sets statement.
- `msearch.py ... loogle "GrothendieckTopology.Point.presheafFiber, colimit.ι"`:
  no hits, unknown identifier in that service's index. The local Mathlib source
  supplies `Point.toPresheafFiber`, the germ-map construction, not this theorem.
- `msearch.py ... grep "henselian|Henselian" AlgebraicGeometry/Sites`: no hits.
- `rg` of `WeilConjectures` and `lean/Sheaf` for henselian/stalk/sections and
  `toPresheafFiber.*bijective`: no exact statement. Projective-line cohomology,
  structure-sheaf henselian stalks, and open etale decomposition are different.
- `rg` of `WeilConjectures` and `dag/lean_names_upstream.json` for the item id:
  no match. The chosen full declaration name was also searched in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py F1 lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`
compiled the module on the server in 1.7 seconds, exit code 0, with no warnings.
All universes and variables in the signature are explicitly bound. No disputed
statement or dependency fault was found.

## Second reading by F1

Independent reading of the node copy, its three proof steps, the module, all
seven statement dependency nodes, and the declarations those records identify.
Verdict: the Lean says exactly what the node says. No statement, module, or
node-record repair was necessary; this reading adds the review report only.

Source: the local Stacks checkout is absent. I read the raw Stacks source
[etale-cohomology.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex),
lines 7607–7648, including the preceding section introduction and
`lemma-vanishing-etale-cohomology-strictly-henselian`, and
[Tag 03QO](https://stacks.math.columbia.edu/tag/03QO). The section has no standing
Noetherian, separatedness, or characteristic hypothesis. The sets assertion
uses only strict henselianity and the geometric closed point. To apply it
inside the stated ambient scheme, replace each neighbourhood by its inverse
image of `U`; the section over `U` then remains a pointed morphism over `T`.

Object/hypothesis/conclusion inventory and Lean correspondence:

1. Arbitrary scheme `T`: `{T : Scheme.{u}}`. Exact; the dependency
   `def-pc-scheme` uses Mathlib's `Scheme`, a locally ringed space with local
   affine charts. I read `Scheme.lean:42` and its scheme-morphism encoding.
2. Open subscheme `U` of `T`, with its inclusion `j`: `(U : T.Opens)`,
   `U.toScheme`, and `U.ι`. Exact; `Restrict.lean:46–56` constructs the actual
   restriction and canonical open immersion, rather than another scheme with
   an unconstrained morphism. No extra immersion hypothesis is imposed.
3. Commutative local ring `(R, m, κ)`: `{R : Type u} [CommRing R]
   [IsLocalRing R]`. Exact; `IsLocalRing.closedPoint R` is defined by
   `IsLocalRing.maximalIdeal R` in `Spectrum/Prime/Topology.lean:1299`.
   Its residue field is the one in the recorded henselian definition.
4. Strict henselianity: `(hR : IsStrictlyHenselianLocalRing R)`. Exact;
   I opened `Sheaf.RingTheory.HenselianTerminology` and read its definition
   `HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R)`.
   This is the dependency's notion, with genuine data and no hollow definition.
5. Spec identification of the open: `(e : U.toScheme ≅ Spec (.of R))`.
   Exact; `def-weil-affine-spectrum` points to `Spec` in `Scheme.lean:470`,
   whose carrier is the prime spectrum and whose structure is the affine
   locally ringed space. No affineness assumption on all of `T` is added.
6. Geometric point of `T`: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
   and `(s : Spec (.of Ω) ⟶ T)`. Exact; I read the dependency's
   `Scheme.SpecToEquivOfField` signature and construction in
   `ResidueField.lean:346`, which encode a point and its residue-field map.
7. Its image is the closed point in the specified open: the lift
   `(t : Spec (.of Ω) ⟶ U.toScheme)`, `(ht : t ≫ U.ι = s)`, and
   `(hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)`.
   Exact. `default` denotes the unique point of the field spectrum. Since
   `s` has image inside the open, it factors uniquely through the open
   immersion; supplying that unique lift is precisely the node's instruction
   to regard the point as a morphism to `U`, not a stronger hypothesis.
8. The inclusion is etale, giving the pointed neighbourhood `(U, t)`:
   `Etale.mk U.ι` and `Over.homMk t ht`. Exact. The open-immersion-to-etale
   instance is in `Morphisms/Etale.lean:78`; `Etale.mk` at line 191 packages
   that instance. I read `Functor.Elements` and `categoryOfElements` in
   `CategoryTheory/Elements.lean:48–67`, and the definition of
   `pointSmallEtale` in `Sites/EtalePoint.lean:64`. Its fiber is exactly lifts
   over `s`, and its elements category has the pointed morphisms of the node.
9. Every sheaf of sets on the small etale site:
   `(G : Sheaf (smallEtaleTopology T) (Type (max u v)))`. Exact;
   `smallEtaleTopology` in `Sites/Etale.lean:51` is the specified topology,
   and `Sheaf` in `CategoryTheory/Sites/Sheaf.lean:302` is the full category
   of presheaves satisfying the sheaf condition. There is no abelian,
   constructibility, finiteness, or nonempty-section restriction.
10. Sections `G(U)`: `G.obj.obj (op (Etale.mk U.ι))`, the domain of
    `(pointSmallEtale s).toPresheafFiber (Etale.mk U.ι)
    (Over.homMk t ht) G.obj`. Exact: this is evaluation on the open's
    etale-site object, not its Zariski structure-sheaf sections.
11. Stalk `G_s` and the germ of that section at `(U,t)`: the codomain and
    map of that same `toPresheafFiber` term. Exact. I read
    `Point.presheafFiber` and `Point.toPresheafFiber` at
    `Sites/Point/Basic.lean:96–105`: the latter is `colimit.ι` at the
    opposite elements object. `Point.sheafFiber` at line 277 restricts the
    same functor to sheaves, so its value at `G` is definitionally this
    codomain. The dependency's stalk and canonical map are used directly.
12. Bijectivity of the specified germ map for every `G`:
    `Function.Bijective` of the above term. Exact; all preceding objects and
    hypotheses occur before `G`, as in the node. No arbitrary bijection or
    bare existence of an isomorphism replaces the canonical map.
13. Parenthetical identity-open case and abelian sibling: `U = ⊤` with
    `T = Spec R` and its canonical restriction isomorphism yields the source's
    global-sections map. The abelian sibling is explanatory, not an extra
    assertion or coefficient hypothesis in this node.

Edge cases: empty `T` admits no such `s`, and empty `U` admits no such `t`;
these are consequences of the geometric-point data, not added nonemptiness
assumptions. `IsLocalRing` extends `Nontrivial` (read `LocalRing/Defs.lean:30`),
so the zero ring is excluded exactly as in the source's local-ring convention.
An empty section set is allowed, as is a singleton section set; bijectivity
makes no choice of a section. There is no index family, degree `n`, or torsion
parameter to specialize. Every characteristic and non-Noetherian case is
covered. The geometric field need not be the residue field or its algebraic
closure specifically. The explicit shared universe `u` is that of Mathlib's
scheme category, `Spec`, and `pointSmallEtale`; it is arbitrary and can be
chosen large enough for all geometric data. The sheaf-values universe
`max u v` is arbitrary above the site's fiber universe, supplying the required
Type-valued colimits without a hypothesis on the sheaf or a vacuous test
universe. All variables and universes are explicitly bound.

Independent searches, using different phrases from the first reading:

- LeanFinder via `msearch.py`: "canonical map to etale fiber bijective for a
  henselian ring with separably closed residue field". Eight hits, including
  `StandardEtalePresentation.lift_bijective`, `RingHom.Etale.of_bijective`, and
  `Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing`.
  These concern ring maps, not sections of arbitrary etale sheaves.
- Loogle via `msearch.py`: `Function.Bijective, HenselianLocalRing`.
  Successful search with zero hits.
- LeanSearch via `msearch.py`: "etale sheaf germ bijective strictly local ring".
  Service unavailable (Internal Server Error); no mathematical verdict is
  inferred from the failed service.
- `rg` of Mathlib's algebraic geometry, the project's `lean/Sheaf`, and
  `WeilConjectures` for `toPresheafFiber`, `StrictlyHenselian`,
  `strictlyHenselian`, and both orders of henselian/stalk. Also searched
  `WeilConjectures/AlgebraicGeometry/Sites` for henselian/local-stalk wording.
  The hits concern structure-sheaf germs, torsion, constant-sheaf stalks,
  projective-line cohomology, or maps between stalks, not this theorem.
  The upstream-name table and source contain neither the item id nor the
  proposed full declaration name. No existing exact declaration was found.

There are no new definition nodes or delivered dependency modules to review,
and no `statement_change`. All seven dependency records suffice for their
uses here; no private definition is needed. H5/H6: the file has no definitions
and exactly one theorem whose entire proof is `sorry`. H8: both docstrings
name Tag 03QO and the blueprint id; the declaration's proof text follows all
three DAG steps, including affine shrinking inside `U`, residue-field
compatibility of the retraction, and singleton-subcategory colimit computation.
H9: the namespace, module path, imports, and 100-character line width agree
with the conventions. Both imports serve the statement.

Mismatches found and repairs: none. The Lean file and the node's recorded
signature remain unchanged. I checked the recorded signature against the
file verbatim; validation results follow below.

Validation by the second reader: the signature is verbatim equal to
`lean.statement`; all Lean lines are at most 100 characters. The authorized
`scompile.py` invocation using the absolute sandbox module path compiled the
file on the server in 1.8 seconds, exit code 0, without warnings or errors.
An initial invocation used a path relative to the read-only repository and
failed to find the sandbox file; using its absolute path resolved this.
