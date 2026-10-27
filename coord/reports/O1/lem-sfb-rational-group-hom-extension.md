## Worker report

Item: `lem-sfb-rational-group-hom-extension`, group O1, stage 2, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.GroupScheme.RationalHomExtension`.

The module states the unique homomorphism extension and, in a second declaration,
the unique group-isomorphism extension of a birational map. Both proofs are `sorry`.
There are no new definitions. The node copy changes only `lean`.

### Clause-by-clause correspondence

- Any base scheme: `{S : Scheme.{u}}`, with explicit `universe u` and
  `set_option autoImplicit false`. There are no field, normality, Noetherianity,
  reducedness or connectedness assumptions.
- S-group schemes G,H: `(G H : Over S) [GrpObj G] [GrpObj H]`.
  The morphisms of `Over S` are scheme morphisms commuting with the structure maps;
  `GrpObj` supplies multiplication, unit and inverse with the group-object diagrams.
  This is the general group-object API recorded by `def-sc-group-scheme`, applied
  over the base S as the item explicitly specifies.
- Smooth: `[Smooth G.hom] [Smooth H.hom]`.
- Separated: `[IsSeparated G.hom] [IsSeparated H.hom]`. The class is defined by the
  closed-immersion property of the scheme-theoretic diagonal, exactly as in the node.
- Finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` and the same pair
  for H, following the recorded finite-type dependency's conjunction convention.
- Products and fibres: the Cartesian monoidal structure on `Over S` has
  `(A ⊗ B).left = pullback A.hom B.hom`. Its maps `⊗ₘ` are the maps of scheme
  fibre products. `f.fiberι s` is the first projection from the actual pullback
  `f.fiber s = pullback f (S.fromSpecResidueField s)`.
- Open U in G: `(U : Over S) (j : U ⟶ G) [IsOpenImmersion j.left]` represents
  an arbitrary open subscheme by its inclusion, up to its canonical isomorphism.
- S-density of U: `hU : ∀ s : S, Dense ((G.hom.fiberι s) ⁻¹' Set.range j.left)`.
  The preimage is exactly the open subset U_s in the scheme-theoretic fibre G_s,
  since base change of an open immersion is the inverse-image open subscheme.
- S-morphism a: `(a : U ⟶ H)`.
- Domain of a(xy): `D = pullback ((j ⊗ₘ j) ≫ μ[G]) j` in `Over S`. Its first
  projection goes to U ×_S U, while its second projection supplies the product
  in U. Thus it is precisely the inverse image of U under multiplication on
  U ×_S U. No pointwise approximation to this domain is used.
- S-dense open of that domain: `hcompat` existentially quantifies `(W : Over S)`
  and `(k : W ⟶ D)`, requires `IsOpenImmersion k.left`, and requires
  `∀ s : S, Dense ((D.hom.fiberι s) ⁻¹' Set.range k.left)`.
- Rational multiplicativity: the remaining conjunct of `hcompat` equates
  `k ≫ pullback.fst ... ≫ (a ⊗ₘ a) ≫ μ[H]` with
  `k ≫ pullback.snd ... ≫ a`. These are the scheme morphisms a(x)a(y) and a(xy)
  on W, including their sheaf maps; the equality is in `Over S`.
- Extension and uniqueness: `∃! f : G ⟶ H, IsMonHom f ∧ j ≫ f = a`.
  `IsMonHom` supplies the unit and multiplication diagrams; between group objects
  this also preserves inverses. The restriction equality is on the whole given U.
- In-particular birational clause: the second theorem adds `(V : Over S)` and
  `(jV : V ⟶ H) [IsOpenImmersion jV.left]` with the corresponding fibrewise
  density `hV`, and `(α : U ≅ V)`. Thus α is an isomorphism between S-dense opens,
  representing exactly the S-birational map specified in the node.
- Multiplicativity of that birational map is the same `hcompat` with
  `a = α.hom ≫ jV`. Its conclusion is
  `∃! f : G ≅ H, IsMonHom f.hom ∧ j ≫ f.hom = α.hom ≫ jV`.
  A scheme isomorphism whose forward map is a group homomorphism has a group
  homomorphism as inverse, so this is exactly a group-scheme isomorphism.
  Uniqueness on the prescribed dense open also gives uniqueness for the represented
  rational map: representatives agreeing on a dense common open have the same extension.

### Dependencies and sources read

Statement dependencies and the declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
  Its recorded convention expressly directs scheme products to `Limits.pullback`;
  `moduleBaseChange` is only the module-sheaf part and is irrelevant here.
  `Scheme.Hom.fiber` and `Scheme.Hom.fiberι` are reexported from
  `Mathlib.AlgebraicGeometry.Fiber`. Their definitions and the Cartesian structure
  in `Mathlib.AlgebraicGeometry.Pullbacks` were read.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; also
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, used through the definition of
  `AlgebraicGeometry.IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`,
  `CategoryTheory.GrpObj`, with `CategoryTheory.MonObj.mul` and
  `CategoryTheory.IsMonHom` from `Mathlib.CategoryTheory.Monoidal.Mon`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (publicly available through the imports above).

The recorded source declarations and docstrings were read, including the upstream
`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` explanation of the group-object
and group-homomorphism encodings. Its field-specific auxiliary definitions are unnecessary.
All dependencies use their recorded notions; no dependency record needed repair.

The stated proof dependencies are imported, using plain imports for proof-only modules:
Mathlib Smooth (smooth-flat, smooth-composition, open restriction and smooth base change),
Proper (proper base change), UniversallyOpen (flat lfp openness), QuasiSeparated and
their affine-scheme imports (affine qcqs), Sites.Fpqc (covering and representable descent),
and `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`
(`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated`).
`lem-sfb-smooth-fibrewise-dense-open-base-change` has no Lean record or Mathlib match
in the read clone, so its module cannot yet be imported. It remains an unchanged proof
prerequisite and is explicitly cited in both proof docstrings.

Read the primary BLR scan linked in the node, printed pp.55--58 and 112--114,
especially 2.5's definition of S-density and S-birational maps, 2.5 Proposition 5,
and 5.1 Lemma 4 and Proposition 3. The scan's one-based physical pages for printed
pp.113--114 are 120--121. The node's source-place PDF page numbers are one page low;
its printed page references and mathematical content are correct. This bibliographic
observation does not require a statement change. The theorem docstrings reproduce
the eight-step accepted DAG proof, including the actual kernel pair, fpqc descent,
agreement on all U, multiplicativity and extension of the inverse rational map.

### Edge cases

- Empty S: the fibre-density quantifiers are vacuous; any S-scheme is empty and
  the extension and isomorphism conclusions still hold. Nothing excludes this case.
- Nonempty S and empty U: each G_s has the unit point, so U cannot satisfy hU.
  There is no extra nonemptiness assumption.
- Disconnected fibres and finite étale groups: density is required on the entire
  fibre, hence on every component; connectedness and irreducibility are never used.
- Nonreduced bases: morphism equality in `Over S` includes nilpotents, and the proof
  uses schematic density instead of a reduced-source dominance lemma.
- Noncommutative groups: `GrpObj` has no commutativity requirement, and the tensor
  factors preserve the order of x and y.
- U containing the identity is not required. U and W need not be quasi-compact.
- Empty fibres of intermediate opens and domains are permitted by `Dense` on the
  empty fibre. There is no choice of geometric/rational point in the signature.
- All schemes and their fibres live in the same arbitrary universe u; no finite-size
  restriction or additional universe equality is imposed.

### Searches

All service searches used the prescribed `msearch.py O1 lem-sfb-rational-group-hom-extension`:

- LeanFinder query: `A rational group homomorphism between smooth separated group
  schemes over any base scheme extends uniquely to a group scheme homomorphism`.
  Eight results, headed by `ext_of_isDominant_of_isSeparated'`, `IsSmooth`, and
  `AffineSpace.hom_ext`. None constructs this extension.
- Loogle query: `"RationalMap", "Group"`. Zero results.
- Mathlib grep query:
  `rational.*homomorphism|birational.*homomorphism|homomorphism.*rational`.
  Zero results.
- LeanSearch query: `A rational homomorphism of smooth separated group schemes
  over a scheme extends uniquely from a fibrewise dense open to a group scheme
  homomorphism`. Eight results: separated-target uniqueness, ordinary
  `Scheme.PartialMap` constructors and restrictions, uniform-ring extension,
  rational-number ring homomorphisms, and continuous algebra maps. None matches.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` by rational/birational homomorphism
  wording finds rational Tate modules, rationalized abelian-variety Hom groups,
  and representation theory. These are different notions, not maps from an open
  subscheme. Searching the exact node id in those two trees finds no declaration.
- `rg` of the DAG for fibrewise-density wording found statement nodes using it;
  no private predicate is needed: the signature directly uses Mathlib `Dense`,
  inverse image and the recorded scheme-theoretic fibre.
- Full new declaration names were checked against `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

### Validation

`scompile.py O1 lem-sfb-rational-group-hom-extension` compiled the module in sandbox
and library module modes, within the 60-second per-file limit, with no errors or warnings.
The node's `lean.statement` was extracted verbatim from the main theorem signature.
Both theorem names are listed in `lean.declarations`. Every variable and universe is bound.

## Second reading by O1

Author's separate self-check, under the dispatcher instruction not to start other agents;
the maintainer supplies the independent review. Reopened the node and module and matched
all clauses above. In particular: the compatibility open is dense in the domain of a(xy),
not an unrelated product; the equality is an equality of morphisms, not only geometric
points; the extension restricts to the entire original U; both G and H carry all three
geometric hypotheses; and the second theorem includes both dense opens and their actual
S-isomorphism. `IsMonHom` asks for the same group-homomorphism structure as the node.
The inverse map of the final isomorphism is not extra assumed data.
No mathematical mismatch, statement correction, or disputed statement was found.
