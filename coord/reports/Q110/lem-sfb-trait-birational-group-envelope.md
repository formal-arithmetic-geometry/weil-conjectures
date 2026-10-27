## Worker report

States `AlgebraicGeometry.exists_trait_birationalGroupEnvelope` with one `sorry` and adds
the real definitions needed for relative rational multiplication. There is no proof or
choice of an unspecified envelope. The item's statement and proof are unchanged.

Source read: the BLR primary scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
4.3 Theorem 6 (printed p.108; PDF p.114), 5.1 Definition 1 and Theorem 5 including the
no-shrinking paragraph (printed pp.112–114; PDF pp.118–120), and 2.5 on S-rational maps.
The source explicitly allows X' = X when the entire generic fibre is a group scheme.
The item is a supporting node, not a blueprint unit statement. No statement correction.

Clause-by-clause translation:

- R is a DVR: `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  E is the canonical `FractionRing R`; T is `Spec (.of R)`. The special fibre is
  `Y.hom.fiber (IsLocalRing.closedPoint R)`, canonically the fibre over R/m.
- Y is a T-scheme: `Y : Over (Spec (.of R))`. Smooth, separated, finite type are
  `[Smooth Y.hom]`, `[IsSeparated Y.hom]`, `[LocallyOfFiniteType Y.hom]`
  and `[QuasiCompact Y.hom]`. `hSpecial` says its special fibre is nonempty.
- Products are the cartesian tensor products in `Over T`; the underlying scheme is
  `pullback Y.hom Y.hom`. Fibres and base changes are `Over.pullback` and `Hom.fiber`.
- The generic group is `G : Grp (Over (Spec (.of (FractionRing R))))` and `e` identifies
  Y_E with its underlying E-scheme. Smoothness and finite type of G are already implied
  by this identification and the hypotheses on Y; no independent restriction is needed.
- The rational multiplication is supplied by a representative `m` on an open dense in
  every fibre. This is a presentation of the rational map in the node, retaining the
  chosen representative for the final restriction equation. `hGenericDomain` says the
  base change of its inclusion is an isomorphism, i.e. the domain contains all (Y×Y)_E.
  `hGenericMul` is the multiplication agreement after the canonical product comparison
  and `e ⊗ e`. It imposes exactly the given generic group law.
- `hLaw` contains the two fibrewise birational universal translations and associativity.
  Each translation is an open immersion with dense image after a fibrewise dense domain
  restriction, precisely an isomorphism between dense open subschemes. Associativity
  quantifies over every test T-scheme and four lifts to the multiplication domain,
  hence tests equality of scheme morphisms rather than only ordinary points.
- The conclusion existentially supplies `M : Grp (Over T)`, together with Smooth,
  LocallyOfFiniteType, QuasiCompact and IsSeparated for its structure morphism.
- `j : Y ⟶ M.X` is over T; `IsOpenImmersion j.left` and
  `RelativeGroupLaw.IsFiberwiseDense M.X (Set.range j.left)` give the exact open and
  T-dense image clauses.
- The group isomorphism `a : G ≅ (Over.pullback ...).mapGrp.obj M` and its equation
  `e.hom ≫ a.hom.hom.hom = (Over.pullback ...).map j` assert that j_E is the specified
  generic group isomorphism. The group structure on M_E is the canonical pullback one.
- `m.hom ≫ j = m.inclusion ≫ (j ⊗ₘ j) ≫ μ[M.X]` asserts multiplication restricts to m
  on its full supplied domain. No mapping property is present.

Dependency declarations used, with their recorded modules and source signatures read:
`Scheme` and `Spec`, `Spec.map` in Mathlib.AlgebraicGeometry.Scheme;
`IsDiscreteValuationRing` in Mathlib.RingTheory.DiscreteValuationRing.Basic;
`Over.pullback`, `baseChange_morphism_projections` and fibre conventions from
WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
`Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth;
`LocallyOfFiniteType` and `QuasiCompact` in Mathlib.AlgebraicGeometry.Morphisms.FiniteType
and QuasiCompact; `IsClosedImmersion` in Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
used by the standard `IsSeparated` diagonal condition;
`GrpObj`, `Grp` in Mathlib.CategoryTheory.Monoidal.Grp;
`IsOpenImmersion` in Mathlib.AlgebraicGeometry.OpenImmersion.
The standard slice cartesian structure and pullback group functor are used directly,
with no replacement definition of group schemes.

Proof imports: Mathlib.AlgebraicGeometry.Morphisms.Proper for the recorded proper
base-change dependency. Smooth base change and composition are already publicly imported
by the statement. The proof-only nodes lem-sfb-birational-law-strictification,
lem-sfb-strict-birational-law-realization, lem-sfb-smooth-trait-birational-immersion,
lem-sfb-relative-weil-codimension-extension and
lem-sfb-smooth-trait-local-rational-spreading have no recorded declarations yet; there
is no module to import for them. All five are explicitly retained in the proof docstring.

Edge cases checked: a DVR is explicitly not a field in Mathlib's class; empty special
fibre is excluded exactly by the stated hypothesis; disconnected groups and positive
characteristic are allowed; neither commutativity, properness, henselianity nor a
connected-fibre assumption occurs. Density is tested on both fibres, not just on the
total space. Empty fibres impose the ordinary vacuous density condition in the general
helper definition. Test schemes have the same unrestricted universe u as the schemes;
this includes the common domain itself, so the Yoneda form detects scheme equality.
Use of the canonical fraction field does not choose a smaller field or impose a field
extension hypothesis. A group structure on the generic fibre ensures it is nonempty.

Searches: msearch LeanFinder for a smooth birational group envelope over a DVR found
only smoothness and Weierstrass reduction results; Loogle for Scheme.RationalMap,
GrpObj and Scheme.PartialMap had no match (remote index does not resolve these names).
The local Mathlib sources do contain GrpObj and absolute RationalMap, and these were
read. msearch LeanSearch for relative rational maps returned absolute PartialMap and
RationalMap; LeanFinder for fibrewise density returned ordinary dominance; msearch
grep `RelativeRational|FiberwiseDense|FibrewiseDense|BirationalGroupLaw` found no match.
`rg` over WeilConjectures and Sheaf found no relative rational map or birational group
law definition and no declaration tagged with the item id. DAG definition nodes and
`blueprint_refs.py search birational`/`search 'rational map'` yielded no duplicate
notion (the birational blueprint hits concern normalization). Absolute RationalMap
cannot replace the relative quotient: an open containing only the generic fibre may
be dense in the total space and miss the special fibre completely.

Compilation: both delivered files compiled individually, in dependency order, through
scompile.py against the live server build, with no errors or warnings. The theorem
retains its required sorry. No STATEMENT-DISPUTED issue was found.

## New nodes

`def-sfb-relative-birational-group-law` owns RelativeBirationalGroupLaw.lean. It defines
fibrewise density, relative representatives, agreement and their quotient, birational
representatives, the two actual universal translation maps, and associativity/birational
law predicates. All data are explicit definitions; there are no postponed theorems.
Source: BLR 2.5 and 5.1 Definition 1. Its three recorded searches are the actual
msearch outputs saved in this sandbox; no existing DAG definition, Mathlib relative
interface, upstream declaration or Sheaf declaration gives the notion. The new node
cites the existing scheme, base-change and open-immersion definitions and is added to
the item's statement dependencies. The main theorem works with a representative so
that it can preserve the entire generic domain and state restriction on that domain;
no arbitrary quotient representative or noncanonical choice is used.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
