## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology` gives real definitions
for all notions of the node; there are no theorems, proofs, choices of geometric data,
or sorries. All declarations are in `AlgebraicGeometry.PrimeToEllAlteration`.
The original statement and dependency list are unchanged. No repair note was present.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, printed
pp. 23--28 (PDF pages 29--34), especially 1.1.2, 1.1.8, 1.2.2, 2.1.1--2.1.2,
2.3.1 and Remark 2.3.2. The last remark is why the generating families are not
asserted to be a pretopology. Section 3 supplies the language of refinement.

Clause-by-clause correspondence:

* The scheme base is `S : Scheme.{u}` with `[IsNoetherian S]`. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` and
  `isNoetherian_iff_of_finite_affine_openCover` identify this class with the node's
  finite affine covering by Noetherian rings. No separatedness, reducedness,
  irreducibility, nonemptiness or excellence is assumed for S. The prime is
  `ell : ℕ` with `[Fact ell.Prime]` in `topology` and `IsCoveringFamily`.
  The subsidiary predicates are defined more generally for every natural ell.
* `Alt S` is the full subcategory of `Over S` satisfying exactly four conditions:
  `LocallyOfFiniteType T.hom`, `QuasiCompact T.hom` (together finite type),
  `IsReduced T.left`, and the condition on generic points. A generic point x is
  rendered literally by `closure ({x} : Set X) ∈ irreducibleComponents X`.
  At each source generic point, its image has the same condition in S and
  `(T.hom.residueFieldMap t).hom.Finite` expresses the finite field extension.
  Morphisms of the full subcategory are precisely the over-category morphisms:
  `f.hom.left` is the underlying scheme map and `f.hom.w` its equation over S.
  This does not require objects to dominate all components or be proper.
* `IsMaximallyPrimeToEllFinite ell f` first requires finite residue extensions
  at every source generic point. It then quantifies over target generic points
  `y ∈ Set.range f`, and requires a source generic x with `f x = y` and
  `Nat.Coprime (f.residueDegree x) ell`. Finiteness at this chosen x is already
  required by the first conjunct. The test uses the actual residue-field map,
  not an independently chosen algebra structure.
* `IsPrimeToEllDecomposedEtaleFamily ell U f` requires `Etale (f i).hom.left`
  for every member and, for every target point t, a member i and a point x over t
  with finite residue extension and residue degree coprime to ell.
  `IsCompletelyDecomposedEtaleFamily` uses the same étaleness and point-lifting
  clauses, with `IsIso ((f i).hom.left.residueFieldMap x)` for the canonical map
  on residue fields. It is not merely an abstract field isomorphism.
* `IsPrimeToEllDecomposedEtalePresieve` is the same étale-generator condition
  expressed directly on a `Presieve T`. It quantifies over its arrows rather
  than over a separately chosen indexing type. This avoids restricting the
  generator class to any fixed index universe: a family of any size gives its
  presieve via `Presieve.ofArrows`, and every presieve is indexed by its arrows.
  Étaleness and the existence of finite prime-to-ell lifts are unaffected by
  repeated arrows or their removal. This helper belongs to the same node.
* `topology S ell` is `sInf` of the set of Grothendieck topologies J satisfying
  both generator conditions. The first is membership of `Sieve.generate R`
  for each decomposed étale presieve. The second is membership of
  `Sieve.generate (Presieve.singleton f)` for every arrow with `IsProper`,
  `Surjective` and `IsMaximallyPrimeToEllFinite` on its underlying scheme map.
  The complete lattice of Grothendieck topologies makes this exactly the
  smallest such topology. This is concrete Mathlib lattice data, with no
  postponed well-definedness proof or arbitrary chosen topology.
* `IsCoveringFamily` says `Sieve.ofArrows U f ∈ topology S ell T`.
  Mathlib defines `Sieve.ofArrows` as `Sieve.generate (Presieve.ofArrows U f)`;
  its `mem_ofArrows_iff` says exactly that an arrow factors through a member.
* `Refines A a B b` says `∀ i, ∃ j, ∃ h : A i ⟶ B j, h ≫ b j = a i`.
  This is precisely a morphism over T for every member of A, with no added
  joint surjectivity or covering assumption on either family.

Dependencies read and used (all their recorded modules are public imports):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; used through the
  Noetherian scheme class and its finite-affine-cover characterization from
  `Mathlib.AlgebraicGeometry.Noetherian`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `QuasiCompact` from `Morphisms.QuasiCompact`, imported transitively.
* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and the existing `Scheme.Hom.residueDegree`.
  `RingHom.Finite`, from `Mathlib.RingTheory.Finiteness.Defs`, is finiteness as
  a module under the map's induced algebra; for fields this is finite degree.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `Sheaf.CategoryTheory.Sites.GrothendieckTopos`: the dependency's published
  module, using its Mathlib `GrothendieckTopology`, `Sieve` and `Presieve`
  interfaces. Its main `IsGrothendieckTopos` predicate is not needed here:
  the node only uses the topology portion of this dependency.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
* `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
* `Mathlib.Topology.Irreducible`: `irreducibleComponents`, the recorded Mathlib
  match for `def-weil-irreducible-components` (this leaf has no lean record).

Supporting categorical APIs are `ObjectProperty.FullSubcategory` and `Over`,
with their existing category instances, and the complete lattice on
`GrothendieckTopology` and the existing generated sieves. No dependency needs
an interface repair and no independent notion requires a new node.

Edge cases checked before and during drafting:

* Empty source: generic-point conditions are vacuous. Empty target: all
  point-lifting requirements are vacuous, so an empty family is allowed there.
  Over a nonempty target an empty family is not a decomposed étale generator.
* Empty S is allowed by the Noetherian class, and no nonempty or integral
  constraint is imposed on the full subcategory.
* Nonreduced S remains allowed, whereas all objects are required to be reduced.
* Reducible T and T' use every irreducible component's generic point; no single
  arbitrary generic point is selected. The maximal-finiteness lifting clause
  applies only to target generic points in the image, exactly as in 1.1.8.
* Identity maps have residue degree 1, hence are prime to every prime ell.
  For Spec C → Spec R the degree 2 passes the degree test for ell=3 and fails
  it for ell=2. Étale families require point lifts at all points, not just
  generics, as emphasized immediately after ILO II 2.3.1.
* `Scheme.{u}` is uniform in u; the category has object universe u+1 and
  morphism universe u. Family predicates permit arbitrary `I : Type w`;
  refinement permits independent `Type w` and `Type w'`. Topology generators
  are presieves, avoiding an artificial bound on the indexing universe.
* The convention `residueDegree = 0` for an infinite extension cannot create a
  false finite generator: explicit finiteness accompanies every degree test
  (in the maximal case, through the first conjunct).

Searches for an existing declaration:

* msearch leanfinder: `category of reduced generically finite schemes and topology
  generated by prime to ell decomposed etale covers and proper surjective alterations`:
  8 hits, all ordinary étale, jointly surjective or Zariski sites; no match.
* msearch loogle: `CategoryTheory.GrothendieckTopology.generate,
  CategoryTheory.Sieve.generate`: unavailable as written, since the first
  identifier does not exist. The source of Mathlib's complete lattice and
  `Sieve.generate` was read directly; no such topology was found.
* msearch grep: `[Aa]lteration|[Mm]aximally|[Cc]ompletely[Dd]ecomposed`:
  20 unrelated hits on words such as maximally; no alteration-site declaration.
* msearch leansearch: `prime-to-ell alteration Grothendieck topology maximally
  finite reduced schemes`: 8 hits on ordinary sites, spectra and quasi-finiteness;
  no matching prime-to-ell alteration site.
* rg over the upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no `PrimeToEllAlteration`,
  `IsMaximallyPrimeToEllFinite`, or `IsPrimeToEllDecomposedEtale` declarations.
  The required upstream grep for this item's blueprint id found no module.
  Broader alteration searches found `Paper.OrgogozoInductionData.IsAlteration`,
  which was read: it requires a proper surjection finite over a dense open and
  is not the category or the maximal prime-to-ell degree condition of this node.
  Existing uniformization statements likewise do not define this site.
* Direct Mathlib sieve-source search found `Sieve.ofArrows`,
  `Sieve.mem_ofArrows_iff` and `Sieve.generate`. These are reused.

Validation: `scompile.py Q75 def-per-prime-to-ell-alteration-topology` compiled
both the sandbox form and its actual library module cleanly after making `Alt`
an abbreviation, which allows Lean's existing full-subcategory instance to be
visible during typeclass search. No universe equalities were added. Every
variable and universe is explicit and `autoImplicit` is disabled. Final
compilation and server preflight are run by the delivery dry run as well.
There are no statement disputes or statement corrections.

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
