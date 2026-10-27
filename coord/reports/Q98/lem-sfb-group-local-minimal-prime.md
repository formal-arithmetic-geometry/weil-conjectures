## Worker report

The module `Sheaf.AlgebraicGeometry.GroupLocalMinimalPrime` states
`AlgebraicGeometry.GrpObj.localMinimalPrimes_neutralComponent`, with its whole proof
`sorry`. It introduces no definition. The node is unchanged except for `lean`.
The source was read locally: `literature/stacks-project/groupoids.tex`, Tag 047M,
label `lemma-group-scheme-field-geometrically-irreducible`, statement and entire proof.
It has precisely the three conclusions formalized here.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`, using the `Field` mathlib_match of
  def-weil-field. The universe is explicitly declared and autoImplicit is false.
- A group scheme over k is `(G : Over (Spec (.of k))) [CategoryTheory.GrpObj G]`.
  This is exactly the recorded interpretation of def-sc-group-scheme; G.left is
  its scheme and G.hom its structure morphism. No commutativity, finite type,
  quasi-compactness, separatedness or reducedness hypothesis is imposed.
- The identity point e is `AlgebraicGeometry.GrpObj.onePoint G`, whose definition
  in the upstream group-scheme module evaluates the unit section on the unique
  point of Spec k. It does not select an arbitrary point.
- For every g in G, `∀ g : G.left` quantifies over every topological point,
  including non-rational and nonclosed points. Its local ring is the actual
  structure-sheaf stalk `G.left.presheaf.stalk g`.
- A unique minimal prime ideal is `∃! p : Ideal (G.left.presheaf.stalk g),
  p ∈ minimalPrimes (G.left.presheaf.stalk g)`. Mathlib's minimalPrimes is the set
  of primes minimal over the zero ideal, equivalently minimal among all primes,
  not the primes minimal over an additional ideal.
- The component Z is existentially quantified as `TopologicalSpace.Closeds G.left`.
  `(Z : Set G.left) ∈ irreducibleComponents G.left` asserts maximal irreducibility.
  Bundling it as closed adds no restriction: every irreducible component is closed
  by `isClosed_of_mem_irreducibleComponents`.
- Passing through e is `GrpObj.onePoint G ∈ (Z : Set G.left)`.
- Uniqueness is a separate clause quantifying over *all* subsets Z' which are
  components and contain e, concluding `Z' = (Z : Set G.left)`. It is not merely
  uniqueness among geometrically irreducible components.
- Its reduced induced closed scheme is the pre-existing canonical construction
  `(Scheme.IdealSheafData.vanishingIdeal Z).subscheme`, with canonical inclusion
  `(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι`. This is the quotient by
  the radical vanishing ideal, not an arbitrary closed immersion or a choice
  from an unproved existence theorem. Geometric irreducibility over k is
  `GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ G.hom)`.
  The construction's support, reducedness and uniqueness are exactly those in
  the already recorded reduced-induced-closed-subscheme theorem.

Recorded dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs (available transitively).
- def-sc-group-scheme: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp. The existing interpretation on schemes
  over Spec k is documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
  `AlgebraicGeometry.GrpObj.onePoint` is read from and publicly imported through
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic.
- def-weil-irreducible-components: `irreducibleComponents`,
  Mathlib.Topology.Irreducible, exactly the maximal irreducible subsets.
- def-pc-reduced-scheme: `AlgebraicGeometry.IsReduced`,
  Mathlib.AlgebraicGeometry.Properties. This is section-wise reducedness,
  equivalent to stalk-wise reducedness by the adjoining declarations.
- def-pc-geometrically-irreducible: `AlgebraicGeometry.GeometricallyIrreducible`,
  imported through its recorded Mathlib.AlgebraicGeometry.Geometrically.Integral.
  Its definition in Geometrically/Irreducible.lean tests all field-valued base
  changes, specializing here to field extensions of k.
- The canonical reduced component uses `Scheme.IdealSheafData.vanishingIdeal`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic, and `.subscheme` / `.subschemeι`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme. Their full definitions and
  docstrings were read. The proof dependency
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme, characterizes
  the reduced closed structure and its uniqueness over the ambient scheme.

All recorded statement-dependency modules are publicly imported. Modules of
recorded proof declarations (including Mathlib matches) are imported privately,
except those already public for the statement. The proof-only prerequisite
lem-sfb-field-extension-irreducible-components currently has no Lean record,
Mathlib match or closed upstream declaration; it is not needed to type this
statement, and no nonexistent import or replacement theorem was added. Its use
remains explicit in the seven-step proof docstring. All other proof modules are
imported. No dependency repair, new node or statement correction was necessary.

Edge cases checked mathematically before writing:

- The trivial group Spec k has just one stalk minimal prime and its whole space
  is the neutral geometrically irreducible reduced component.
- Nonreduced groups such as alpha_p in characteristic p are allowed: the stalk
  need not be a domain, and the reduced component (not the original component
  with its nilpotents) is the object tested for geometric irreducibility.
- A disconnected constant finite group is allowed: only the component through
  the identity is claimed geometrically irreducible; no irreducibility of G is
  asserted.
- mu_3 over Q can have non-geometrically-irreducible nonneutral components;
  the statement correctly singles out the neutral component.
- Infinite or non-quasi-compact group schemes are not excluded. There are no
  Noetherian, finite-type, connectedness or characteristic restrictions.
- The empty scheme cannot be a group scheme over a field because a unit section
  would give a point. No extra Nonempty hypothesis is needed.
- Minimal-prime existence is included by `∃!`, not only a subsingleton assertion.
  All points, rather than only k-rational points, are covered.

Searches (all performed with the prescribed msearch wrapper or read-only rg):

- leanfinder, query "A group scheme over a field has a unique minimal prime in
  every local ring and a unique geometrically irreducible component containing
  the identity": eight hits, including IsReduced, integral-scheme
  irreducibility and singleton field spectra; no group-scheme theorem.
- leansearch, query "Every local ring of a group scheme over a field has a
  unique minimal prime ideal": eight hits, including minimalPrimes,
  Ideal.minimalPrimes, localization and domain specializations; none is the
  claimed group-scheme result.
- loogle, query "GrpObj, minimalPrimes, GeometricallyIrreducible": zero hits
  (the service reported unknown unqualified GrpObj). Repeated with qualified
  "CategoryTheory.GrpObj": twelve structural group-object declarations,
  none expressing the geometric theorem.
- msearch grep, pattern
  `GrpObj.*minimal|group.*minimal.*prime|geometricallyIrreducible.*[Gg]roup`:
  zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and neutral
  irreducible-component / unique-minimal-prime variants found only the
  downstream modules' proof-docstring references, general local algebra and
  field tensor results, not an existing statement of Tag 047M.
- Read the group-scheme Basic module's identity-component results: they have
  finite-type hypotheses and different conclusions, hence are not this theorem.
- Read the canonical vanishingIdeal and subscheme definitions instead of
  introducing a second reduced closed subscheme construction.

Validation: the prescribed scompile.py compiled both its sandbox module and the
actual library module successfully (16.7 s and 7.1 s), with no diagnostics.
There is no STATEMENT-DISPUTED flag or node fault.

## Second reading by Q98

A separate in-thread rereading compared the completed module against the node
and Stacks 047M. No additional agent was started, as the dispatcher brief
explicitly prohibits that; the maintainer's independent review remains separate.
The conjunction starts with existence *and* uniqueness at every stalk. The
component existential includes membership and identity containment, followed by
uniqueness against all components through the identity, independently of the
last geometric clause. The final structure morphism is the canonical reduced
closed component inclusion followed by G.hom, so it is over the original k.
The bundled closed subset is equivalent to the node's subset because components
are closed. No extra finite-type or reducedness instance on G occurs. All
variables and the universe are bound; no local notation, private construction,
let binder, arbitrary map or hollow definition occurs. No mismatch was found.
