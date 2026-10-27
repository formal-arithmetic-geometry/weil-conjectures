## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalizableGroupGeometricCriteria` states
`AlgebraicGeometry.diagonalizableGroup_geometric_criteria`. Its only theorem proof
is `sorry`. No construction is chosen from an undetermined existence statement.
No statement correction or new node is needed.

The node's construction is already implemented by the landed
`def-sfb-diagonalizable-group`: `AlgebraicGeometry.diagonalizableGroup` in
`Sheaf.AlgebraicGeometry.DiagonalizableGroup`. I read that entire module and its
`hopfSpec` and additive group algebra dependencies. It is precisely Spec k[M]
with multiplication e_m e_n = e_(m+n), coproduct e_m tensor e_m, counit 1,
and antipode e_(-m). I add that already-landed node to stmt_deps and reuse its
construction rather than introduce another definition. The additional map
`diagonalizableGroupMap` sends e_m to e_(alpha m) on coordinates.

Hypothesis and clause correspondence:

* The field k is `(k : Type u) [Field k]`. The additive abelian group M is
  `(M : Type u) [AddCommGroup M]`; finite generation is `[AddGroup.FG M]`.
  The common universe accommodates every pair by taking a common upper universe.
* The affine group scheme is `diagonalizableGroup k M`, a
  `Grp (Over (Spec (.of k)))`; its structure morphism is `.X.hom`.
  Its existing definition supplies the basis and all the specified Hopf operations.
* Finite type is the first conjunct:
  `LocallyOfFiniteType ... ∧ QuasiCompact ...`, exactly the recorded convention
  on def-weil-finite-type-morphism.
* r,s >= 0 are `(r s : ℕ)`. The orders are `(n : Fin s → ℕ)` and
  `[∀ i, NeZero (n i)]`, equivalent to n_i >= 1. The displayed decomposition
  is an actual `e : M ≃+ ((Fin r → ULift.{u} ℤ) ×
  (∀ i : Fin s, ULift.{u} (ZMod (n i))))`. Finite direct sums and these finite
  Cartesian powers are the same additive groups. ULift changes no additive
  group; it permits a character lattice in the field's universe.
* The product is the categorical binary product of the two categorical finite
  products `∏ᶜ` in `Grp (Over (Spec (.of k)))`. Its factors are
  `Grp.mk (StandardGroupSchemes.multiplicative k)` and
  `Grp.mk (StandardGroupSchemes.roots k (n i))`, using their recorded group laws.
  The existential isomorphism `a` gives the standard decomposition group and
  `b` gives D_k(M). The equality
  `b.hom = diagonalizableGroupMap k e.symm.toAddMonoidHom ≫ a.hom`
  explicitly makes b the isomorphism induced by e and the standard factor
  comparison. The variance is correct: e.symm goes from the standard character
  group to M, hence D(e.symm) goes from D(M) to its standard decomposition.
* The free case is separately included as
  `∀ r : ℕ, Nonempty (diagonalizableGroup k (Fin r → ULift.{u} ℤ) ≅ ...)`.
  No hidden cyclic factors or nonzero-rank assumption is imposed.
* Positive characteristic is `∀ (p : ℕ) [CharP k p], 0 < p → ...`.
  Smoothness is `Smooth ...`; no nonzero p-power-annihilated elements is
  `∀ (m : M) (a : ℕ), (p ^ a) • m = 0 → m = 0`.
* The positive-characteristic connectedness clause uses
  `GeometricallyConnected ... ↔ ∀ m : M,
  (∃ n : ℕ, 0 < n ∧ n • m = 0) → ∃ a : ℕ, (p ^ a) • m = 0`.
  Thus the premise is exactly finite order and the conclusion is p-primary
  torsion. No condition is put on infinite-order elements.
* Characteristic zero is `∀ [CharZero k], ...`; it asserts smoothness and
  `GeometricallyConnected ... ↔
  ∀ (m : M) (n : ℕ), 0 < n → n • m = 0 → m = 0`.
  Positive natural n is equivalent to the positive integer n in the node.
* `Mathlib.AlgebraicGeometry.Geometrically.Connected.GeometricallyConnected`
  (declaration namespace: `AlgebraicGeometry`) means connectedness of every
  pullback along a field-valued point. For the structure morphism to Spec k,
  the field-valued points are exactly field extensions, as expressed by
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`. Its
  `ConnectedSpace` includes nonemptiness, matching def-weil-connected-scheme.

Dependency interfaces read and used:

* def-weil-field: Mathlib's `Field`.
* def-sc-group-scheme: `CategoryTheory.GrpObj` and `CategoryTheory.Grp` in
  `Mathlib.CategoryTheory.Monoidal.Grp`; the categorical products preserve
  group structure, not merely the underlying schemes.
* def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in `.Morphisms.QuasiCompact`.
* def-sc-gm-ga: `StandardGroupSchemes.multiplicative`, `.multiplicativeGroup`,
  `.roots`, `.rootsAlgebra`, `.rootsGroup`, in
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`. These are the Laurent algebra
  and the polynomial quotient by (t^n-1), with the stated Hopf laws.
* def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `.Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`, already used by the recorded construction.
* def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
* def-weil-connected-scheme: `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, used through `GeometricallyConnected`.
* def-pc-field-extension: `Algebra` in `Mathlib.Algebra.Algebra.Defs` and
  `algebraMap`; the existing geometric predicate quantifies over these extensions.
* Added landed dependency def-sfb-diagonalizable-group: `diagonalizableGroup`
  and `diagonalizableGroupMap`, as above.

All already stated proof dependencies are imported, publicly when also used by
statements and otherwise by plain import. In particular these include the tensor
universal property, `pullbackSpecIso`, the finite abelian group structure theorem,
`AdjoinRoot.powerBasis'`, `FormallySmooth`, `LocallyOfFinitePresentation`,
`IsFirstOrderThickening`, `Smooth.geometricallyReduced`, the polynomial-domain
instance, `PrimeSpectrum.isHomeomorph_comap`,
`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`, irreducibility,
`AlgebraicClosure`, and `Ideal.quotientInfRingEquivPiQuotient`.
The declaration docstring follows all seven proof steps of the node, naming
these nodes and spelling out the constructions, square-zero lift, nilpotent
obstruction, nilpotent quotient and Chinese-remainder argument.

Edge cases checked against the statement and the source:

* M = 0, r = s = 0: the character groups are trivial, the categorical products
  are terminal group schemes, and D(0) = Spec k is smooth and geometrically
  connected. The theorem excludes neither empty product.
* n_i = 1: NeZero permits it; ZMod 1 is zero and mu_1 is the trivial group.
* Characteristic p and M = Z/p: the smoothness right side is false, while the
  connectedness right side is true. For prime-to-p nontrivial finite torsion,
  these truth values reverse. These detect accidental reversal of the criteria.
* M = Z^r: there is no nonzero torsion, so smoothness and geometric
  connectedness hold in every characteristic, including rank zero.
* Characteristic zero with nonzero finite torsion: smoothness is unconditional,
  while geometric connectedness fails.
* a = 0 is allowed in p^a: 1 • m = 0 forces m = 0 and permits the zero torsion
  element without requiring a positive exponent.
* n = 0 is excluded only in the definition of finite order and torsion-free,
  exactly as the node requires. Characteristic p = 0 is excluded only from
  the positive-characteristic clause; the separate CharZero clause covers it.
* No algebraic closedness, perfection, reducedness or nonempty-index hypothesis
  is imposed. The geometric predicate tests all field extensions.

Source checked directly using pdftotext on
`literature/milne-algebraic-groups_iAG2017.pdf`: Section 12(b), Examples
12.1--12.2, Proposition 12.3, Remark 12.5 and Theorem 12.9(a), printed
pp.231--234. Remark 12.5 uses the characteristic exponent. The node's more
explicit geometric wording follows the same presentation after every scalar
extension, as its proof explains. No source discrepancy or STATEMENT-DISPUTED
issue was found.

Searches actually run:

* msearch.py leanfinder: "For a finitely generated abelian group M, Spec k[M]
  decomposes as a product of multiplicative groups and roots of unity and is
  smooth and geometrically connected according to characteristic torsion".
  Eight hits: Spec of a field, terminal Spec Z, affine space, number-field
  units and general smooth-algebra results; none states this theorem.
* msearch.py loogle: "AddMonoidAlgebra, AlgebraicGeometry.Smooth,
  AlgebraicGeometry.diagonalizableGroup". Zero hits, with unknown identifier
  for the project-specific diagonalizableGroup. This is not evidence that
  the project declaration is absent; its source was separately found and read.
* msearch.py grep: "diagonalizableGroup|AddMonoidAlgebra.*Smooth|
  [Gg]eometrically[Cc]onnected" in AlgebraicGeometry: five hits, all for
  Mathlib's geometric connectedness predicate and its definition.
* rg in lean/Sheaf/AlgebraicGeometry and lean/WeilConjectures/AlgebraicGeometry
  for diagonalizable/Diagonalizable/groupAlgebra/GroupScheme/rootsOfUnity and
  multiplicativeGroup found the existing DiagonalizableGroup and
  StandardGroupSchemes constructions and consumers, with no copy of this
  product-and-geometric-criteria theorem. Searching the item id in
  lean/WeilConjectures returned no match. Searching dag/lean_names_upstream.json
  also produced no theorem match.
* Read the recorded nodes and signatures for every statement dependency, and
  their defining modules. No dependency interface repair was necessary.

Validation: the module compiled on the server through scompile.py; the final
version is also checked by the required deliver2.py dry run. No other compiler,
global build, repository write or direct Git command was used.

## Second reading by Q12

I reread the node and the final Lean signature clause by clause. This is a
self-audit; the dispatcher's instruction forbids starting another agent, and
the maintainer performs the independent review of the delivered statement.
The audit checked that the theorem quantifies over a supplied decomposition,
that all roots factors carry their actual group structures, that the isomorphism
for M is induced in the correct contravariant direction, and that both the
free special case and each of the two positive-characteristic and two
characteristic-zero conclusions are present. It also checked the zero group,
empty products, n_i = 1, a = 0, and unrestricted infinite-order elements.
The universe lifts prevent the lattice and cyclic factors from forcing u = 0.
No mathematical mismatch was found; the final import pass added the recorded
formal-smoothness, thickening, finite-presentation and polynomial-domain proof
interfaces. Only the node's lean record and the addition of the already-landed
canonical-construction dependency are changed.
