## Worker report

Item: lem-sfb-polarized-abelian-automorphisms-finite. The new module
`Sheaf.AlgebraicGeometry.AbelianVariety.PolarizedAutomorphismsFinite` states
`AlgebraicGeometry.polarized_abelian_automorphisms_finite`, with one named theorem
and its proof `sorry`. All definitions used are existing declarations. The natural-language
statement, proof plan and source are unchanged.

Clause-by-clause correspondence:

- An algebraically closed field k is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The abelian variety A/k is `A : Over (Spec (.of k))` with `[GrpObj A]`
  and `[IsAbelianVariety A]`. These are the recorded group-scheme and
  abelian-variety interfaces: proper, smooth and connected.
- The dual representing rigidified algebraically trivial invertible sheaves is the
  supplied `D : AbelianDualPoincareDatum A`, with underlying abelian variety `D.dual`.
  Its universal property covers arbitrary parameter schemes and rigidifications;
  its tensorGroupLaw is the group law of the represented Picard identity component.
  The datum is supplied, never chosen from an unproved existence theorem.
- The invertible sheaf is `L : A.left.Modules` with
  `[Scheme.Modules.IsInvertible L]`; ampleness is `hL : IsAmple A.hom L`.
  The invertibility instance spells out the node's line-bundle hypothesis; it is
  already implied by ampleness, so adds no restriction.
- The given polarization is `lambda : A ⟶ D.dual` with
  `hlambda : ClassifiesAbelianDifference D L lambda`. This identifies its classifying
  family with the existing `abelianNormalizedDifference A L`, namely
  m*L tensor p1*(L-dual) tensor p2*(L-dual) tensor c*(0*L).
  On each fibre it is exactly `[t_x*L tensor L^-1]`, with the constant identity-line
  factor needed for rigidification. No principal-polarization assumption is made.
  The classifying morphism is a homomorphism by the existing polarization calculus;
  that property is not an additional hypothesis.
- The automorphism a is an element of `A ≅ A`, hence an isomorphism over k.
  The subtype condition `IsMonHom a.hom` restricts to k-group automorphisms.
  An inverse of an invertible group homomorphism is automatically a homomorphism;
  separate inverse data would not change this subtype.
- The dual a-dual is the map quantified by `∃ aDual : D.dual ⟶ D.dual` with
  `ClassifiesAbelianDualHom D D a.hom aDual`. This existing predicate asserts an
  isomorphism of Poincare pullbacks respecting the specified rigidification. Thus
  it defines pullback on Pic^0, not an arbitrary self-map of the dual. Universality
  makes it unique; the displayed existential is a proposition, so it does not
  create multiple elements for different witnesses or proofs.
- The preservation equation is `a.hom ≫ lambda ≫ aDual = lambda`, which in usual
  right-to-left notation is exactly a-dual lambda a=lambda.
- The conclusion `Finite {a : A ≅ A // ...}` is finiteness of precisely the set
  underlying Aut_k(A,lambda). A separate bundled group structure is unnecessary
  for the finiteness assertion. We do not merely assert finite-order elements or
  finiteness of the smaller group fixing the particular isomorphism class of L.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed
  part of def-weil-algebraic-closure, not a newly chosen extension).
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the associated
  homomorphism predicate is `CategoryTheory.IsMonHom` in Monoidal.Mon.
  The specialization to schemes over k is documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`:
  `AlgebraicGeometry.IsAmple`.
- `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`:
  `AbelianDualPoincareDatum`, `abelianNormalizedDifference`,
  `ClassifiesAbelianDifference`. Its landed node
  def-sfb-abelian-dual-poincare-datum is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AbelianVariety.PoincareBiduality`:
  `ClassifiesAbelianDualHom`. Its definition owner
  def-sfb-abelian-dual-hom-classification is added to stmt_deps. This is a plain
  definition in that module, without assuming the biduality theorem. The full
  predicate includes the rigidification equation, not just an unnormalized
  line-bundle isomorphism. Neither added dependency has a path back to the item.
- Proof-only import:
  `Sheaf.AlgebraicGeometry.AbelianVariety.HomFiniteFree`, declaring
  `AlgebraicGeometry.abelianVariety_hom_finite_free`. The other two proof nodes,
  lem-sfb-rosati-trace-positive and lem-sfb-positive-form-lattice-sublevels-finite,
  have no lean records, so there are no recorded modules to import for them.
  All four proof steps, including these named inputs, appear in the theorem docstring.

Edge cases checked before writing:

- The zero-dimensional abelian variety is admitted; its automorphism group is
  trivial and the finite-basis argument allows rank zero.
- Every characteristic is admitted, including inseparable polarization isogenies.
  No prime, invertibility-of-degree condition or characteristic exclusion appears.
- Nonprincipal ample polarizations are admitted: no inverse in integral Hom is
  requested. The proof plan inverts lambda only in rational Hom.
- The empty scheme is not an abelian variety (connectedness and the identity
  section exclude it), so no empty-scheme case is inadvertently asserted.
- Translations by nonzero points are excluded by IsMonHom. This is necessary:
  preserving a polarization is meant for group automorphisms here.
- Without ampleness the zero polarization on a product can have an infinite
  stabilizer. The ample hypothesis is therefore essential and retained.
- The chosen L is a representative for lambda. Preserving lambda need not mean
  a*L is isomorphic to L; the theorem uses the former, larger stabilizer.

Searches made on 2026-10-24:

- msearch.py leanfinder: "The group of automorphisms of an abelian variety preserving
  an ample polarization is finite". Eight hits, including the finite-Aut instance
  for connected Galois-category objects and AlgEquiv.fintype; none is this theorem.
- msearch.py loogle: `"IsAbelianVariety", "Finite"`. Zero hits.
- msearch.py grep: `polariz.*[Aa]ut|[Aa]ut.*polariz|[Aa]belian[Vv]ariety`.
  Zero Mathlib hits.
- msearch.py leansearch: "The automorphism group of a polarized abelian variety
  is finite". Eight hits on Galois-category, finite-type and field automorphisms;
  no match for the requested stabilizer.
- rg on lean/WeilConjectures and lean/Sheaf for polarization automorphisms and the
  item id: no existing finiteness theorem. PolarizedOddLevelRigidity is a downstream
  rigidity theorem, not the finiteness result, and cannot be imported here.
- Searches for dual abelian varieties, Poincare data and classification predicates
  found the landed DualPoincareDatum, RationalDualityData and PoincareBiduality
  modules. The exact rigidified ClassifiesAbelianDualHom interface was reused.
- Proposed declaration name checked in Mathlib, WeilConjectures and
  dag/lean_names_upstream.json: no duplicate.

Read Milne AV I Proposition 14.4(a), printed p.62, from the local PDF, and the
polarization and duality conventions in the recorded interfaces. The DAG already
repairs the source's false claim that the entire real endomorphism space is compact:
only the positive-form sublevel is compact. No new node fault or
STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled both its sandbox probe and the module under its
actual library name cleanly (3.5 s and 2.1 s); no errors or warnings were emitted.
All universes and variables are explicit, with both auto-implicit options disabled.

## Second reading by NW

I made a separate manual rereading of the node and final module; no additional
agent was started. The maintainer supplies the independent review required by
this dispatch. The field, algebraic closedness, proper/smooth/connected group
scheme, ample invertible L, represented dual, normalized difference formula,
group-automorphism condition, dual pullback action, preservation equation and
finite conclusion correspond exactly as listed above. In particular the dual
witness is constrained by the full rigidified Poincare predicate, and the type
being counted retains only a, so no choices of representatives are being counted.
The composition order was checked against the domains and codomains. The
zero-dimensional, arbitrary-characteristic and nonprincipal cases remain included.
No mismatch was found and no statement correction was made. The repaired record adds the definition owner described below and cites the landed
normalized dual datum. No dependency module is needed.

## New nodes

def-sfb-abelian-dual-hom-classification records the existing plain definitions
`AlgebraicGeometry.ClassifiesAbelianDualHom` and
`AlgebraicGeometry.poincareRigidificationBaseChange` in the published module
`Sheaf.AlgebraicGeometry.AbelianVariety.PoincareBiduality`. The first is exactly the
rigidified pullback predicate in Milne AV I Section 9, p.41. Its equality of identity
axes supplies the square used by the second, a canonical composition of pullback
comparison isomorphisms. The existential isomorphism must commute with the supplied
rigidifications, precisely as in the existing signature and body. The node states
only these definitions, not existence, uniqueness, biduality or any choice from a
theorem. It retains arbitrary maps f as in the actual predicate; for the item f is
a group automorphism, so the identity-axis square is satisfied. No declaration is
moved, copied or added. The existing module and both definitions remain unchanged.

Fresh searches: LeanSearch and LeanFinder for “Dual homomorphism of abelian varieties
classified by rigidified Poincare pullback” return eight unrelated linear-dual,
character-module and lattice-dual results each. Mathlib grep
`ClassifiesAbelianDualHom|poincareRigidificationBaseChange|Poincare` in AlgebraicGeometry
returns zero hits. Searches of WeilConjectures find neither definition; Sheaf finds
both exact definitions at lines 44 and 127. DAG search finds no separate definition
owner; blueprint_refs search “dual hom classification” returns zero matches. These
searches, including the returned names, are recorded in the new node.

## Repair of immutable head 01b666ae132f

H2 is repaired: replaced lem-sfb-abelian-poincare-biduality in the item's stmt_deps
by the new definition node def-sfb-abelian-dual-hom-classification. The definition
node has existing:true and names exactly the two plain declarations requested by
the maintainer. There is no modification to the biduality node or module. No
statement_change is needed: the natural-language statement and Lean statement are
identical to the returned delivery. The retained Lean file SHA256 before and after
repair is c4f4eddeaebe4a6e6fbbe14c80188c074dc72978a77d27e78604bae31d28bbf1.

Compared the retained item to current read-only main: before repair only lean and
stmt_deps differed, matching the returned packet; all other fields are retained.
The delivery wrapper rebases the repaired packet on current main. In the separate
repair rereading, the new node's parameters k, A, B, D_A, D_B, f and g match the
existing ClassifiesAbelianDualHom signature. Its axis equality, existential line
isomorphism and compatibility equation match that definition's body; the canonical
base-change comparison matches poincareRigidificationBaseChange. The item's Lean
remains byte-identical as required. This resolves the sole numbered return point.
