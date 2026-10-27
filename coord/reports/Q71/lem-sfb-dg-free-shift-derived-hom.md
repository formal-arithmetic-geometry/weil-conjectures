## Worker report

States `CategoryTheory.DgAlgebra.free_shift_derived_hom` in
`Sheaf.CategoryTheory.DgFreeShiftDerivedHom`. Its sole postponed proof is `sorry`.
The helpers `shiftedRegularUnit` and `shiftedRegularEvaluation` are explicit data:
they transport the monoid unit through the supplied shift comparison and evaluate
the underlying chain map there. They require no existence choice or postponed proof.

Source reading: Stacks dga.tex definition-shift, Tag 09K1
(lemma-hom-from-shift-free), and Tag 09KY(1) (lemma-hom-derived), with the
node's four-step proof plan. Read the current blueprint unit
sk-thm-sf-ctf-stability and its direct-images proof (3), the inherited source route.
The item statement is unchanged. The existing definition node
`def-sfb-dg-derived-category` was added to stmt_deps under the explicit permission
to cite landed nodes; no node or notion is introduced or corrected.

Hypotheses and clauses:

- The size convention is expressed by explicit `universe u`. Components are
  modules over `ULift.{u} ℤ`; the actual Gabriel--Zisman localization uses its
  larger morphism universe. No independently smaller universe limits modules.
- `A : Algebra.{u}` is the landed monoid in integer cochain complexes. It encodes
  an associative unital graded integer algebra, square-zero differential, and
  the signed Leibniz identity, without any commutativity restriction.
- `RightModule A` is the existing module-object definition in the reversed tensor
  category. Its morphisms are the action-preserving degree-zero chain maps.
  `underlying A` forgets only the action. Thus `M`, `N`, `f`, `g`, and `h` are
  precisely the right DG modules and DG module homomorphisms in the node.
- `Derived A` and `Q A` are the fixed localization and its canonical functor.
  `[DerivedStructure A]` supplies the standard additive triangulated structure
  on that localization, as in the dependency's recorded declaration; it is
  structural data, not a projectivity, boundedness, or flatness assumption.
- `k : ℤ`, `S : RightModule A`, and
  `s : ShiftComparison A k (regular A) S` name any presentation of A[k].
  The comparison identifies the underlying complex with the ordinary shift,
  including differential (-1)^k d, and its action equation is exactly the
  unchanged right action. This is the existing framework's way to name A[k],
  not an arbitrary DG module or a derived object substituted for it.
- `shiftedRegularUnit A k S s` transports 1 from degree zero of A through the
  canonical degree identification and `s.iso.inv` to degree -k in S. Its formula
  uses `MonObj.one`, evaluated on 1 in the degree-zero tensor unit.
- The first conjunct quantifies every M and derived morphism φ and gives
  `∃ f : S ⟶ M, (Q A).map f = φ`: the required DG representative.
- The second conjunct is the exact iff between equality of the two images and
  existence of `y` in degree -k-1 with `d y = f(1)-g(1)`. The reversed orientation
  of this equality has the same meaning as saying the difference is a boundary.
- The last conjunct gives a family of `≃+` equivalences from the derived Hom
  groups to `((underlying A).obj M).homology (-k)`. This is Mathlib's actual
  cohomology, not an uninterpreted or newly chosen quotient.
- The normalization clause says `homologyι (e M (Q.map f)) = pOpcycles (f(1))`.
  Here `homologyι` is the canonical injective map H^(-k)(M) into opcycles and
  `pOpcycles` is the quotient M^(-k) by the incoming boundaries. This specifies
  exactly the class [f(1)], while avoiding a proof-bearing cycle constructor
  inside the statement. The injectivity pins the class uniquely, and the
  representative conjunct pins the entire equivalence uniquely.
- The final clause is `e N (φ ≫ Q.map h) = homologyMap (underlying.map h) (-k)
  (e M φ)`. It states precisely the specified naturality on DG homomorphisms.
- There are no boundedness, countability, flatness, or commutativity binders.

Dependencies read and used:

- `def-weil-size-convention` has an existing convention record, with no Lean
  declaration or import; explicit universes implement that convention.
- `def-sfb-dg-derived-category`, module
  `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`: read the full docstrings and
  signatures of `Complex`, `Algebra`, `RightModule`, `underlying`, `regular`,
  `act`, `quasiIsomorphisms`, `Derived`, `Q`, `ShiftComparison`, `ConeComparison`,
  and `DerivedStructure`. Reused its actual constructions and public import.
- Mathlib `HomologicalComplex.homology`, `homologyι`, `pOpcycles`, and
  `homologyMap`, in `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  give the actual cohomology, its injection into opcycles, the quotient map,
  and the induced map. These are already public through the framework import.
- The proof dependency `lem-sfb-dg-homotopically-projective-hom-derived` has no
  recorded Lean declaration or mathlib_match in the read tree, so there is no
  module to import. Its proof use remains in the DAG and in the theorem docstring.
  No unavailable proof dependency is added as a hypothesis.

Edge checks, before writing and on the second pass: k=0 is ordinary evaluation;
k=1 places 1 in degree -1, and k=-1 in degree 1; the parity cancellation in the
proof remains valid for negative k and in characteristic 2. A=0 and M=0 give
trivial groups on both sides, and the boundary iff still holds. An ordinary
noncommutative ring concentrated in degree zero is included. Algebras with
nonzero differential and unbounded modules are retained by the monoid/module
encoding; no ordinary-module derived category is substituted. Rescaling a shift
comparison rescales its transported unit consistently in all clauses. Naturality
is simultaneous for the same equivalence family, not separate unrelated choices.

Searches for reuse (2026-10-24):

- msearch LeanFinder: "Morphisms from a shifted rank one free module over a
  differential graded algebra in the derived category compute cohomology".
  Eight hits, including projective/injective-resolution Ext equivalences and
  HomComplex cohomology-to-small-shifted-Hom. They concern complexes in an
  abelian category, not modules over a general DG algebra.
- msearch Loogle: `"DifferentialGraded", "Module"`: zero hits.
- msearch grep: `DGAlgebra|DGModule|DifferentialGraded|DgModule`: zero Mathlib hits.
- msearch LeanSearch: "Evaluation at the unit identifies derived morphisms from
  a shifted free differential graded module with cohomology". Eight hits,
  including `ModuleCat.free_ε_one`, `CochainComplex.shiftEval`, and
  DifferentialObject maps; none is this theorem for a general DG algebra.
- rg over lean/Sheaf and lean/WeilConjectures for DG algebra/module names,
  evaluation/regular-module Hom, and the three proposed declaration names:
  located the landed `DgAlgebraDerivedCategory` interface, but no statement
  computing this derived Hom. No name clash. Item-id search in
  lean/WeilConjectures returned no match.
- DAG search located `def-sfb-dg-derived-category` and the related
  `lem-sfb-dg-free-module-hom-cohomology`. The latter has no Lean record and
  states the shift-transposed isomorphism with target M[k]; it supplies no
  existing declaration for this item.

Validation: scompile.py compiled this file separately in sandbox and library
module mode, cleanly (32.1 seconds and 11.0 seconds). All variables and universes
are explicit, autoImplicit is false, and all lines have at most 100 characters.
No statement dispute or correction is needed.

## Second reading by Q71

A second pass by the same worker, with the node and final Lean file open;
no separate agent was started, as instructed. The maintainer's independent review
is still required. Checked every binder and all four conclusion blocks against
the node. The `ShiftComparison` action condition and the inverse direction of its
underlying isomorphism make `shiftedRegularUnit` the unit in the intended source,
not the unit of a different shift. Checked the degree identity 0=-k+k and the
incoming differential (-k-1) to (-k). Confirmed that the normalization takes place
in opcycles only after applying the injective canonical map from actual homology:
it therefore means [f(1)], and does not weaken the bijection to an arbitrary
additive equivalence. Representative surjectivity and the explicit boundary iff
are both retained. The last clause quantifies h and every derived φ for the same
family e. No missing or extra mathematical hypothesis was found. The first
compiler pass found a reversed equality argument in the degree identification
and one misplaced parenthesis; both were fixed, and both module-mode compiles
then passed. No mathematical statement was changed.
