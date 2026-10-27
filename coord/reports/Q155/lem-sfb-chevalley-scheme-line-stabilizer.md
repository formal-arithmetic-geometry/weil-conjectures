## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ChevalleyLineStabilizer` states
`AlgebraicGeometry.exists_rational_line_stabilizer`, with its whole proof postponed by
`sorry`. No definitions are added and no mathematical claims are proved. The statement
and its seven-step proof docstring follow Milne, Algebraic Groups (2017), Theorem 4.27,
Lemma 4.28, printed pp.94--95, and Remark 4.30, printed p.96. I read the actual PDF pages
106--108, as well as the chapter's standing affine algebraic group convention on p.83.

Hypothesis and clause comparison:

- A field k is `{k : Type u} [Field k]`.
- The k-scheme G is `(G : Scheme.{u}) [G.Over (Spec (.of k))]`.
- The group scheme structure is `[GrpObj (G.asOver (Spec (.of k)))]`.
- Affineness is `[IsAffine G]`.
- Finite type is the conjunction of the two class binders
  `[LocallyOfFiniteType (G ↘ Spec (.of k))] [QuasiCompact (G ↘ Spec (.of k))]`.
- A closed subgroup H is `(H : Over (Spec (.of k))) [GrpObj H]`, with its inclusion
  `(i : H ⟶ G.asOver (Spec (.of k))) [IsClosedSubgroupScheme i]`. The recorded
  definition includes `IsMonHom i`, injectivity on all algebra-valued points, and
  `IsClosedImmersion i.left`.
- The conclusion supplies an actual vector space E: `∃ (E : Type u)
  (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)`.
  `Nontrivial E` states that it is nonzero.
- A rational representation is the actual scheme morphism
  `ρ : GeneralLinearGroup.RationalHom (G.asOver (Spec (.of k)))
  (RationalRepresentation.FiniteIndex (k := k) E)`, together with `IsMonHom ρ`.
  Its target is the existing GL scheme in a fixed genuine finite basis of E;
  this records exactly the node's permitted basis choice.
- A line is `(D : Submodule k E)` with `Module.finrank k D = 1`.
  Finite-dimensionality of D follows from its being a subspace of E.
- Every commutative k-algebra is quantified by
  `∀ (A : Type u) [CommRing A] [Algebra k A]`.
- The subset H(A) of G(A) is `Set.range (fun h : points H A ↦ h ≫ i)`.
  This retains the given inclusion, rather than an arbitrary subgroup of abstract points.
- The node's scalar-extended line is `D.baseChange A`, the range of the canonical
  base-changed inclusion, in `A ⊗[k] E`. Mathlib and the recorded module-base-change node
  use A tensor E; `TensorProduct.comm` identifies this with the node's E tensor A.
- The A-linear automorphism attached to g is obtained from `g ≫ ρ` by the recorded
  `GeneralLinearGroup.homMulEquiv`, then `Matrix.GeneralLinearGroup.toLin'` in
  `(RationalRepresentation.finiteBasis (k := k) E).baseChange A`.
  `Submodule.map` by its underlying linear map is exactly the image of the extended line.
  The equality `Submodule.map ... (D.baseChange A) = D.baseChange A` asks for preservation
  with equality, not merely containment or fixation of an arbitrarily selected vector.
- The displayed set equality is quantified over every A with the same E, ρ and D.
  Naturality is built into these canonical constructions: the left side is the image of
  the fixed scheme inclusion on points, and on the right `g ≫ ρ` is a fixed scheme map.
  `GeneralLinearGroup.homMulEquiv_specMap_comp` identifies changes of test algebra with
  entrywise matrix change. The base-changed basis and D have the usual tensor functor maps.
  Thus this is equality of the indicated subfunctors, rather than unrelated pointwise
  representations. No independent choice of an action for each algebra is present.
- There is no smoothness, reducedness, perfectness, algebraic-closedness or characteristic
  binder anywhere.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; homomorphisms use
  `CategoryTheory.IsMonHom` from `Mathlib.CategoryTheory.Monoidal.Mon`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (and its `IsSubgroupScheme` parent).
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, the recorded general-linear node module,
  publicly imports the existing GL construction, without defining it again:
  `AlgebraicGeometry.GeneralLinearGroup` and `...homMulEquiv`, from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional` is `Module.Finite`.
- `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`:
  `AlgebraicGeometry.RationalRepresentation.FiniteIndex` and `...finiteBasis`, and its
  `finite_dictionary` for the proof route. I read the whole module, including its natural
  representation, generic coaction and finite-dimensional dictionary signatures/docstrings.
  The new definition node `def-sfb-rational-representation-finite-basis` records these
  two already-existing helpers and is the statement dependency. The dictionary theorem
  stays in proof_deps only. No dependency record is repaired.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`:
  `GeneralLinearGroup.RationalHom` (an actual Over morphism).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring`: `points`, `points.map`.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`:
  `Matrix.GeneralLinearGroup.toLin'`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `Submodule.baseChange`, whose data are
  `LinearMap.range (p.subtype.baseChange A)`.

Plain proof imports preserve all stated dependencies: the closed-immersion definition
through the public subgroup module; `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`
(`affine_finiteType_algebra_of_field`); `Mathlib.RingTheory.FiniteType`
(`Algebra.FiniteType.isNoetherianRing`); `Mathlib.RingTheory.Noetherian.Defs`
(`IsNoetherianRing`); `Mathlib.AlgebraicGeometry.Group.Affine` (the recorded coordinate
Hopf instance); `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` (`ExteriorAlgebra`);
`Mathlib.LinearAlgebra.ExteriorPower.Basis` (`Module.Basis.exteriorPower`,
`exteriorPower.finrank_eq`, and its imported zero/one-degree equivalences). Module base
change and the comodule dictionary are public imports because the signature uses them.
`lem-sfb-coalgebra-finite-subcoalgebra` has neither a Lean record nor a Mathlib match, so
there is no module to import for that proof-only node; it is named in the proof docstring.
The statement does not need a coalgebra construction. The new finite-basis definition
node records existing data only.

Edge cases checked before writing and on the resulting signature:

- H=G: the trivial action on E=k and D=E works. Thus no improper-subgroup exclusion occurs;
  the proof's exterior degree zero is included (w=1).
- H the identity subgroup: no nontriviality of H is required.
- G or H nonreduced, e.g. alpha_p in G_a: arbitrary characteristic and arbitrary algebras
  include dual numbers, so infinitesimal stabilizer information is retained.
- The zero vector space is excluded exactly by `Nontrivial E`; a one-dimensional E with
  D=E is permitted. Rank one on D is literal, with no nonzero-vector surrogate.
- The zero test ring is allowed; `CommRing A` has no `Nontrivial A` constraint. Its tensor
  space and line are zero and its point groups are singletons, consistently.
- No strict containment D<E is assumed. Exterior degrees d=n and d=0 both work in the
  proof docstring.
- The base field, schemes, vector space and test algebras share universe u, as in the
  recorded group-scheme and rational-representation interfaces. There is no independent
  smaller test-algebra universe that could make the hypothesis vacuous. Finite vector
  spaces may be chosen in this universe; the finite index is explicitly ULift (Fin n).

Searches actually run:

1. msearch.py leanfinder: `Chevalley closed subgroup scheme line stabilizer finite
   dimensional rational representation`. Eight hits concerned finite-dimensional fixed
   fields, Galois fixing subgroups and abstract actions. None was this theorem.
2. msearch.py loogle: `"stabilizer", "Submodule"`. Four hits were
   `Submodule.stabilizer_coe`, `Submodule.mem_stabilizer_submodule_iff_map_eq`,
   `LinearEquiv.mem_stabilizer_fixedSubmodule`, and
   `LinearEquiv.mem_stabilizer_submodule_of_le_fixedSubmodule`. None supplies a
   rational representation or the scheme-theoretic existence result.
3. msearch.py grep: `Chevalley|line.*stabilizer|stabilizer.*line`, subdirectory
   `AlgebraicGeometry`. Four hits concerned constructible-image Chevalley theorems.
4. rg of both project source roots for
   `Chevalley|lineStabilizer|line_stabilizer|rationalRepresentation` found other Chevalley
   results and rational representation material, but no declaration of the assigned
   theorem. A separate rg for the exact node id in WeilConjectures found no occurrence.
5. File/name searches located and I read the general-linear scheme, matrix/basis action,
   rational representation and comodule dictionary, so those existing notions are reused.

No statement correction, disputed statement, or dependency repair. The item changes
only in `lean` and the addition of `def-sfb-rational-representation-finite-basis` in
`stmt_deps`. The dictionary theorem remains in `proof_deps`. There is one named
postponed theorem matching the assigned DAG node; the new definition node records
existing declarations and introduces no Lean source.

Validation: scompile.py compiled this single file in sandbox and library contexts against
the published server build, with no errors or unexpected warnings (3.3 s and 3.0 s).

## Second reading by Q155

I re-opened the node and compared its clauses to the final Lean signature as a second
pass; the dispatch brief prohibits starting another agent, and the maintainer provides
an independent delivery review. The source's affine finite-type hypotheses are both
present, and the closed subgroup is the actual Over inclusion with the recorded class.
The existential has finite-dimensional nonzero E, an actual group-scheme homomorphism,
and D of dimension exactly one. The comparison of the two sets uses every commutative
k-algebra and equality of the image submodule, preserving the distinction between line
stabilizer and vector stabilizer. In particular it neither drops nilpotent algebras nor
replaces scheme-theoretic stabilization by k-point stabilization. Naturality follows from
the fixed morphisms and the fixed tensor/basis constructions. No mismatch or statement
change was needed. The repair pass checked that the two plain basis helpers now have definition-node
ownership, with the theorem node cited only in proof_deps. Both declarations are
recorded as existing and remain in their original module.


## New nodes

`def-sfb-rational-representation-finite-basis` records the existing definitions
`AlgebraicGeometry.RationalRepresentation.FiniteIndex` and
`AlgebraicGeometry.RationalRepresentation.finiteBasis` in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`, with `existing: true`.
It describes a field k, a finite-dimensional vector space V, the lifted finite index
ULift (Fin (finrank k V)), and the standard finite basis reindexed along the inverse
lift equivalence. Its only statement dependencies are the field and finite-dimensional
vector-space definitions. There is no group G hypothesis in either definition's actual
signature. The zero space gives the empty basis; dimension one gives a singleton index.
The actual body is finBasis.reindex, not data chosen from an unproved theorem.

Source: Milne, Algebraic Groups (2017), Chapter 4(a), printed p.83, for GL(V) of a
finite-dimensional representation; the fixed lifted basis is the existing project's
implementation convention. The source PDF page 95 and both defining signatures and
bodies were read again, including the live server source via scompile.py --source.
The declaration record's main signature is verbatim from the source, from `def` to `:=`.
No declarations were moved or copied, and no new Lean module was written.

New-node searches were actually run and their exact logged results are in its
mathlib_searches: LeanSearch `finite dimensional vector space finite basis indexed by
dimension` found Module.finBasis among eight hits; Loogle `Module.finBasis` found the
same definition and two unrelated root lemmas; Mathlib grep
`def finBasis|def finiteBasis|abbrev FiniteIndex` in LinearAlgebra found finBasis and
finBasisOfFinrankEq in Dimension.Free. Project grep found the exact two helpers only
in the dictionary module, and DAG grep found only their theorem-node declaration list,
with no definition owner. Blueprint search `finite basis` gave two unrelated coefficient
and Cech nodes; ancestor returns the inherited null ancestor. The new node uses that
ancestor and the item's via chain with the item prepended.

## Repair of returned delivery dc81fdb6821d

H2: the former stmt_deps addition was the theorem node
`lem-sfb-rational-representation-comodule-dictionary`, but the statement only uses the
plain definitions FiniteIndex and finiteBasis in its module. They do not depend on
choosing data from that theorem. Added the requested existing definition node and
replaced that addition by `def-sfb-rational-representation-finite-basis`. The dictionary
is still a proof dependency. The Lean file and its recorded signature are unchanged
from the returned delivery. Comparing the retained delivery with the current read clone
showed only the expected lean and stmt_deps changes on the item, so no independent
main-branch changes were overwritten. The delivery wrapper rebases against current main.

Second repair reading: checked the new node clause by clause against FiniteIndex and
finiteBasis: the field and finite-dimensional V are the same binders; I(V) is precisely
the lifted Fin n; the basis is precisely finBasis reindexed by Equiv.ulift.symm; V=0 is
included. Confirmed existing:true, the original module and both declaration names, no
new Lean file, definition-only stmt_deps on the new node, and the dictionary theorem
retained only in the item's proof_deps. This repairs the single return point without
changing the mathematical statement previously accepted by the independent reviewer.

Repair validation: the unchanged theorem module compiled cleanly again via scompile.py.
The first dry run requested the current new-node schema key `import_flags`; supplied
an empty list because this is a new definition record, with no imported-text flags.
