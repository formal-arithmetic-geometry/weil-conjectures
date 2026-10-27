## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismBorelRigidity states
AlgebraicGeometry.hom_ext_of_borel, with a single `sorry` and no definitions or proved
results. Source checked directly: Milne, Algebraic Groups (2017), Proposition 17.21,
printed p.358, the first paragraph of the proof (R = k). The five proof steps of the
DAG are reproduced in the theorem docstring, including the reduced-orbit argument,
fpqc descent, scheme-level constancy and cancellation in a possibly noncommutative target.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The three schemes over F are `(A D B : Over (Spec (.of F)))`; group structures
  are `[GrpObj A] [GrpObj D] [GrpObj B]`.
- Smoothness of A and D is `[Smooth A.hom]` and `[Smooth D.hom]`.
- Connectedness is `[ConnectedSpace A.left]` and `[ConnectedSpace D.left]`;
  this includes nonemptiness, precisely as def-weil-connected-scheme requires.
- Affineness is `[IsAffine A.left]` and `[IsAffine D.left]`.
- Finite type is `[LocallyOfFiniteType A.hom] [QuasiCompact A.hom]` and the
  corresponding pair for D, exactly the recorded finite-type convention.
- `(i : B ⟶ A) (hB : IsBorelGroupScheme i)` is the Borel inclusion. Expanding the
  existing definition gives IsClosedSubgroupScheme i, Smooth B.hom,
  ConnectedSpace B.left, IsSolvableGroupScheme B and maximality among such closed
  subgroups by factorization of inclusions. IsSolvableGroupScheme is termination
  of GroupSchemeDerivedLength; each successor is the smallest closed subgroup
  through which groupSchemeCommutator factors, with no reduction of test algebras.
- `(u v : A ⟶ D) [IsMonHom u] [IsMonHom v]` are homomorphisms over F.
- `(h : (i ≫ u).left = (i ≫ v).left)` states agreement on B as scheme morphisms.
- `u.left = v.left` is equality as scheme morphisms, rather than equality of their
  underlying point functions. It therefore implies equality on every algebra-valued
  point, including nonreduced algebras. Conversely all algebra-valued points detect
  equality: A is affine and its universal point over its coordinate algebra suffices.
- No reductivity, surjectivity or kernel condition is imposed.

Dependency declarations read and used:

- def-weil-field: Field, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: IsAlgClosed, Mathlib.FieldTheory.IsAlgClosed.Basic;
  algebraic-closure data are not required because F itself is algebraically closed.
- def-sc-group-scheme: GrpObj, Mathlib.CategoryTheory.Monoidal.Grp; homomorphisms
  are IsMonHom as documented by WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- def-sc-group-scheme-subgroup: IsClosedSubgroupScheme and IsSubgroupScheme,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The closed-subgroup predicate
  includes the group-homomorphism condition, injectivity on all algebra-valued points
  and a closed immersion of schemes.
- def-sbc-smooth-morphisms: Smooth, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-weil-connected-scheme: ConnectedSpace, Mathlib.Topology.Connected.Basic.
- def-weil-finite-type-morphism: LocallyOfFiniteType and QuasiCompact,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact.
- def-sfb-borel-subgroup-scheme: IsBorelGroupScheme,
  Sheaf.AlgebraicGeometry.GroupScheme.Borel. This existing landed node is added to
  stmt_deps under the explicit permission to add landed statement dependencies.
  Its underlying IsSolvableGroupScheme, GroupSchemeDerivedLength,
  IsDerivedGroupScheme and groupSchemeCommutator were read in
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple. No notion is copied.

The recorded modules of all stated proof dependencies are imported without `public`:
GeneralBorelFlagVariety, SmoothGroupOrbitGeometry, HomogeneousOrbitQuotientGeometry,
ProperReducedGlobalSectionsProduct, WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced,
and the relevant Mathlib finite-type, algebraically closed field, fpqc and affine-adjunction
modules. Finite-type cancellation and the Jacobson instance are in FiniteType, already
publicly imported as a statement dependency. The group-scheme module is likewise already
public. The docstring records the precise role of every proof dependency.

Edge cases checked mathematically before writing: B = A (solvable source) reduces to
agreement on the whole group; the trivial source or target is included; empty group schemes
are excluded by the identity section and ConnectedSpace, as in the source; SL2 and its Borel
are included without any isogeny condition; positive characteristic and inseparable
homomorphisms are unrestricted; nilpotent and zero test algebras are retained by scheme
morphism equality. The arbitrary universe u imposes no dimension or characteristic bound.
No statement fault or STATEMENT-DISPUTED issue was found; the informal statement is unchanged.

Searches made:

- msearch.py leanfinder, "Homomorphisms of connected affine algebraic groups agreeing on
  a Borel subgroup are equal": 8 hits, including AffineSpace.hom_ext,
  ext_of_isAffine and ProfiniteGrp.hom_ext; none is Borel rigidity.
- msearch.py loogle, `"Borel"`: 12 hits, involving Lie-algebra Borel subspaces
  and measurable Borel spaces, with no group-scheme statement.
- msearch.py grep, `Borel|homomorphism.*rigidity`, Mathlib/AlgebraicGeometry:
  0 hits.
- msearch.py leansearch, "Restriction to a Borel subgroup determines a homomorphism of
  connected algebraic groups": 8 abstract restriction/range hits, no matching theorem.
- rg in lean/WeilConjectures and dag/lean_names_upstream.json for Borel homomorphism
  names: only unrelated Borel-Moore constructions. Search for the literal item id in
  lean/WeilConjectures: no hit.
- rg in lean/Sheaf for Borel homomorphism names found
  AlgebraicGeometry.hom_ext_of_borel_baseChange in
  Sheaf.AlgebraicGeometry.GroupScheme.BorelHomomorphismRigidity. Its full signature
  was read: it quantifies over an additional algebra R and homomorphisms between
  canonical pullbacks. This strictly general statement does not have the item's
  direct A-to-D signature. The present direct statement does not duplicate that
  declaration's signature and can later be obtained by the canonical R = F transport.
- rg in dag/nodes for IsBorelGroupScheme found the already landed
  def-sfb-borel-subgroup-scheme, whose full statement, Lean record and source were read.
  Its definition is exactly the notion used here; no new node is necessary.

Validation: scompile.py NB lem-sfb-homomorphism-borel-rigidity compiled this file
both in its sandbox and with its final library module name, cleanly (11.7s and 8.0s).
Only the sandbox has been written; no direct git commands or local/global builds ran.

## Second reading by NB

A second pass by this worker reopened the node, Borel and derived-series definitions,
and final module. It matched the field, all five properties of each of A and D,
closed Borel inclusion and maximal scheme-theoretic solvability, the two homomorphisms,
and the restriction and conclusion equalities. In particular `.left` is a scheme
morphism, not its point function. No extra smoothness or finiteness assumption on B
is separately added, and no pointwise abstract-solvability substitute is used.
No mismatch was found and no correction was needed. This is a self-check, not an
independent-agent review: the dispatcher brief forbids starting other agents and
assigns the independent review to the maintainer.
