## Worker report

This is a stage-2 statement delivery for lem-sfb-multiplicative-isogeny-composition,
not a re-split. The accepted Q146 split is preserved verbatim. The current node has
no lean record and is listed at stage 2 in coord/queue.tsv. The explicit maintenance
handoff in coord/brief-stage2.md §0 says that an inherited stage-1 stale-assignment
failure does not prevent this stage-2 work. There is no released repair note for
this item. No shared source, launcher script or live git state was edited directly.

The main module Sheaf.AlgebraicGeometry.MultiplicativeIsogenyComposition states
AlgebraicGeometry.multiplicativeIsogeny_comp. Its only theorem has proof `sorry`.
The new dependency module contains a real Prop-valued definition, with no sorry,
no chosen representing object and no arbitrary comparison map.

Clause-by-clause mapping of the item:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  No characteristic assumption is present.
- H0, H1, H2 are `Over (Spec (.of F))` and each has `GrpObj`. These are the
  dependency's actual scheme group objects, not a private algebraic-group structure.
- Affineness is `[IsAffine Hi.left]` for all three groups.
- Smoothness is `[Smooth Hi.hom]` for all three structure morphisms.
- Connectedness is `[ConnectedSpace Hi.left]` for all three underlying spaces,
  retaining nonemptiness, as def-weil-connected-scheme requires.
- Finite type is `[LocallyOfFiniteType Hi.hom] [QuasiCompact Hi.hom]`, for each i,
  precisely the conjunction specified in def-weil-finite-type-morphism's record.
- The maps f and g are morphisms in the slice, with `[IsMonHom f] [IsMonHom g]`.
  Thus they are actual F-group-scheme homomorphisms. The composite is `f ≫ g`.
- The faithfully flat coordinate pullbacks are
  `hf : f.left.appTop.hom.FaithfullyFlat` and
  `hg : g.left.appTop.hom.FaithfullyFlat`. `appTop` is the contravariant map
  Γ(target) → Γ(source); RingHom.FaithfullyFlat is the existing faithfully-flat
  module predicate for its induced algebra structure, equivalently exact extension
  of scalars which detects zero modules. No merely surjective point map is substituted.
- The two finite scheme-theoretic kernels are `[IsFinite (GrpObj.ker f).hom]` and
  `[IsFinite (GrpObj.ker g).hom]`. The recorded group-scheme convention identifies
  this with finite-dimensional coordinate algebra over F.
- Multiplicative type of these finite kernels is expressed by hN and hQ, each an
  `IsFiniteDiagonalizableGroupScheme` of the corresponding actual kernel. Since F
  is algebraically closed, the algebraic-closure clause is exactly diagonalizability
  over F. The finite character group is existential, never a fixed extra input.
- The first conclusion is `(f ≫ g).left.appTop.hom.FaithfullyFlat`.
- The second is `IsFinite (GrpObj.ker (f ≫ g)).hom`.
- The third is `IsFiniteDiagonalizableGroupScheme (GrpObj.ker (f ≫ g))`.
- The last clause quantifies over every F-test scheme T, every kernel point x and
  every H0-point h, and asserts
  `(x ≫ GrpObj.kerι (f ≫ g)) * h = h * (x ≫ GrpObj.kerι (f ≫ g))`.
  This is exactly scheme-theoretic centrality. Restricting to affine test schemes
  gives every F-algebra in the node; conversely equality on affine tests implies
  equality on arbitrary T by restricting to an affine cover. Thus it adds no
  mathematical hypothesis or conclusion. The two point products use the existing
  `CategoryTheory.Hom.group` from the scoped MonObj API.

The source was read directly: Milne Definition 18.1 and Proposition 18.2, printed
p.387, and Proposition 12.3, Remark 12.6 and Theorem 12.8, printed pp.231--233.
The accepted proof's corrected use of 12.41 and its central-kernel hypothesis is
retained. The docstring gives all seven DAG proof steps and names their nodes:
kernel sequence; faithfully-flat base change; centrality of N by rigidity;
centrality of K by corrected extension-action rigidity; multiplicative type by the
commutative extension theorem; finiteness by the torsor tensor identity and finite
module descent; faithful-flat composition by tensor associativity. No proof step
or proof dependency was changed. The latest blueprint's direct-image stability
proof (3) was read for the ancestor context; this item is a supporting lemma, not
the unit statement. The ancestor search returns null, as in the item's inherited
blueprint provenance.

Dependency declarations read and reused:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`
  (the node's mathlib_match explicitly lists this component).
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `CategoryTheory.GrpObj`,
  together with `CategoryTheory.IsMonHom` and the documented slice specialization
  in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. Kernel declarations are
  `CategoryTheory.GrpObj.ker`, `kerι`, `instGrpObjKer`, in
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, with
  `AlgebraicGeometry.IsFinite` from Mathlib.AlgebraicGeometry.Morphisms.Finite.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-weil-connected-scheme: Mathlib.Topology.Connected.Basic, `ConnectedSpace`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact,
  `QuasiCompact`.
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `Scheme` and `Scheme.Hom`;
  affineness is Mathlib.AlgebraicGeometry.AffineScheme, `IsAffine`.
- The new definition's dependencies are these same field, scheme and group-scheme
  declarations; no interface repair of any recorded dependency is needed.

The stated proof inputs are imported without public: the upstream kernel module;
Mathlib.AlgebraicGeometry.Pullbacks (`pullbackSpecIso` and its projection lemmas);
Mathlib.RingTheory.Flat.FaithfullyFlat.Basic (faithfully flat tensor base change);
Mathlib.RingTheory.Finiteness.Descent
(`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`). Their signatures and
source docstrings were read. The three action/extension-rigidity proof nodes have
no Lean or Mathlib record yet, so have no modules to import. They are needed only
to prove this theorem; the statement uses none of their unformalized notions.

Edge cases checked before drafting:

- The trivial group and identity maps are permitted. A finite character group is
  nonempty as a group, and its trivial case gives D(0) = Spec F, not an empty scheme.
- There is no positive rank, positive dimension, nontriviality or separability binder.
- In characteristic p, successive p-power maps on G_m have kernels μ_p and μ_(p²).
  All test schemes, including nonreduced affine schemes, occur in the definition
  and the centrality clause. Nothing assumes smoothness or reducedness of kernels.
- If just one map is the identity, its trivial kernel is allowed. No geometric
  point surjectivity is used in place of faithful flatness.
- Universe u is explicitly bound; F, schemes, and test schemes use that same scheme
  universe. A finite character group admits a representative in Type u. Naturality
  over this full category detects scheme morphisms and does not quantify over a
  smaller independent universe. `autoImplicit false` is set in both modules.

Searches were made with msearch.py and read, with exact queries in searches.jsonl:

- LeanFinder: "Composition of multiplicative isogenies of smooth connected affine
  algebraic groups has finite central kernel of multiplicative type" returned eight
  hits about ideal-sheaf kernels, finite abstract groups and composition of finite
  scheme morphisms; none states the item.
- Loogle: "GrpObj, MonoidHom" reported unknown identifier GrpObj and no hits; this
  is an unsupported query, not evidence of absence.
- msearch grep: "Diagonalizable|MultiplicativeType|multiplicative.isogeny|diagonalizable"
  restricted to AlgebraicGeometry returned no hits.
- LeanSearch: "finite diagonalizable group scheme represented by characters of a
  finite abelian group" returned eight hits on abstract characters, finite Fourier
  theory and representations; none defines diagonalizable group schemes.
- LeanFinder: "finite diagonalizable group schemes are represented by the functor
  of homomorphisms from a finite abelian group to units of algebras" returned eight
  Tannaka and Galois-category hits; none defines the notion or provides this theorem.
- Further whole-Mathlib grep for "IsFiniteDiagonalizableGroupScheme|diagonalizable
  group scheme|multiplicative isogeny" found no definition or theorem.
- Read-only rg searches of all WeilConjectures and Sheaf for the item id,
  MultiplicativeIsogeny, multiplicativeIsogeny, IsMultiplicativeType,
  MultiplicativeType and diagonalizable found no applicable definition or statement.
  Other centrality hits concern central algebras, not group schemes.
- Whole-DAG searches found the existing *theorem* nodes on diagonalizable geometric
  criteria, character antiduality, split-torus subgroups and multiplicative-type
  rigidity. Their statements define D(M) inline, and none has a usable Lean record.
  A parsed search of definition nodes found no existing diagonalizable or
  multiplicative-type definition node. None of those substantive theorem statements
  is needed to define this functor-of-points predicate.
- tools/blueprint_refs.py search for multiplicative isogeny and finite diagonalizable
  found no corresponding blueprint definition. This supports a new definition node,
  not a duplicate theorem or a restatement of one of the existing geometry inputs.

Validation: scompile.py compiled BOTH files separately, including the private
sibling overlay, cleanly with no errors and no unexpected warnings. The expected
sorry is only AlgebraicGeometry.multiplicativeIsogeny_comp. The required dry run
and final delivery are performed after this report is written. The first dry run
required the current schema field import_flags on the new node; it was added as
an empty list, and the dry run was repeated. No statement dispute
or source correction is needed for the item.

## New nodes

`def-sfb-finite-diagonalizable-group-scheme` defines the missing finite diagonalizable
predicate in its own module, Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme.
The definition is existential over a finite abelian M and genuine group isomorphisms
on every test scheme, with the explicit compatibility under each map of tests.
Its data is a real formula and contains no sorry. Milne Proposition 12.3 identifies
Hom(M,R×) with the group scheme Spec k[M], and Remark 12.6 gives exactly the basis
comultiplication in the item. Applying the same affine representation to arbitrary
T gives Hom(M,Γ(T)×); this glues on open covers. Naturality and multiplicative
isomorphisms therefore express isomorphism of group schemes with the specified
Hopf operations, not merely an isomorphism of the underlying schemes or of geometric
point groups. For finite M, k[M] has the finite basis M; conversely finite coordinate
dimension forces the diagonalizable group's basis M to be finite. Over algebraically
closed F no further scalar extension is needed. The existing theorem nodes mentioned
above have larger mathematical assertions and no recorded notion interface, so this
small definition duplicates none of them. Its field, group-scheme and scheme
dependencies are named in its statement and stmt_deps. The actual search receipts
are recorded in its mathlib_searches. The item gains only this stmt_dep and its lean
record; no statement_change is made.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
