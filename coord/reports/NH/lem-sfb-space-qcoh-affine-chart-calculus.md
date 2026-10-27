## Worker report

The item is stated by `AlgebraicGeometry.AlgebraicSpace.quasiCoherent_affine_chart_calculus`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus`. Its natural-language statement,
proof, source, and proof dependency list are unchanged. Every theorem introduced here has
`sorry` as its whole proof. All definitions have actual data.

The theorem has ten conjuncts, in the following order. This gives the correspondence with
every hypothesis and clause of the DAG statement.

1. The base is explicitly `{S : Scheme.{u}}`, with `X : AlgebraicSpace S`. Modules are
   `X.Modules`, exactly the existing small-etale module category. The first conjunct is a
   natural isomorphism, for every `U : X.EtaleSite` with affine underlying scheme, between
   `QCoh(X)` restricted by `schemeRestriction X U` and evaluation at `op U` followed by
   `affineChartAssociated X U`. The latter is the existing tilde functor followed by
   pullback along the canonical `Scheme.isoSpec.hom`. Thus the module is specifically
   `F.val.obj (op U)`, over the actual regular-functions ring of U. Zariski restriction here
   is the inverse of the recorded scheme Zariski/etale quasi-coherent equivalence, so this
   states the associated-module description under that equivalence, naturally in F.
2. For `f : F ⟶ G`, the two `IsQuasicoherent` premises are precisely quasi-coherence of
   the input modules. Ambient `kernel f`, `cokernel f`, and `image f` are quasi-coherent.
   `kernelComparison` and `cokernelComparison` for the existing evaluation functor are
   isomorphisms on every affine etale chart. Equality between the section image of
   `image.ι f` and the ordinary range of `f.val.app (op U)` gives the image formula as an
   embedded module, rather than merely an abstract module isomorphism.
3. The tensor is the existing `SheafOfModules.siteSheafTensorRight`, with the original
   commutative structure sheaf and original module universe. It is quasi-coherent for
   quasi-coherent F and G. Its affine sections are linearly equivalent to
   `TensorProduct R F(U) G(U)`. The equation on every pure tensor identifies the comparison
   with the canonical sheafification-unit tensor map.
4. A module diagram has `J : Type u`, `SmallCategory J`, and `IsFiltered J`, with each term
   quasi-coherent. The cocone is a colimit in **all** `X.Modules`, its vertex is
   quasi-coherent, and each affine evaluation is an ordinary module colimit. The same
   assertion for any chosen colimit cocone follows by its unique cocone isomorphism; no
   special colimit object or cocone legs are assumed.
5. For a quasi-coherent F, `F.IsFiniteType` is equivalent to `Module.Finite R F(U)` on
   every affine chart, and `F.IsFinitePresentation` is equivalent to
   `Module.FinitePresentation R F(U)` there. These are Mathlib's local finite-generator
   and local finite-presentation predicates. The last part quantifies over every scheme
   chart U with `IsSurjective U.obj.hom` and gives both iff tests after its canonical
   `schemeRestriction`. This is equivalent to small-etale restriction by the existing
   scheme comparison; U need not be affine.
6. `∀ F, F.IsFinitePresentation → F.IsQuasicoherent` has no quasi-coherence premise.
   The finite-presentation notion is Mathlib's local finite cokernel presentation,
   `SheafOfModules.IsFinitePresentation`, used verbatim, not a replacement predicate.
7. For quasi-coherent F there exist an actual algebra sheaf A and module map j. Its
   underlying module is quasi-coherent. The `∀ B f, ∃! t` clause is the full algebra
   universal property `j ≫ algebraModuleFunctor.map t = f`; B has no quasi-coherence
   assumption. The affine ring equivalence has source `SymmetricAlgebra R F(U)` and
   explicitly preserves the scalar map and every degree-one generator, which uniquely
   characterize the canonical R-algebra comparison.
8. For an algebra morphism psi with quasi-coherent source and target, its actual module
   kernel inclusion satisfies `IsAlgebraIdeal`. Its quasi-coherence and section kernel
   formula are already given by conjunct 2. Q is the kernel quotient, B is the image
   algebra, and both are quasi-coherent. The specified module isomorphism `eb` identifies
   B with the actual module image and commutes with its inclusion into A. The algebra
   isomorphism `e : Q ≅ B` satisfies `q ≫ e.hom ≫ b = psi`, so it is exactly the first
   isomorphism comparison. Q kills the kernel and has the quotient universal property
   against every algebra target. On every affine chart, b has exactly the ordinary
   range of psi, and the ring equivalence from the ordinary kernel quotient to Q(U)
   sends each residue class to the image under q. This also fixes its R-algebra structure.
9. For quasi-coherent E and D, e is exactly a module map into D's underlying module.
   The witnesses I and i are a quasi-coherent embedded ideal; E factors through i.
   Minimality is quantified against **all** embedded ideal sheaves K, without a
   quasi-coherence restriction: any factorization of e through K induces a factorization
   of i through K. Thus this is the smallest sheaf of ideals containing e(E). Q is
   quasi-coherent, q kills I, and every algebra map killing e factors uniquely through q.
   The affine section image of i is the ordinary `Ideal.span` of the range of e_U, and
   the ordinary quotient ring is identified with Q(U) by the equation on residue classes.
   The explicit `@id` in this expression only exposes the existing algebra-section
   carrier of the underlying module; it introduces no cast or additional hypothesis.
10. For any small filtered algebra diagram with quasi-coherent terms there is a colimit
    cocone in **all** `X.CommAlgebraSheaf`, with quasi-coherent vertex and colimiting
    evaluations at every affine etale chart. The evaluation category is `Under R` in
    commutative rings, the ordinary category of R-algebras carrying its scalar maps.
    The last implication is the requested affine test for any algebra cocone with
    quasi-coherent vertex. It does not restrict the target algebras in its colimit
    universal property to quasi-coherent ones.

Dependencies used directly in signatures/constructions:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `etaleForget`,
  `structureSheaf`, `Modules`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the original `QCoh` full
  subcategory and its Mathlib `SheafOfModules.isQuasicoherent` predicate and slice instances.
- `def-weil-size-convention` is a convention record: explicit u throughout, site objects
  u+1, morphisms u, sections and filtered diagrams u, with no imposed equality of site
  object and morphism universes and no coefficient lift.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `mapCocone`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- Landed `def-trf-space-module-scheme-restriction`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction.schemeRestriction` (in namespace
  `AlgebraicGeometry.AlgebraicSpace`), gives the actual inverse comparison to Zariski opens.
- Landed `def-pur-sheaf-tensor-product`, with its independent-universe interface in
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
  `SiteTensorFunctoriality`: `siteSheafTensorRight`, `siteSheafTensorTmul`.
- The new definition node supplies the missing algebra category, module/evaluation
  functors, commutative structure sheaf, embedded-ideal predicate, and additive
  sheafification instances. The theorem uses Mathlib's ambient abelian module instance,
  rather than choosing an Abelian structure.

The two landed definition nodes above and the new node were added to `stmt_deps` under
brief-stage2 section 5. No dependency module or statement correction is needed. Stated
proof dependencies are imported as plain imports; Mathlib matches for left-adjoint
colimit preservation and existence of algebra colimits are also imported. The three
proof prerequisites without a Lean record (cartesian chart family, kernels/colimits,
scheme etale exact-finiteness comparison) cannot yet supply imports and have not been
silently restated here.

Sources read: local Stacks spaces-properties.tex 03LZ, 03M0, 03M1 and local module
properties; spaces-limits.tex 082A and 086Z and their symmetric-algebra/kernel/generated-
ideal constructions. The current blueprint unit and direct-images prerequisite route
were read under `literature/blueprint/latest/`; this helper does not alter that unit.
The example CompactObject module is withdrawn in the current read clone, so the header,
namespace and module-mode conventions are taken from the current dependency modules.

Edge cases checked before delivery: empty X and the empty affine chart (zero rings are
allowed); F=0, whose symmetric algebra is O_X; zero and identity module arrows; identity
algebra morphism (zero kernel); morphisms to the zero algebra; E=0 (zero generated ideal);
e containing 1 (unit ideal and zero quotient); finite presentations of ranks zero;
non-affine and disconnected surjective etale charts; and singleton filtered diagrams.
Filteredness supplies nonemptiness; no empty filtered diagram is asserted. No
Noetherian, quasi-compactness, quasi-separatedness, reducedness or nonzero-ring assumption
has been introduced. No `STATEMENT-DISPUTED` issue was found.

Searches: prescribed msearch leanfinder query for the full affine chart calculus returned
8 unrelated/local-presentation hits, not this statement. Loogle
`SheafOfModules.IsQuasicoherent, SymmetricAlgebra, SheafOfAlgebras` returned no match
(unknown final identifier). The msearch grep of ModuleCat/Sheaf returned finite-generator
and presentation definitions, which are reused. The separate LeanSearch query for algebra
sheaves and their underlying module returned generic sheaf/module declarations only;
Loogle `Under, Sheaf` gave no hit; grep for `commAlgebraSheafModule|CommAlgebraSheaf` in
Mathlib CategoryTheory gave zero hits. Direct rg of `lean/WeilConjectures`, `lean/Sheaf`
and the DAG found the topological-space and scheme specializations, the graded-etale
algebra node, and consumers mentioning this item only in proofs; none states this
ungraded small-etale interface or this theorem. Exact query results are recorded in
`searches.jsonl` and the new node's `mathlib_searches`.

Compilation uses scompile.py only. Explicit module-mode probes read the complete universe
signatures of unit, restriction of scalars, and the original site/module categories.
The required arbitrary-site commutative-ring forgetful instance is exposed by importing
`Sheaf.CategoryTheory.CochainCoefficientUniverseTransport` directly, and the ring-to-group
limit instance by `WeilConjectures.Mathlib.Algebra.Category.Ring.Limits`; no site or
coefficient universe was changed. Temporary probe modules are removed before delivery.

## New nodes

`def-sfb-space-comm-algebra-sheaf` is the missing ungraded small-etale algebra interface.
Its module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf` retains the actual
commutative regular-functions sheaf, defines its `Under` category, constructs the underlying
module and evaluation functors, and expresses embedded ideals by module monomorphisms
whose section images are ideals. This does not choose an ideal or quotient from arbitrary
existence. Named sheaf-condition and sheafification obligations have source/proof docstrings
and are included explicitly in the new node's statement and `lean.declarations`. Their
proofs are postponed. The structure presheaf is actual scheme Gamma; the only postponed
part of the structure sheaf is its sheaf-condition proof. Sheafification is characterized
by its adjunction, which determines it up to the canonical isomorphism.

Sources are Stacks 03G7, 03ED, 039Z and the algebra/ideal operations in 082A/086Z. Existing
`Scheme.CommAlgebraSheaf` and `CategoryTheory.commAlgebraSheafModuleFunctor` apply to
Zariski topological sites. The existing `RingedSiteIdeal` additionally fixes the object
and section universes equal and cannot represent this site (objects u+1, sections u).
`IsAlgebraIdeal` instead describes embedded ideals using the existing ambient module
category; the sheaf and mono imply local membership. The existing etale graded-algebra
node does not define ungraded algebra sheaves or these functors. The three search kinds
and direct source/DAG search are recorded in the new node. `blueprint_refs.py ancestor`
returns None on this inherited prerequisite chain, so its new node retains that same
null ancestor and prepends the item to the inherited via list, with an explicit source
place; this is an inherited ancestry fact, not a change to the unit or route.

Validation: both delivered modules compiled cleanly with the prescribed two-file
scompile.py command on 2026-10-24; the main file compiled in 9.9 seconds in its
library form, below the unchanged 60-second per-file limit.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
