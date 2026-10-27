## Worker report

The module `Sheaf.AlgebraicGeometry.DedekindGenericSubgroupClosure` states
`AlgebraicGeometry.exists_dedekind_generic_subgroup_closure`. Its only theorem
has proof `by sorry`; no definitions, instances, helper theorems, or new nodes
are introduced. The node changes only in its `lean` record.

Hypothesis and conclusion correspondence, checked against the node:

- The domain `D` is `(D : Type u) [CommRing D] [IsDedekindDomain D]` together with
  `_hDdim : ringKrullDim D = 1`. Mathlib's Dedekind class means a Noetherian,
  integrally closed domain of dimension at most one; the explicit equality
  preserves the node's specified dimension exactly one. The field case is
  therefore excluded by the node itself, not silently admitted by the encoding.
- `E = Frac D` is `(E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]`.
  Every displayed base-change functor uses the canonical morphism
  `Spec.map (CommRingCat.ofHom (algebraMap D E))`. `S` is `Spec (CommRingCat.of D)`.
- The commutative S-group scheme is `M : Grp (Over (Spec (CommRingCat.of D)))`
  with `[IsCommMonObj M.X]`. `Grp` bundles an `Over` object and its `GrpObj`
  structure, giving precisely multiplication, identity, inverse and group
  diagrams over S. There is no extra smoothness, flatness, affine, or
  quasi-compactness condition on M.
- Its separatedness and local finite type are `[IsSeparated M.X.hom]` and
  `[LocallyOfFiniteType M.X.hom]`. `IsSeparated` is closedness of the diagonal.
- `J` is a group object over Spec E. The morphism `j` goes to the actual
  pullback of M. The scoped `CategoryTheory.Obj` instances apply the canonical
  monoidal pullback functor to M's given group structure. `[IsMonHom j]`
  expresses subgroup compatibility and `[IsClosedImmersion j.left]` its closed
  immersion. A closed immersion is a monomorphism, so no separate injectivity
  hypothesis is needed. No arbitrary group structure on M_E is supplied.
- The node's finite-type J is exactly the pair
  `[LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]`, the dependency's
  recorded finite-type convention; it does not assert module finiteness.
- The closure is the existential group object `C` and S-morphism `i : C.X ⟶ M.X`.
  `IsMonHom i ∧ IsClosedImmersion i.left` is precisely a closed subgroup.
  `IsCommMonObj C.X`, `IsSeparated C.X.hom`, `Flat C.X.hom` and
  `LocallyOfFiniteType C.X.hom` are the four asserted properties of C.
- For EVERY affine open `U : M.X.left.affineOpens`,
  `RingHom.ker (i.left.app U).hom` is its closure ideal in B = Γ(U,O_M).
  The right-hand kernel is that of the section map for
  `a = j.left ≫ pullback.fst M.X.hom (Spec.map (CommRingCat.ofHom (algebraMap D E)))`.
  Its target is Γ(a⁻¹(U),O_J); by the pullback universal property this open
  subscheme is canonically `U_E ×_{M_E} J`. Thus the equation is exactly the
  node's displayed formula, with the same B and the same restriction map.
  For a closed immersion the kernel of its section map on an affine open is
  the defining ideal (Mathlib `IdealSheafData.ker_subschemeι_app` and
  `Scheme.Hom.ker_apply` give the standard ideal-sheaf presentation).
- `e : (Over.pullback ...).obj C.X ≅ J.X` with
  `e.hom ≫ j = (Over.pullback ...).map i` states equality of closed subschemes
  of M_E, using the usual isomorphism over the ambient scheme. The isomorphism
  is over Spec E, rather than merely an isomorphism of underlying spaces or
  an unspecified isomorphism of schemes. Group compatibility of e follows
  by cancellation against the subgroup inclusion, so need not be added as
  an extra clause absent from the node.
- Every S-scheme is quantified as `X : Over (Spec (CommRingCat.of D))` with only
  `_hX : Flat X.hom`; it is not assumed affine, separated, smooth, locally of
  finite type or quasi-compact. Every S-morphism `f : X ⟶ M.X` is allowed.
  Its generic restriction factors through J exactly when the displayed
  existential `g` over Spec E satisfies `g ≫ j = (Over.pullback ...).map f`.
  The conclusion `∃! g : X ⟶ C.X, g ≫ i = f` is existence and uniqueness of
  S-factorization; X and its maps carry no group structure requirement.

Dependency declarations read and used:

- def-weil-affine-spectrum and def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `Spec.map`, `Scheme`, `Scheme.Hom`.
- def-pc-base-change: WeilConjectures.AlgebraicGeometry.BaseChangeConventions,
  especially its documentation and `baseChange_morphism_projections`:
  scheme and morphism base change are `Over.pullback`, with `pullback.fst`
  and `pullback.snd` as projections. The recorded principal declaration
  `Scheme.Modules.moduleBaseChange` is explicitly only the module clause;
  the record itself directs scheme citers to `Over.pullback`.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat` (equivalent to stalkwise flatness).
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, `Grp`;
  Mathlib.CategoryTheory.Monoidal.Mon, `IsCommMonObj`, `IsMonHom`. Read also
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, which documents exactly
  this Over/GrpObj encoding. The group's base is S, as the item explicitly
  stipulates, so the field-specific `IsSubgroupScheme` wrapper is not used
  over D; a group homomorphism that is a closed immersion expresses exactly
  the subgroup notion directly. Mathlib's general group-object notion already
  applies without a field and needs no dependency repair or new definition.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact,
  `QuasiCompact` (together mean finite type).

Proof dependencies are available through the imports. The existing scheme
image is `Scheme.Hom.image` in Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme,
read together with `Hom.imageι`, `Hom.toImage`, `Hom.toImage_app_injective`
and `Hom.ker_apply`. The proof-only import
Mathlib.RingTheory.Flat.TorsionFree supplies both
`Module.Flat.instOfIsDedekindDomainOfIsTorsionFree` and `Module.Flat.torsion_eq_bot`.
The scheme Flat import supplies `Flat.comp`, base-change flatness, `flat_iff`
and the underlying ring-flatness API (`RingHom.Flat.localRingHom`). All seven
steps of the node's proof are included in the theorem docstring, with their
DAG references. The standard scheme image supplies an existing notion, so the
statement does not introduce a second schematic-closure definition.

Edge cases checked before writing: the identity subgroup, J = M_E whenever
that generic fibre is finite type, nonreduced generic subgroups, M with vertical
components or nilpotents, an affine U disjoint from J, and non-quasi-compact M
or X. The empty inverse image has zero section ring, so the kernel formula
makes the corresponding closure piece empty. J itself cannot be empty because
it is a group over the nonempty Spec E. The zero ring D is excluded by the
domain class. Fields have dimension zero and are excluded by the node's
explicit dimension-one convention. No reducedness or smoothness of J is used.
A special-fibre-only nonempty X generally violates flatness, illustrating why
that hypothesis is necessary. Universes and all variables are explicitly
bound; `Scheme.{u}` and `Over (Spec (.of D))` use the standard common universe
for the base and its schemes, with no independent smaller test universe.

Searches (via the prescribed msearch.py NP/item wrapper, 2026-10-24):

- leanfinder: "Schematic closure of a generic fibre subgroup over a Dedekind
  domain is flat and has universal factorization from flat schemes": 8 hits,
  including Flat, Flat.generalizingMap, the Dedekind torsion-free flatness
  instance, Algebra.HasGoingDown.of_flat and flatness on stalk maps; no match
  for the whole statement.
- loogle: `"schematicClosure"`: OK, zero hits.
- grep: `schematicClosure|schematic.closure|generic.*[Ss]ubgroup`, subdirectory
  AlgebraicGeometry: OK, zero hits.
- leansearch: "schematic closure of a closed generic subgroup is flat over a
  Dedekind base": 8 hits, mainly unrelated topological subgroup/matroid
  closure and `Flat.isStableUnderBaseChange`; no matching theorem.
- rg of lean/WeilConjectures and lean/Sheaf for schematic closure, generic
  subgroup and subgroup closure found compactification descriptions and
  topological/Hopf-algebra special cases, but no theorem stating this item.
  Search of the exact item id in lean/WeilConjectures found no declaration.
- Direct source search found the standard scheme-image and kernel APIs above,
  and the general monoidal `Over.pullback` group-object transport in
  Mathlib.CategoryTheory.Monoidal.Cartesian.Over. These are reused.

Source verification: read local Stacks morphisms.tex, scheme-theoretic image
and quasi-compact scheme-theoretic image (Tags 01R6/01R8), and more-algebra.tex,
lemma-dedekind-torsion-free-flat (0AUW). Opened the primary BLR scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
including the 7.1 Corollary 6 discussion of the flat schematic closure and its
factorization property. The node's source and agent-written expanded proof
are preserved. No statement correction and no STATEMENT-DISPUTED fault.

Validation: prescribed scompile.py compiled this file independently both as
sandbox `Sheaf.Stage2.Sandbox0` (8.9 seconds) and as
`Sheaf.AlgebraicGeometry.DedekindGenericSubgroupClosure` (45.6 seconds), exit 0,
with no error or disallowed warning. No direct Lean or Lake build was run.

## Second reading by NP

This is a separate rereading by the assigned worker, not a claim that another
agent reviewed it; the dispatcher's instructions forbid starting agents and
reserve the independent review for the maintainer. Reopened the node and final
module and checked the correspondence above. In particular checked that J's
finite type is over E, C's finite type remains local, `_hDdim` retains dimension
one, the pullback group structure is induced from M, the affine kernel formula
has Γ(U) as source, the generic isomorphism commutes with the inclusion into
M_E, and uniqueness quantifies arbitrary flat X and arbitrary S-maps. No
hypothesis or conclusion mismatch found. No new nodes or dependency modules.

The primary scan's PDF page 297, printed p.291, was also read directly:
BLR 10.1 Proposition 4 constructs the subgroup's schematic closure and asserts
its flatness; its remaining smoothening step belongs to the consumer, not this
node. The node's expanded affine proof supplies the other listed clauses.
`deliver2.py ... --no-push` returned `OK (dry run)` at commit `28b105c79f9`:
preflight passed and the module compiled; nothing was pushed by that dry run.
