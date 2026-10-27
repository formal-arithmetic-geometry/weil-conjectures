## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent` states
`AlgebraicGeometry.locallyAlgebraicGroup_identityComponent` with one `sorry` and
no new definitions. It realizes the whole locally finite type group-scheme assertion,
including its open subgroup structure, geometric irreducibility, finite type,
field-extension compatibility, and the smooth integral connected separated reduced
subgroup with the same topological space. Its docstring carries the seven-step
accepted proof. No other statement or proof is changed.

The previous BLOCKED ending concerned stage-1 re-splitting after Q36's accepted
split. The current assignment is stage 2, the node has no Lean record, the queue
lists stage 2, and coord/brief-stage2.md section 0 explicitly authorizes this
handoff. No released repair note exists for this item. The accepted statement,
statement dependencies, proof, proof dependencies, searches, provenance and review
are retained verbatim. Only the item's `lean` field changes.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Group scheme over k | `(G : Over (Spec (.of k))) [GrpObj G]` |
| Locally of finite type | `[LocallyOfFiniteType G.hom]`; no quasi-compactness hypothesis on G |
| Connected component of the identity | `connectedComponent (GrpObj.onePoint G)` |
| Open and closed | `∃ U : G.left.Opens`, equality of its carrier with that component, and `IsClosed (U : Set G.left)`; membership in `Opens` includes openness |
| With its open-subscheme structure | The scheme is the actual `U.toScheme`, its inclusion is `U.ι`, and its structure map is `U.ι ≫ G.hom` |
| Subgroup scheme | `∃ gC : GrpObj (Over.mk (U.ι ≫ G.hom))`, with `IsMonHom` for `Over.homMk (V := G) U.ι` using precisely gC and G's given group structure; the open immersion is already a monomorphism |
| Geometrically irreducible | `GeometricallyIrreducible (U.ι ≫ G.hom)` |
| Of finite type | `LocallyOfFiniteType (U.ι ≫ G.hom) ∧ QuasiCompact (U.ι ≫ G.hom)` |
| Formation commutes with field extension | For every `(K : Type u) [Field K] [Algebra k K]`, the inverse image of U along `pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))` equals the connected component of `GrpObj.onePoint ((Over.pullback ...).obj G)` |
| Reduction by the nilradical | Exactly `U.toScheme.nilradical.subscheme` and its canonical `subschemeι`; no arbitrary reduced replacement |
| Smooth reduction over k | `Smooth (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom)` |
| Connected | `ConnectedSpace U.toScheme.nilradical.subscheme` |
| Integral | `IsIntegral U.toScheme.nilradical.subscheme`; in particular this includes reducedness and nonemptiness |
| Separated over k | `IsSeparated (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom)` |
| Finite type reduction | `LocallyOfFiniteType` and `QuasiCompact` for that same composite |
| Reduced group and closed subgroup | `∃ gR : GrpObj (Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom))`, with `IsMonHom` for the actual nilradical immersion into the group with structure gC; this immersion is inherently closed |
| Same underlying topological space | `IsHomeomorph U.toScheme.nilradical.subschemeι` for the actual canonical reduction map |

The `@IsMonHom` arguments explicitly fix the existential group structures; this
avoids a hidden alternative instance or an unconnected group law. No choice of
scheme, coefficient map, or reduction is concealed in a hypothesis. The two
existential group structures assert that the *fixed* canonical inclusions preserve
multiplication and unit, hence also inverse. Their laws are consequently induced
from G. A monomorphic group homomorphism is exactly a subgroup inclusion.

The base-change equality is an equality of the actual open carriers in G_K,
not just a bijection between component sets. The scheme structure on an open
subset is restriction of the ambient structure sheaf. Thus this equality is
precisely compatibility of the open-subscheme structures, including the canonical
comparison. Since the group laws are induced through these monomorphisms, it also
identifies the subgroup schemes. It does not require K itself to be algebraically
closed. The standard `CategoryTheory.Obj` scoped instances supply the base-changed
group structure through the canonical monoidal pullback functor. The universe u
is explicit throughout, using the project's standard schemes/field-extension
size convention; there is no independent smaller test universe.

### Dependency declarations and sources read

Read all twelve statement-dependency statements and their recorded declarations
or Mathlib matches, with signatures and docstrings:

- `def-weil-field`: Mathlib `Field` (Algebra.Field.Defs).
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed` and `IsAlgClosure`
  (FieldTheory.IsAlgClosed.Basic); only `IsAlgClosed` is needed here.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`
  (Mathlib.CategoryTheory.Monoidal.Grp and Mon); these are the given dependency's
  group-object and homomorphism notions. Upstream GroupScheme.Defs documents
  exactly their specialization to `Over (Spec (.of k))`. The `onePoint` definition
  from WeilConjectures.AlgebraicGeometry.GroupScheme.Basic is the actual unit image.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  (Mathlib.AlgebraicGeometry.Morphisms.FiniteType) and `QuasiCompact`
  (Morphisms.QuasiCompact), combined exactly as its record specifies.
- `def-weil-connected-scheme`: Mathlib `ConnectedSpace`
  (Topology.Connected.Basic); its connected-component notion is `connectedComponent`.
- `def-pc-reduced-scheme`, `def-pc-integral-scheme`: `IsReduced` and `IsIntegral`
  (Mathlib.AlgebraicGeometry.Properties).
- `def-sbc-smooth-morphisms`: `Smooth`
  (Mathlib.AlgebraicGeometry.Morphisms.Smooth).
- `def-weil-proper-morphism`: `IsSeparated` imported through its recorded module
  Mathlib.AlgebraicGeometry.Morphisms.Proper; no properness is asserted.
- `def-weil-open-immersion`: `IsOpenImmersion`
  (Mathlib.AlgebraicGeometry.OpenImmersion), supplied canonically by `U.ι`.
- `def-pc-geometrically-irreducible`: `GeometricallyIrreducible`, imported through
  the recorded Mathlib.AlgebraicGeometry.Geometrically.Integral module. Its
  definition in Geometrically.Irreducible is exactly the required field-fibre
  irreducibility, also after arbitrary field extensions.
- `def-weil-pbc-scheme-reduction`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme` and `subschemeι`
  (Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme, with nilradical in Basic).

Recorded stated proof dependencies are imported without `public`: local component
finiteness, irreducibility of products, the reduction universal homeomorphism,
base-change conventions, perfect-field reduced tensors, reduced-source closed
factorization, perfect-field geometric reducedness, group-scheme separatedness,
and Mathlib's affine prime-spectrum/minimal-prime and localization results.
`smooth_of_grpObj` is imported with the group smoothness module.
The new stage-1 proof nodes `lem-sfb-group-local-minimal-prime` and
`lem-sfb-irreducible-group-quasi-compact` have no recorded Lean modules yet, so
there is no import to add for them; their exact role is retained in the proof
docstring. They are proof inputs, not unstated objects needed for this statement.

Read the source groupoids.tex at 0B7R, 047R, 047L, 047N and 047P. 0B7R gives
geometric irreducibility and quasi-compactness of the neutral subgroup; local
finite type provides openness and finite type as in the accepted seven-step
proof. 047R gives the reduced closed subgroup over a perfect field; 047P/047N
give smoothness and 047L gives separatedness. No statement correction is needed.

### Edge cases checked before writing

- The trivial group has the entire one-point scheme as identity component.
- An infinite constant group, for example Z_k, is locally of finite type and
  need not be quasi-compact; the theorem allows it and says only its identity
  component is of finite type. This rules out simply using the upstream finite
  type identity-component API.
- In characteristic p, alpha_p and mu_p can be nonreduced. Their open identity
  component is not replaced by its reduction; smoothness is asserted only for
  the separately specified reduction. Its topology is still the one-point space.
- A connected positive-dimensional group such as an elliptic curve is allowed;
  no affineness or dimension-zero hypothesis appears.
- The empty scheme admits no unit from the nonempty Spec k, hence is not a
  counterexample among group schemes. Integral and connected conclusions do
  not silently treat the empty space as connected.
- Any field extension K/k is allowed, including K=k and transcendental extensions;
  no finite, algebraic, separable, characteristic-zero or closedness assumption
  on K was added.

### Searches for existing declarations

Actual calls to `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q89
lem-sfb-locally-algebraic-group-identity-component`:

1. leanfinder: "The identity component of a group scheme locally of finite type
   over an algebraically closed field is open closed geometrically irreducible
   finite type and its reduction is a smooth subgroup". Eight hits, including
   `IsReduced`, `IsIntegral`, `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`,
   and integral/reduced equivalences. None states the group-scheme result.
2. loogle: "AlgebraicGeometry.GrpObj.onePoint, CategoryTheory.GrpObj".
   Zero hits: external Loogle does not know upstream `GrpObj.onePoint`.
   Read its actual upstream definition rather than treating this as absence.
3. grep: "identityComponent|onePoint|reduced.*[Gg]roup" in AlgebraicGeometry/Group.
   Zero Mathlib hits. Mathlib group smoothness supplies only a smoothness input.
4. leansearch: "identity component of locally finite type group scheme is finite
   type and geometrically irreducible". Eight hits including the topological-group
   `Subgroup.connectedComponentOfOne`, local finite type Noetherianness and
   unrelated ring finite-type facts; none states this assertion for scheme points.

Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf` and
`lean/.lake/packages/mathlib/Mathlib`, plus the item blueprint tag, found no exact
statement. Inspected GroupScheme.Basic, especially lines 242-260 and its
IdentityComponent section: the existing `isOpen_connectedComponent_onePoint`,
`GrpObj.identityComponentOpens`, `GrpObj.identityComponent` and component theorems
all require `[QuasiCompact G.hom]` as well as local finite type. They cannot be
attached to this stronger locally finite type statement. Existing reduced-group
smoothness and group separatedness cover individual inputs only. Searched the
proposed full declaration name also in dag/lean_names_upstream.json: no collision.
No notion is duplicated: the statement is expressed with existing opens, group
objects, reduction and scheme-property predicates, so no new definition node is
necessary.

### Validation

The final module passes scompile.py both as a sandbox module and at its intended
library path, with the stated proof-dependency imports, no errors and no warnings
other than the permitted sorry category. `set_option autoImplicit false` enforces
explicit binders, and the sole universe u is declared. No theorems are proved.
No source checkout or launcher script was modified, no git command was run, and
all writable files are within the assigned sandbox. Dry-run and push receipts
will be recorded below.

## Second reading by Q89

The dispatcher explicitly prohibits starting other agents. This is a separate
second reading by this worker, with the JSON statement and final Lean file open;
the maintainer supplies the independent review after delivery.

Rechecked the algebraically closed base, the over-category group object and local
finite type without global quasi-compactness. Rechecked each row of the table
against the final signature. Openness is part of `U : G.left.Opens`, and closedness
and carrier equality identify precisely the neutral component. The existential
group data are on that fixed open subscheme and the canonical reduction, and the
homomorphism types explicitly use those group laws; neither is arbitrary extra
data in a hypothesis. Rechecked geometric irreducibility and both finite-type
conditions, then field extension compatibility on the actual pullback ambient
scheme. Rechecked all six reduction conclusions (smooth, connected, integral,
separated, finite type and same underlying space), and its subgroup inclusion.
The canonical reduction immersion is a closed immersion independently of the
asserted group structure. No target hypothesis or clause is missing or extra.

The initial elaboration exposed one extra implicit argument in each explicit
`@IsMonHom` application. Removed it and fixed the target of the open inclusion to
G. The final compile verifies these are homomorphisms between the intended
structures. The mathematical statement was unchanged by this elaboration repair.
There are no new nodes, dependency repairs, statement changes or disputed clauses.

Final dry run: `deliver2.py Q89 lem-sfb-locally-algebraic-group-identity-component
--no-push` printed `OK (dry run): commit 200ca29bcda passes the preflight and
compiles; nothing pushed`. It staged exactly this report, the item JSON with
only its Lean record added, and its single Lean module.
